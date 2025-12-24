import os
import re
import csv
import time
import zipfile
import shutil
import requests
import json
import cv2
import numpy as np
from PIL import Image
import imagehash
from bs4 import BeautifulSoup
from prettytable import PrettyTable
from urllib.parse import urlparse
import logging
from concurrent.futures import ThreadPoolExecutor
import threading
from selenium import webdriver
from selenium.webdriver.chrome.options import Options
from selenium.webdriver.common.by import By
from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.support import expected_conditions as EC
from datetime import datetime
from cryptography.fernet import Fernet

# GUI
import tkinter as tk
from tkinter import ttk, filedialog, messagebox, scrolledtext
import queue

# -----------------------
# Settings
# -----------------------
HEADLESS = True
IMAGE_THRESHOLD = 3
DOWNLOAD_DIR = os.path.join(os.getcwd(), "downloads")
RESULTS_CSV = "results_report.csv"
LINKS_FILE = "links.csv"  
STORES_FILE = "stores.csv"
amazon_driver = None
icepim_driver = None
lock = threading.Lock()
EXPORT_ENABLED = False
CHECK_IMAGES = False
CHECK_VIDEOS = False 
ENCRYPTED_FILE = "credentials.enc"
KEY_FILE = "secret.key"

# -----------------------
# Logging
# -----------------------
log_queue = queue.Queue()

class QueueHandler(logging.Handler):
    def emit(self, record):
        log_queue.put(record.msg)

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s | %(message)s',
    datefmt='%H:%M:%S',
    handlers=[
        logging.FileHandler("full_parser_log.txt", encoding="utf-8"),
        logging.StreamHandler(),  
        QueueHandler()  
    ]
)


# -----------------------
# Encrypring credentials
# -----------------------
def get_fernet():
    if not os.path.exists(KEY_FILE):
        key = Fernet.generate_key()
        with open(KEY_FILE, "wb") as f:
            f.write(key)
    with open(KEY_FILE, "rb") as f:
        key = f.read()
    return Fernet(key)

def save_credentials(login, password):
    fernet = get_fernet()
    data = f"{login}|{password}"
    encrypted = fernet.encrypt(data.encode())
    with open(ENCRYPTED_FILE, "wb") as f:
        f.write(encrypted)

def load_credentials():
    if not os.path.exists(ENCRYPTED_FILE):
        return "", ""
    try:
        fernet = get_fernet()
        with open(ENCRYPTED_FILE, "rb") as f:
            encrypted = f.read()
        decrypted = fernet.decrypt(encrypted).decode()
        login, password = decrypted.split("|", 1)
        return login, password
    except:
        return "", ""


# -----------------------
# Logging
# -----------------------
class NoDuplicateFilter(logging.Filter):
    def filter(self, record):
        return True  

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s | %(message)s',
    datefmt='%H:%M:%S',
    handlers=[
        logging.FileHandler("full_parser_log.txt", encoding="utf-8"),
        logging.StreamHandler(),
        QueueHandler()
    ]
)

logging.getLogger().addFilter(NoDuplicateFilter())

# -----------------------
# Driver setup
# -----------------------
def setup_driver(is_amazon=True):
    options = Options()
    if not HEADLESS:
        options.add_argument("--start-maximized")

    options.add_argument("--no-sandbox")
    options.add_argument("--disable-dev-shm-usage")
    options.add_argument("--disable-blink-features=AutomationControlled")
    options.add_experimental_option("excludeSwitches", ["enable-automation"])
    options.add_experimental_option("useAutomationExtension", False)
    options.add_argument("--blink-settings=imagesEnabled=true")

    prefs = {
        "download.default_directory": DOWNLOAD_DIR,
        "download.prompt_for_download": False,
        "download.directory_upgrade": True,
        "safebrowsing.enabled": True,
        "credentials_enable_service": False,      
        "profile.password_manager_enabled": False,  
        "autofill.profile_enabled": False,         
        "autofill.credit_card_enabled": False      
    }
    options.add_experimental_option("prefs", prefs)

    driver = webdriver.Chrome(options=options)
    driver.execute_script("Object.defineProperty(navigator, 'webdriver', {get: () => false});")

    driver.execute_script("""
        const originalPlay = HTMLMediaElement.prototype.play;
        HTMLMediaElement.prototype.play = function() {
            this.muted = true;
            this.volume = 0;
            return originalPlay.apply(this, arguments);
        };
        document.querySelectorAll('video, audio').forEach(el => {
            el.muted = true;
            el.volume = 0;
        });
    """)

    driver.set_window_size(900, 900)
    if is_amazon:
        driver.set_window_position(0, 0)  
        logging.info("Amazon browser positioned on the left")
    else:
        driver.set_window_position(900, 0)  
        logging.info("IcePIM browser positioned on the right")

    return driver

def init_amazon_driver():
    global amazon_driver
    with lock:
        if amazon_driver is None:
            amazon_driver = setup_driver(is_amazon=True)
            amazon_driver.get("https://www.amazon.com")
            logging.info("Amazon-driver started")
    return amazon_driver

def init_icepim_driver():
    global icepim_driver
    with lock:
        if icepim_driver is None:
            icepim_driver = setup_driver(is_amazon=False)
            login_icepim(icepim_driver)
            logging.info("IcePIM-driver started. Login - OK")
    return icepim_driver

def init_drivers():
    global amazon_driver, icepim_driver

    if amazon_driver is None:
        init_amazon_driver()

    if icepim_driver is None:
        init_icepim_driver()

    logging.info("Browser sessions ready (reusing existing if available)")


def get_domain_from_url(url):
    try:
        domain = urlparse(url).netloc.lower()
        return domain.replace("www.", "")
    except:
        return None

# -----------------------
# extract_all_hires
# -----------------------
def extract_all_hires(page_source):
    match = re.search(r'colorImages["\s:]*:\s*{\s*["\']initial["\']:\s*(\[[^\]]*\])', page_source, re.DOTALL)
    if match:
        try:
            arr = json.loads(match.group(1))
            urls = [item.get("hiRes") or item.get("large") for item in arr if item.get("hiRes") or item.get("large")]
            return [u for u in urls if u]
        except: pass
    return re.findall(r'"hiRes"\s*:\s*"([^"]+)"', page_source)

# -----------------------
# Login IcePIM
# -----------------------
def login_icepim(driver):
    username = entry_login.get().strip()
    password = entry_password.get().strip()

    if not username or not password:
        raise ValueError("IcePIM login and password required (check GUI fields)")

    logging.info("Logging in to IcePIM with GUI credentials...")
    driver.get("https://versuni.icepim.biz/index.php")
    try:
        user_field = WebDriverWait(driver, 5).until(
            EC.presence_of_element_located((By.NAME, "admin_login_form_user_name"))
        )
        pass_field = driver.find_element(By.NAME, "admin_login_form_user_password")
        user_field.clear()
        user_field.send_keys(username)
        pass_field.clear()
        pass_field.send_keys(password)
        login_button = driver.find_element(By.XPATH, '//button[contains(text(),"Login")]')
        driver.execute_script("arguments[0].click();", login_button)
        WebDriverWait(driver, 5).until(EC.presence_of_element_located((By.TAG_NAME, "body")))
        logging.info("Successfully logged in to IcePIM")
    except Exception as e:
        logging.info(f"IcePIM login failed: {e}")
        raise

# -----------------------
# Amazon video parsing
# -----------------------
def parse_amazon_videos(driver):

    trigger = None
    trigger_parent = None

    carousel_selectors = [
        "#altImages",
        "#imageBlockVariations",
        ".a-carousel-container",
        "ul.a-unordered-list.a-horizontal"
    ]

    found_carousel = False
    for carousel_sel in carousel_selectors:
        try:
            carousel = driver.find_element(By.CSS_SELECTOR, carousel_sel)
            found_carousel = True
            break
        except:
            continue

    if not found_carousel:
        logging.info("   Image carousel not found")
        return 0, []

    play_img_selectors = [
        "img[src*='play']",
        "img[src*='video']",
        "img[alt*='Play video']",
        "img[data-old-image*='play']",
        "img[data-a-image-name*='video']"
    ]

    for img_sel in play_img_selectors:
        try:
            imgs = carousel.find_elements(By.CSS_SELECTOR, img_sel)
            for img in imgs:
                if not img.is_displayed():
                    continue
                parent = img.find_element(By.XPATH, "./ancestor::li | ./ancestor::div[contains(@class,'item')]")
                overlay_text = parent.text.strip().upper()
                if "VIDEO" in overlay_text and len(overlay_text) < 30:
                    trigger = parent
                    trigger_parent = parent
                    break
            if trigger:
                break
        except:
            continue

    if not trigger:
        logging.info("   No valid main gallery video trigger found")
        return 0, []

    overlay_text = trigger_parent.text.strip()
    count_match = re.search(r'(\d+)', overlay_text)
    estimated_count = int(count_match.group(1)) if count_match else 1
    logging.info(f"   Video trigger found: '{overlay_text}' → {estimated_count} videos.")

    try:
        driver.execute_script("arguments[0].scrollIntoView({block: 'center'});", trigger_parent)
        time.sleep(1)
        driver.execute_script("arguments[0].click();", trigger_parent)

        WebDriverWait(driver, 5).until(
            EC.any_of(
                EC.presence_of_element_located((By.ID, "ivVideos")),
                EC.presence_of_element_located((By.CSS_SELECTOR, ".ivStage")),
                EC.presence_of_element_located((By.CSS_SELECTOR, "video"))
            )
        )
        time.sleep(1)
    except Exception as e:
        logging.info(f"   Failed to open lightbox: {e}")
        return estimated_count, []

    driver.execute_script("""
        let videos = document.querySelectorAll('video');
        videos.forEach(v => { v.muted = true; v.pause(); });
    """)

    page = driver.page_source

    seconds_matches = re.findall(r'"durationSeconds"\s*:\s*(\d+)', page)
    if seconds_matches:
        all_durations = []
        for sec in seconds_matches:
            s = int(sec)
            all_durations.append(f"{s//60}:{s%60:02d}")

        unique_durations = []
        seen = set()
        for d in all_durations:
            if d not in seen:
                unique_durations.append(d)
                seen.add(d)
            if len(unique_durations) == estimated_count:
                break

        final_durations = unique_durations[:estimated_count] if len(unique_durations) >= estimated_count else all_durations[:estimated_count]

        logging.info(f"   Found Amazon video durations: {final_durations}")

        try:
            close_btns = driver.find_elements(By.CSS_SELECTOR, "#ivClose, .ivClose, button.a-button-close")
            if close_btns:
                driver.execute_script("arguments[0].click();", close_btns[0])
        except:
            pass

        return estimated_count, final_durations

    else:
        logging.info("   No durationSeconds found in page_source")

    try:
        close_btns = driver.find_elements(By.CSS_SELECTOR, "#ivClose, .ivClose, button.a-button-close")
        if close_btns:
            driver.execute_script("arguments[0].click();", close_btns[0])
    except:
        pass

    logging.info(f"   Only count available: {estimated_count} videos (no durations)")
    return estimated_count, []

# -----------------------
# Amazon parser
# -----------------------
def parse_amazon(driver, url, is_first=False):
    try:
        logging.info(f"Parsing Amazon: {url}")

        if is_first:
            logging.info("   First product — checking for 'Continue shopping' page...")
            try:
                continue_btn = WebDriverWait(driver, 3).until(
                    EC.element_to_be_clickable((By.XPATH,
                        "//input[contains(@value, 'continue shopping')] | "
                        "//button[contains(., 'Continue shopping')] | "
                        "//a[contains(., 'Continue shopping')]"
                    ))
                )
                driver.execute_script("arguments[0].click();", continue_btn)
                logging.info("   Clicked 'Continue shopping'")
                WebDriverWait(driver, 5).until(EC.presence_of_element_located((By.ID, "productTitle")))
            except:
                logging.info("   No intermediate page — proceeding")
                pass
        
        if is_first:
            logging.info("   First product — trying to auto-accept cookie banner...")
            try:
                accept_selectors = [
                    "#sp-cc-accept",
                    "button[data-cel-widget='sp-cc-accept']",
                    "#a-autoid-3-announce",
                    "input.a-button-input[aria-labelledby*='accept']",
                    "//button[contains(text(), 'Accept') or contains(text(), 'Alle akzeptieren') or contains(text(), 'Akzeptieren')]",
                    "//button[contains(., 'Accept all') or contains(., 'Tout accepter')]"
                ]

                accepted = False
                for sel in accept_selectors:
                    try:
                        btn = WebDriverWait(driver, 5).until(
                            EC.element_to_be_clickable((By.CSS_SELECTOR if not sel.startswith("//") else By.XPATH, sel))
                        )
                        driver.execute_script("arguments[0].click();", btn)
                        logging.info(f"   Cookie banner accepted with selector: {sel}")
                        accepted = True
                        time.sleep(0.5)  
                        break
                    except:
                        continue

                if not accepted:
                    logging.info("   No cookie banner found on first product (already accepted?)")
            except Exception as e:
                logging.info(f"   Cookie banner handling error: {e}")
        else:
            logging.info("   Not first product — skipping cookie banner check")

       
        
        driver.execute_script("window.scrollTo(0, document.body.scrollHeight/3);")
        time.sleep(0.7)
        driver.execute_script("window.scrollTo(0, 0);")
        time.sleep(0.7)
        
        
        for attempt in range(2):
            soup = BeautifulSoup(driver.page_source, "html.parser")
            title_tag = soup.find(id="productTitle")
            bullets = [li.get_text(strip=True) for li in soup.select("#feature-bullets ul li span.a-list-item") if li.get_text(strip=True)]

            if title_tag and len(bullets) > 2:
                title = title_tag.get_text(strip=True)
                logging.info(f"   Title (Amazon): Found")
                logging.info(f"   Bullets found (Amazon): {len(bullets)}")

                has_manual = False
                try:
                    links = driver.find_elements(By.CSS_SELECTOR, "a[id^='product-docs-btf-ingress-']")
                    for link in links:
                        if "(PDF)" in link.text:
                            has_manual = True
                            break
                    if not has_manual:
                        all_links = driver.find_elements(By.TAG_NAME, "a")
                        for link in all_links:
                            if "(PDF)" in link.text:
                                has_manual = True
                                break
                except:
                    pass
                logging.info(f"   User Manual (PDF): {'Found' if has_manual else 'NO'}")

                domain = get_domain_from_url(url)
                expected_id = BRAND_STORES.get(domain)
                store_correct = False
                if expected_id:
                    if expected_id in driver.page_source:
                        store_correct = True
                        logging.info(f"   Brand Store: MATCH")
                    else:
                        logging.info(f"   Brand Store: MISMATCH")
                else:
                    logging.info(f"   Brand Store: domain '{domain}' not in stores.csv")

                if CHECK_VIDEOS:
                    videos_count, videos_durations = parse_amazon_videos(driver)
                else:
                    videos_count, videos_durations = 0, []
                    logging.info("   Video check skipped by user")

                return {
                    "title": title,
                    "bullets": bullets,
                    "has_manual": has_manual,
                    "store_correct": store_correct,
                    "videos_count": videos_count,
                    "videos_durations": videos_durations
                }

            if attempt == 0:
                logging.info("   Content not fully loaded — quick retry with scroll...")
                driver.execute_script("window.scrollTo(0, document.body.scrollHeight/2);")
                time.sleep(1)
                driver.execute_script("window.scrollTo(0, 0);")
                time.sleep(1)

        videos_count, videos_durations = 0, []
        return {
            "title": title_tag.get_text(strip=True) if title_tag else "NOT FOUND",
            "bullets": bullets or ["NOT FOUND"],
            "has_manual": False,
            "store_correct": False,
            "videos_count": videos_count,
            "videos_durations": videos_durations
        }
    except Exception as e:
        logging.info(f"Error parsing Amazon: {e}")
        return {"title": "NOT FOUND", "bullets": ["NOT FOUND"], "has_manual": False, "store_correct": False,
                "videos_count": 0, "videos_durations": []}

# -----------------------
# IcePIM parser
# -----------------------
def parse_icepim(driver, url):
    try:
        logging.info(f"Parsing IcePIM: {url}")
        driver.get(url)
        WebDriverWait(driver, 5).until(EC.presence_of_element_located((By.TAG_NAME, "body")))
        time.sleep(1)

        soup = BeautifulSoup(driver.page_source, "html.parser")
        lang_match = re.search(r"languageID=(\d+)", url)
        language_id = lang_match.group(1) if lang_match else None
        lang_block = None

        try:
            status_elem = driver.find_element(By.ID, f"approvalStatus-{language_id}")
            status = status_elem.text.strip()
        except:
            status = "NOT FOUND"
        logging.info(f"   IcePIM Status: {status}")

        if language_id:
            btn = soup.find(lambda t: t.name in ['button', 'a'] and t.get('data-lang') == language_id)
            if btn:
                target = btn.get('data-bs-target')
                if target:
                    lang_block = soup.find(id=target.lstrip('#'))
        if not lang_block and language_id:
            lang_block = soup.find(lambda t: t.has_attr('id') and f"language_{language_id}" in t['id'])
        if not lang_block:
            lang_block = soup.find("div", class_=lambda c: c and 'tab-pane' in c and 'active' in c)
        if not lang_block:
            logging.info("   Language block not found")
            return {"title": "NOT FOUND", "bullets": ["NOT FOUND"], "status": status}

        title_input = lang_block.find("input", {"id": lambda x: x and "[name]" in x})
        title = title_input.get("value", "").strip() if title_input else "NOT FOUND"

        bullets = []
        bullet_inputs = lang_block.find_all(
            lambda t: t.name in ["input", "textarea"]
            and t.get("name")
            and re.search(r"(bulletPoints|reasonsToBuy)", t.get("name"), re.I)
        )
        for bi in bullet_inputs:
            text = (bi.get("value") or bi.get_text() or "").strip()
            if not text or len(text) < 3 or len(text) > 350: continue
            if re.search(r"(https?://|www\.|insert|delete|make default|\d{4}-\d{2}-\d{2})", text, re.I): continue
            if text.lower() in ["edit", "delete", "make default"]: continue
            bullets.append(text)

        clean_bullets = list(dict.fromkeys(bullets)) or ["NOT FOUND"]
        logging.info(f"   Title (IcePIM): ok")
        logging.info(f"   Bullets found (IcePIM): ok({len(clean_bullets)})")
        if CHECK_VIDEOS:
            icepim_videos_count, icepim_videos_durations = get_icepim_video_durations_by_modal(driver, language_id)
        else:
            icepim_videos_count, icepim_videos_durations = 0, []
            logging.info("   IcePIM video check skipped by user")

        return {
            "title": title,
            "bullets": clean_bullets,
            "status": status,
            "videos_count": icepim_videos_count,
            "videos_durations": icepim_videos_durations
        }
        return {"title": title, "bullets": clean_bullets, "status": status}
    except Exception as e:
        logging.info(f"Error parsing IcePIM: {e}")
        return {"title": "NOT FOUND", "bullets": ["NOT FOUND"], "status": "ERROR"}


def get_icepim_video_durations_by_modal(driver, language_id):
    logging.info(f"   Parsing IcePIM videos for languageID={language_id}...")
    try:
        video_list = WebDriverWait(driver, 5).until(
            EC.presence_of_element_located((By.ID, f"videoList-{language_id}"))
        )
    except:
        logging.info("   No videoList block found")
        return 0, []

    play_icons = video_list.find_elements(By.CSS_SELECTOR, "i.fa-circle-play")
    count = len(play_icons)
    logging.info(f"   Found {count} videos (by play icon) in videoList-{language_id} — opening each modal...")

    durations = []

    for i, icon in enumerate(play_icons):
        try:
            logging.info(f"     Opening IcePIM video {i+1}/{count}...")
            driver.execute_script("arguments[0].scrollIntoView({block: 'center'});", icon)
            time.sleep(0.5)
            driver.execute_script("arguments[0].closest('a').click();", icon)

            modal = WebDriverWait(driver, 15).until(
                EC.presence_of_element_located((By.CSS_SELECTOR, "div.modal.show"))
            )

            iframe = WebDriverWait(driver, 15).until(
                EC.frame_to_be_available_and_switch_to_it((By.ID, "videoFrame"))
            )

            dur_sec = None
            for attempt in range(20):
                dur_sec = driver.execute_script("""
                    if (window.s7player && typeof s7player.getDuration === 'function') {
                        return s7player.getDuration();
                    }
                    if (window.player && typeof player.getDuration === 'function') {
                        return player.getDuration();
                    }
                    let vid = document.querySelector('video');
                    return vid ? vid.duration : null;
                """)
                if dur_sec and dur_sec > 0:
                    break
                time.sleep(1)

            driver.switch_to.default_content()

            if dur_sec and dur_sec > 0:
                mins = int(dur_sec // 60)
                secs = int(dur_sec % 60)
                formatted = f"{mins}:{secs:02d}"
                durations.append(formatted)
                logging.info(f"     IcePIM Video {i+1} duration: {formatted}")
            else:
                durations.append("?:??")
                logging.info(f"     IcePIM Video {i+1} duration not loaded after waiting")

            try:
                close_btn = driver.find_element(By.CSS_SELECTOR, "div.modal.show button.btn-close")
                driver.execute_script("arguments[0].click();", close_btn)
                time.sleep(1)
            except:
                logging.info("     Close button not found — forcing hide")
                driver.execute_script("document.querySelector('div.modal.show').style.display = 'none';")
                time.sleep(1)

        except Exception as e:
            logging.info(f"     Error with IcePIM video {i+1}: {e}")
            durations.append("error")
            driver.switch_to.default_content()

    logging.info(f"   IcePIM video durations extracted: {durations}")
    return count, durations


# -----------------------
# Amazon images
# -----------------------
def download_amazon_images(driver, asin):
    folder = os.path.join(os.getcwd(), f"tmp_amazon_{asin}")
    os.makedirs(folder, exist_ok=True)

    if CHECK_VIDEOS:
        logging.info("   Reloading page...")
        driver.refresh()
        WebDriverWait(driver, 5).until(
            EC.presence_of_element_located((By.ID, "productTitle"))
        )
        time.sleep(1.5)
    
    logging.info("   Opening lightbox to count real gallery size...")
    try:
        main_img = None
        selectors = [
            "#landingImage",
            "#imgTagWrapperId img",
            "img.a-dynamic-image",
            "#main-image-container img"
        ]

        for sel in selectors:
            try:
                main_img = WebDriverWait(driver, 5).until(
                    EC.element_to_be_clickable((By.CSS_SELECTOR, sel))
                )
                break
            except:
                continue

        if not main_img:
            raise Exception("Main image not found")

        driver.execute_script("arguments[0].scrollIntoView({block: 'center'});", main_img)
        time.sleep(1)

        try:
            main_img.click()
        except:
            driver.execute_script("arguments[0].click();", main_img)

        time.sleep(1)

        thumbs = driver.find_elements(By.CSS_SELECTOR, "#ivThumbs img, .ivThumbImage")
        visible_thumbs = [t for t in thumbs if t.is_displayed() and t.size['width'] > 40]
        count = len(visible_thumbs)

        if count == 0:
            raise Exception("Thumbnails not found")

        logging.info(f"   Detected {count} thumbnails in lightbox")

        try:
            close_btn = driver.find_element(By.CSS_SELECTOR, "#ivClose, button.a-button-close")
            driver.execute_script("arguments[0].click();", close_btn)
        except:
            pass
        time.sleep(1)

    except Exception as e:
        logging.info(f"   Lightbox failed: {e} → fallback count = 10")
        count = 10

    urls = extract_all_hires(driver.page_source)
    urls = list(dict.fromkeys([u for u in urls if u and "media-amazon.com" in u]))[:count]

    logging.info(f"   Downloading {len(urls)} images")
    headers = {"User-Agent": "Mozilla/5.0"}
    for i, url in enumerate(urls):
        filename = f"{asin}.MAIN.jpg" if i == 0 else f"{asin}.PT{i:02d}.jpg"
        path = os.path.join(folder, filename)
        for retry in range(3):
            try:
                r = requests.get(url, headers=headers, timeout=30)
                r.raise_for_status()
                with open(path, "wb") as f:
                    f.write(r.content)
                logging.info(f"     Downloaded: {filename}")
                break
            except Exception as e:
                logging.info(f"     Failed {filename} (retry {retry+1})")
                time.sleep(2)
        else:
            open(path, 'a').close()

    return folder

# -----------------------
# IcePIM ZIP
# -----------------------
def download_icepim_images(driver, asin, download_dir=DOWNLOAD_DIR):
    logging.info("   Downloading gallery zip from IcePIM...")
    for attempt in range(2):
        try:
            driver.execute_script("if (typeof openDownloadImagesModal === 'function') openDownloadImagesModal();")
            time.sleep(1)
            asin_input = WebDriverWait(driver, 5).until(
                EC.presence_of_element_located((By.CSS_SELECTOR, "div.modal.show input[type='text']"))
            )
            break
        except:
            logging.info(f"   Modal not opened, retry {attempt+1}")
            time.sleep(2)
    else:
        logging.info("   Failed to open modal")
        return None, None

    try:
        asin_input.clear()
        asin_input.send_keys(asin)
        time.sleep(0.5)
        buttons = driver.find_elements(By.CSS_SELECTOR, "div.modal.show button")
        if not buttons:
            logging.info("   No buttons in modal")
            return None, None
        download_btn = buttons[-1]
        driver.execute_script("arguments[0].click();", download_btn)
    except Exception as e:
        logging.info(f"   Failed to trigger download: {e}")
        return None, None

    logging.info("   Waiting for ZIP...")
    start = time.time()
    while time.time() - start < 120:
        files = [f for f in os.listdir(download_dir) if f.endswith('.zip') and not f.endswith('.crdownload')]
        if files:
            zip_path = os.path.join(download_dir, max(files, key=lambda f: os.path.getmtime(os.path.join(download_dir, f))))
            logging.info(f"       Done: {os.path.basename(zip_path)}")
            extract_dir = os.path.join(os.getcwd(), f"tmp_icepim_{asin}")
            os.makedirs(extract_dir, exist_ok=True)
            with zipfile.ZipFile(zip_path, 'r') as z:
                z.extractall(extract_dir)
            return extract_dir, zip_path
        time.sleep(1)
    logging.info("   ZIP timeout")
    return None, None

# -----------------------
# Image hash and comparison
# -----------------------
def remove_white_bg_and_crop(image_path, white_threshold=240):
    try:
        img_cv = cv2.imread(image_path)
        if img_cv is None: return None
        img_rgb = cv2.cvtColor(img_cv, cv2.COLOR_BGR2RGB)
        mask = cv2.inRange(img_rgb, np.array([white_threshold]*3), np.array([255]*3))
        mask_inv = cv2.bitwise_not(mask)
        contours, _ = cv2.findContours(mask_inv, cv2.RETR_EXTERNAL, cv2.CHAIN_APPROX_SIMPLE)
        if not contours: return None
        x, y, w, h = cv2.boundingRect(max(contours, key=cv2.contourArea))
        cropped = img_rgb[y:y+h, x:x+w]
        return Image.fromarray(cropped).resize((256, 256), Image.Resampling.LANCZOS)
    except: return None

def get_dhash(path):
    img = remove_white_bg_and_crop(path)
    return str(imagehash.dhash(img)) if img else None

def compare_images_by_name_strict(amazon_folder, icepim_folder):
    logging.info("   Gallery compare:")
    if not icepim_folder or not os.path.exists(icepim_folder):
        logging.info("     IcePIM gallery missing")
        return {"summary": "0/0", "images_match": False, "detailed_summary": "PIM folder missing"}

    a_files = [f for f in os.listdir(amazon_folder) if f.lower().endswith(('.jpg', '.jpeg'))]
    i_files = [f for f in os.listdir(icepim_folder) if f.lower().endswith(('.jpg', '.jpeg', '.png'))]

    a_dict = {os.path.splitext(f)[0]: f for f in a_files}
    i_dict = {os.path.splitext(f)[0]: f for f in i_files}

    all_bases = set(a_dict.keys()) | set(i_dict.keys())
    matched = 0
    total_pairs = 0

    for base in sorted(all_bases):
        a_file = a_dict.get(base)
        i_file = i_dict.get(base)

        if a_file and i_file:
            total_pairs += 1
            h1 = get_dhash(os.path.join(amazon_folder, a_file))
            h2 = get_dhash(os.path.join(icepim_folder, i_file))
            if h1 and h2:
                dist = sum(c1 != c2 for c1, c2 in zip(h1, h2))
                status = "MATCH" if dist <= IMAGE_THRESHOLD else "DIFFER"
                if status == "MATCH":
                    matched += 1
                logging.info(f"     {a_file} -> {i_file} | dist={dist} -> {status}")
            else:
                logging.info(f"     {a_file} -> {i_file} | ERROR (hash failed)")

        elif a_file:
            logging.info(f"     {a_file} → Missing in IcePIM")
        elif i_file:
            logging.info(f"     Missing in Amazon → {i_file}")

    amazon_count = len(a_files)
    pim_count = len(i_files)

    if amazon_count == pim_count and matched == total_pairs:
        detailed_summary = f"{amazon_count} Amazon / {pim_count} PIM, all MATCH"
        images_match = True
    elif amazon_count != pim_count:
        mismatch_count = total_pairs - matched
        detailed_summary = f"{amazon_count} Amazon / {pim_count} PIM, Different q-ty, {mismatch_count} Mismatch"
        images_match = False
    else:
        mismatch_count = total_pairs - matched
        detailed_summary = f"{amazon_count} Amazon / {pim_count} PIM, {matched} Match, {mismatch_count} Mismatch"
        images_match = False

    logging.info(f"   Summary: {detailed_summary}")

    return {
        "summary": f"{amazon_count}/{pim_count}",
        "images_match": images_match,
        "detailed_summary": detailed_summary
    }

# -----------------------
# Export to Amazon if mismatch
# -----------------------
def export_to_amazon_if_needed(driver, amazon_url, title_match, bullets_match):
    if title_match and bullets_match:
        logging.info("   Title and Bullets match → export not needed")
        return

    logging.info("   Mismatch detected → starting export to Amazon")

    locale_map = {
        "amazon.co.uk": "Amazon UK",
        "amazon.de": "Amazon DE",
        "amazon.fr": "Amazon FR",
        "amazon.it": "Amazon IT",
        "amazon.es": "Amazon ES",
        "amazon.nl": "Amazon NL",
        "amazon.pl": "Amazon PL",
        "amazon.se": "Amazon SE",
        "amazon.com": "Amazon US",
        "amazon.ca": "Amazon CA",
        "amazon.com.mx": "Amazon MX",
        "amazon.com.br": "Amazon BR",
        "amazon.com.tr": "Amazon TR",
        "amazon.sg": "Amazon SG",
        "amazon.ie": "Amazon IE",
        "amazon.com.be": "Amazon BE",
    }

    domain = get_domain_from_url(amazon_url)
    target_locale = locale_map.get(domain)
    if not target_locale:
        logging.info(f"   Locale {domain} not supported")
        return

    try:
        export_btn = WebDriverWait(driver, 5).until(
            EC.element_to_be_clickable((By.XPATH, "//button[contains(., 'Export to Amazon')]"))
        )
        driver.execute_script("arguments[0].scrollIntoView({block: 'center'});", export_btn)
        time.sleep(1)
        driver.execute_script("arguments[0].click();", export_btn)
        logging.info("   Clicked 'Export to Amazon'")

        WebDriverWait(driver, 5).until(EC.visibility_of_element_located((By.ID, "export-to-amazon-modal")))

        select = WebDriverWait(driver, 5).until(
            EC.presence_of_element_located((By.ID, "export_to_amazon_selector"))
        )

        option_xpath = f"//select[@id='export_to_amazon_selector']/option[contains(text(), '{target_locale}')]"
        option = WebDriverWait(driver, 5).until(
            EC.presence_of_element_located((By.XPATH, option_xpath))
        )
        option_value = option.get_attribute("value")

        driver.execute_script("""
            let select = document.getElementById('export_to_amazon_selector');
            select.value = arguments[0];
            select.dispatchEvent(new Event('change'));
        """, option_value)

        logging.info(f"   Selected locale: {target_locale}")

        ok_btn = WebDriverWait(driver, 5).until(
            EC.element_to_be_clickable((By.ID, "btn-export-to-amazon"))
        )
        driver.execute_script("arguments[0].click();", ok_btn)
        logging.info("   Export started!")

        time.sleep(3)

    except Exception as e:
        logging.info(f"   Export error: {e}")

# -----------------------
# Process functions
# -----------------------
def process_amazon(row, idx, total):
    asin_match = re.search(r"/dp/([A-Z0-9]{10})", row.get("amazon_url", ""))
    asin = asin_match.group(1) if asin_match else f"unknown_{idx}"

    amazon_url = row.get("amazon_url", "").strip()
    amazon_driver.get(amazon_url)

    amazon_data = parse_amazon(amazon_driver, amazon_url, is_first=(idx == 1))

    amazon_folder = None
    if CHECK_IMAGES:
        amazon_folder = download_amazon_images(amazon_driver, asin)

    return asin, amazon_data, amazon_folder

def process_icepim(row, idx):
    icepim_url = row.get("icepim_url", "").strip()
    icepim_data = parse_icepim(icepim_driver, icepim_url)

    icepim_folder = None
    zip_path = None
    if CHECK_IMAGES and icepim_data["status"] == "Approved":
        asin_match = re.search(r"/dp/([A-Z0-9]{10})", row.get("amazon_url", ""))
        asin = asin_match.group(1) if asin_match else "unknown"
        icepim_folder, zip_path = download_icepim_images(icepim_driver, asin)

    return icepim_data, icepim_folder, zip_path

# -----------------------
# Main
# -----------------------
def main():
    global EXPORT_ENABLED, CHECK_IMAGES, CHECK_VIDEOS, LINKS_FILE, BRAND_STORES

    EXPORT_ENABLED = var_export.get()
    CHECK_IMAGES = var_images.get()
    CHECK_VIDEOS = var_videos.get()
    LINKS_FILE = file_path_var.get()

    os.makedirs(DOWNLOAD_DIR, exist_ok=True)

    if not os.path.exists(LINKS_FILE):
        messagebox.showerror("Error", f"Links file not found:\n{LINKS_FILE}")
        label_status.config(text="Error: file not found", foreground="red")
        return

    icepim_username = entry_login.get().strip()
    icepim_password = entry_password.get().strip()

    if not icepim_username or not icepim_password:
        messagebox.showerror("Error", "Please enter IcePIM login and password")
        label_status.config(text="Error: credentials missing", foreground="red")
        return

    logging.info("\n" + "="*70)
    logging.info("    Amazon IcePIM parser v2.0 GUI STARTED")
    logging.info("="*70)
    logging.info(f"Export enabled: {EXPORT_ENABLED}")
    logging.info(f"Check images: {CHECK_IMAGES}")
    logging.info(f"Check videos: {CHECK_VIDEOS}")
    logging.info(f"Links file: {LINKS_FILE}")
    logging.info("="*70 + "\n")

    label_status.config(text="Initializing drivers...", foreground="blue")

    BRAND_STORES = {
        "amazon.de": "73DDF00A-668C-4A2A-A0C9-2B6DB76C09B9",
        "amazon.es": "F30F4C2C-4593-407B-8068-11FF9FCDFD94",
        "amazon.fr": "4FDBCD69-9258-46BC-AF48-2F12C444BC29",
        "amazon.pl": "33F74A81-6FB6-4639-BB12-50719E1D9A68",
        "amazon.it": "7B9E67E6-2B58-48F3-B172-FB67368C3DC8",
        "amazon.se": "38E27816-B48F-4680-B30C-BFF800108976",
        "amazon.co.uk": "62B78CC9-2C16-479D-AA2A-1E77A3502715",
        "amazon.nl": "3BEBCEA2-AAF5-4D6C-96CF-0B6E3A689FF9",
        "amazon.com.be": "5BD8DDA5-5A93-4452-B515-20CC49A953DF",
        "amazon.com": "0B79BD36-E01B-4440-A79B-9D7405B69466",
        "amazon.ca": "CC82ADD6-9EBF-4ABA-B561-37E944383870",
        "amazon.com.mx": "AFD534C4-FF19-43CC-BDBE-78C942961A9C",
        "amazon.com.br": "C27D6466-1AC7-4C6E-89AD-E26D8C204E9D",
        "amazon.com.tr": "B7EE2800-05C9-4D22-9E22-C63EF2D95C21",
        "amazon.sg": "3DE896C3-B849-4878-9835-92B181088375"
    }
    
    init_drivers()

##    global login_icepim
##    login_icepim = login_icepim_gui

    with open(LINKS_FILE, newline="", encoding="utf-8") as f:
        rows = list(csv.DictReader(f))

    total = len(rows)
    if total == 0:
        messagebox.showinfo("Info", "No rows in links file")
        label_status.config(text="No data", foreground="orange")
        return

    fieldnames = ["ASIN","Title","Bullets","Images","IcePIM Status","User Manual","Brand Store","Video","Video Details","Images Details"]
    with open(RESULTS_CSV, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()

    table = PrettyTable()
    table.field_names = fieldnames

    progress_bar["maximum"] = total
    progress_bar["value"] = 0
    progress_label.config(text=f"Progress: 0 / {total}")
    label_status.config(text="Parsing started...", foreground="blue")

    for idx, row in enumerate(rows, start=1):
        asin_match = re.search(r"/dp/([A-Z0-9]{10})", row.get("amazon_url", ""))
        asin = asin_match.group(1) if asin_match else f"unknown_{idx}"

        logging.info("=" * 55)
        logging.info(f"[{idx}/{total}] ASIN: {asin}")
        logging.info("=" * 55)

        with ThreadPoolExecutor(max_workers=2) as executor:
            future_amazon = executor.submit(process_amazon, row, idx, total)
            future_icepim = executor.submit(process_icepim, row, idx)

            _, amazon_data, amazon_folder = future_amazon.result()
            icepim_data, icepim_folder, zip_path = future_icepim.result()

        if CHECK_IMAGES:
            img_comp = compare_images_by_name_strict(amazon_folder, icepim_folder)
            images_match = img_comp["images_match"]
            detailed_summary = img_comp["detailed_summary"]
            if zip_path and not images_match:
                dest = os.path.join("galleries for upload", f"{asin}.zip")
                os.makedirs("galleries for upload", exist_ok=True)
                shutil.copy2(zip_path, dest)
                logging.info(f"   Gallery saved → {dest}")
        else:
            images_match = True
            detailed_summary = "Image check disabled"

        def clean(text):
            return re.sub(r'[.,;™©\s]+', '', text.strip().lower())

        title_match = clean(amazon_data["title"]) == clean(icepim_data["title"])
        bullets_match = (
            len(amazon_data["bullets"]) == len(icepim_data["bullets"]) and
            all(clean(a) == clean(b) for a, b in zip(amazon_data["bullets"], icepim_data["bullets"]))
        )

        logging.info(f"   Title compare: {'MATCH' if title_match else 'DIFFER'}")
        logging.info(f"   Bullets compare: {'MATCH' if bullets_match else 'DIFFER'}")

        if EXPORT_ENABLED and (not title_match or not bullets_match):
            export_to_amazon_if_needed(icepim_driver, row.get("amazon_url", ""), title_match, bullets_match)

        amazon_v_count = amazon_data.get("videos_count", 0)
        amazon_v_dur_set = set(amazon_data.get("videos_durations", []))

        icepim_v_count = icepim_data.get("videos_count", 0)
        icepim_v_dur = icepim_data.get("videos_durations", [])

        has_unknown_in_icepim = any(d in ["?:??", "error"] for d in icepim_v_dur)

        icepim_known_dur = [d for d in icepim_v_dur if d not in ["?:??", "error"]]
        icepim_known_set = set(icepim_known_dur)

        if has_unknown_in_icepim:
            video_status = "Warning"
            video_details = f"A:{amazon_v_count} ({', '.join(sorted(amazon_v_dur_set))}) | I:{icepim_v_count} ({', '.join(icepim_v_dur)}) → WARNING: some IcePIM videos not loaded"
        elif icepim_known_set.issubset(amazon_v_dur_set):
            video_status = "Match"
            video_details = f"A:{amazon_v_count} ({', '.join(sorted(amazon_v_dur_set))}) | I:{icepim_v_count} ({', '.join(icepim_v_dur)}) → All IcePIM videos present on Amazon"
        else:
            video_status = "Need upload"
            missing = icepim_known_set - amazon_v_dur_set
            video_details = f"A:{amazon_v_count} ({', '.join(sorted(amazon_v_dur_set))}) | I:{icepim_v_count} ({', '.join(icepim_v_dur)}) → Need upload: missing {sorted(missing)}"

        logging.info(f"   Video status: {video_status}")
        logging.info(f"   {video_details}")

        table.add_row([
            asin,
            "MATCH" if title_match else "DIFFER",
            "MATCH" if bullets_match else "DIFFER",
            "MATCH" if images_match else "DIFFER",
            icepim_data["status"],
            "YES" if amazon_data["has_manual"] else "NO",
            "YES" if amazon_data["store_correct"] else "NO",
            video_status,
            video_details,
            detailed_summary
        ])

        with open(RESULTS_CSV, "a", newline="", encoding="utf-8") as f:
            w = csv.DictWriter(f, fieldnames=fieldnames)
            w.writerow({
                "ASIN": asin,
                "Title": "MATCH" if title_match else "DIFFER",
                "Bullets": "MATCH" if bullets_match else "DIFFER",
                "Images": "MATCH" if images_match else "DIFFER",
                "IcePIM Status": icepim_data["status"],
                "User Manual": "YES" if amazon_data["has_manual"] else "NO",
                "Brand Store": "YES" if amazon_data["store_correct"] else "NO",
                "Video": video_status,
                "Video Details": video_details,
                "Images Details": detailed_summary
            })

        for p in [amazon_folder, icepim_folder]:
            if p and os.path.exists(p):
                shutil.rmtree(p, ignore_errors=True)
        if zip_path and os.path.exists(zip_path):
            os.remove(zip_path)

        progress_bar["value"] = idx
        progress_label.config(text=f"Progress: {idx} / {total}")

    logging.info("\n" + "="*55)
    logging.info("FINAL RESULTS:")
    print(table)
    logging.info("="*55)
    logging.info(f"Report saved to: {RESULTS_CSV}")

    label_status.config(text="Completed successfully!", foreground="green")

    shutil.rmtree("downloads", ignore_errors=True)

    

log_queue = queue.Queue()

class QueueHandler(logging.Handler):
    def emit(self, record):
        log_queue.put(self.format(record))

logging.getLogger().addHandler(QueueHandler())



def run_parser():
    global EXPORT_ENABLED, CHECK_IMAGES, CHECK_VIDEOS, LINKS_FILE
    btn_start.config(state="disabled")
    label_status.config(text="Initializing drivers...", foreground="blue")
    progress_bar["value"] = 0
    progress_label.config(text="Progress: 0 / 0")
    log_text.config(state="normal")
    log_text.delete("1.0", "end")
    log_text.config(state="disabled")
    EXPORT_ENABLED = var_export.get()
    CHECK_IMAGES = var_images.get()
    CHECK_VIDEOS = var_videos.get()
    LINKS_FILE = file_path_var.get()

    global seen_lines
    seen_lines = set()  
    log_text.config(state="normal")
    log_text.delete("1.0", "end")  
    log_text.config(state="disabled")

    if not os.path.exists(LINKS_FILE):
        messagebox.showerror("Error", f"Links file not found:\n{LINKS_FILE}")
        label_status.config(text="Error: file not found", foreground="red")
        btn_start.config(state="normal")
        return

    icepim_login = entry_login.get().strip()
    icepim_password = entry_password.get().strip()
    if not icepim_login or not icepim_password:
        messagebox.showerror("Error", "Please enter IcePIM login and password")
        label_status.config(text="Error: credentials missing", foreground="red")
        btn_start.config(state="normal")
        return

    btn_start.config(state="disabled")
    label_status.config(text="Starting...", foreground="blue")
    progress_bar["value"] = 0
    progress_label.config(text="Progress: 0 / 0")

    def thread_target():
        try:
            init_drivers()
            main()  
            root.after(0, lambda: label_status.config(text="Completed successfully!", foreground="green"))
        except Exception as e:
            root.after(0, lambda: messagebox.showerror("Error", f"Error during parsing:\n{e}"))
            root.after(0, lambda: label_status.config(text="Error occurred", foreground="red"))
        finally:
            root.after(0, lambda: btn_start.config(state="normal"))

    threading.Thread(target=thread_target, daemon=True).start()


# === GUI ===
root = tk.Tk()
root.title("Amazon IcePIM Parser v2.0")
root.geometry("700x750")
root.resizable(False, False)

title_label = tk.Label(root, text="Amazon IcePIM Parser", font=("Helvetica", 18, "bold"))
title_label.pack(pady=20)

main_container = tk.Frame(root)
main_container.pack(fill="both", expand=True, padx=40, pady=10)

top_frame = tk.Frame(main_container)
top_frame.pack(fill="x", pady=10)

settings_frame = tk.LabelFrame(top_frame, text="Settings", font=("Helvetica", 10, "bold"), padx=20, pady=15)
settings_frame.pack(side="left", padx=(0, 30))

var_titles = tk.BooleanVar(value=True)
tk.Checkbutton(settings_frame, text="Check Titles and Bullet Points", variable=var_titles, state="disabled").pack(anchor="w", pady=5)

var_images = tk.BooleanVar(value=False)
tk.Checkbutton(settings_frame, text="Download and check images", variable=var_images).pack(anchor="w", pady=5)

var_videos = tk.BooleanVar(value=False)
tk.Checkbutton(settings_frame, text="Check videos", variable=var_videos).pack(anchor="w", pady=5)

var_export = tk.BooleanVar(value=False)
tk.Checkbutton(settings_frame, text="Run Export to Amazon if mismatch", variable=var_export).pack(anchor="w", pady=5)

credentials_frame = tk.LabelFrame(top_frame, text="IcePIM Credentials", font=("Helvetica", 10, "bold"), padx=20, pady=15)
credentials_frame.pack(side="right")

tk.Label(credentials_frame, text="Login:").grid(row=0, column=0, sticky="w", pady=5)
entry_login = tk.Entry(credentials_frame, width=30)
entry_login.grid(row=0, column=1, pady=5, padx=(10,0))

tk.Label(credentials_frame, text="Password:").grid(row=1, column=0, sticky="w", pady=5)
entry_password = tk.Entry(credentials_frame, width=30, show="*")
entry_password.grid(row=1, column=1, pady=5, padx=(10,0))

def save_creds():
    login = entry_login.get().strip()
    password = entry_password.get().strip()
    if login and password:
        save_credentials(login, password)
        messagebox.showinfo("Saved", "Credentials saved securely!")
    else:
        messagebox.showwarning("Warning", "Enter both login and password")

tk.Button(credentials_frame, text="Save Credentials", command=save_creds).grid(row=2, column=0, columnspan=2, pady=15)

saved_login, saved_password = load_credentials()
entry_login.insert(0, saved_login)
entry_password.insert(0, saved_password)

links_frame = tk.Frame(main_container)
links_frame.pack(fill="x", pady=20)

tk.Label(links_frame, text="Links file:").pack(side="left")
file_path_var = tk.StringVar(value="links.csv")
entry_file = tk.Entry(links_frame, textvariable=file_path_var, width=50)
entry_file.pack(side="left", expand=True, fill="x", padx=(10,0))

def browse_file():
    filename = filedialog.askopenfilename(filetypes=[("CSV files", "*.csv")])
    if filename:
        file_path_var.set(filename)

tk.Button(links_frame, text="Browse...", command=browse_file).pack(side="right")

progress_frame = tk.Frame(main_container)
progress_frame.pack(fill="x", pady=10)
progress_label = tk.Label(progress_frame, text="Progress: 0 / 0", font=("Helvetica", 10))
progress_label.pack()
progress_bar = ttk.Progressbar(progress_frame, length=700, mode="determinate")
progress_bar.pack(pady=5)

buttons_frame = tk.Frame(main_container)
buttons_frame.pack(fill="x", pady=30)

btn_start = tk.Button(buttons_frame,
                      text="Start Parsing",
                      command=run_parser,
                      bg="#4CAF50",
                      activebackground="#45a049",
                      fg="white",
                      font=("Helvetica", 12, "bold"),
                      padx=30,
                      pady=12,
                      relief="raised",
                      bd=8,
                      cursor="hand2")
btn_start.pack(side="left")

def on_enter(e):
    btn_start.config(bg="#66BB6A")
def on_leave(e):
    btn_start.config(bg="#4CAF50")
btn_start.bind("<Enter>", on_enter)
btn_start.bind("<Leave>", on_leave)

def open_results():
    if os.path.exists(RESULTS_CSV):
        os.startfile(RESULTS_CSV)
    else:
        messagebox.showinfo("Info", "Results file not ready yet")

btn_open_results = tk.Button(buttons_frame, text="Open results file", command=open_results)
btn_open_results.pack(side="right", ipadx=15, ipady=10)

label_status = tk.Label(main_container, text="Ready", foreground="gray", font=("Helvetica", 10))
label_status.pack(pady=5)

log_frame = tk.LabelFrame(main_container, text="Log", padx=10, pady=10)
log_frame.pack(fill="both", expand=True, padx=10, pady=10)
log_text = scrolledtext.ScrolledText(log_frame, height=6, state="disabled", font=("Courier", 9))
log_text.pack(fill="both", expand=True)

seen_lines = set()

def update_log():
    while not log_queue.empty():
        line = log_queue.get()
        if line not in seen_lines:
            seen_lines.add(line)
            log_text.config(state="normal")
            log_text.insert("end", line + "\n")
            lines = log_text.get("1.0", "end").splitlines()
            if len(lines) > 6:
                log_text.delete("1.0", "2.0")
            log_text.see("end")
            log_text.config(state="disabled")
    root.after(500, update_log)

root.after(500, update_log)
def on_closing():
    for d in [amazon_driver, icepim_driver]:
        if d:
            try:
                d.quit()
            except:
                pass
    root.destroy()

root.protocol("WM_DELETE_WINDOW", on_closing)

root.mainloop()
