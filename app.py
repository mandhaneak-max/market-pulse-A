"""
Market Pulse — Backend (Flask)
==============================
Fetches live financial headlines from free Indian RSS feeds and uses
Google Gemini to turn each headline into a plain-language impact card
(sectors affected, stocks affected, estimated % move, overall sentiment).

Run locally:
    export GEMINI_API_KEY="your-key-here"
    python app.py

Deploy: see the setup guide provided alongside this file.
"""

from __future__ import annotations

import os
import re
import csv
import json
import time
import hashlib
import threading
from datetime import datetime, timedelta, timezone

import requests
import feedparser
from bs4 import BeautifulSoup
from flask import Flask, jsonify, request, send_from_directory
from flask_cors import CORS
from concurrent.futures import ThreadPoolExecutor

# --------------------------------------------------------------------------
# App setup
# --------------------------------------------------------------------------

BASE_DIR = os.path.dirname(os.path.abspath(__file__))

app = Flask(__name__, static_folder=BASE_DIR, static_url_path="")
CORS(app)  # allow index.html to call this API from any origin (needed if you host frontend separately)

# --------------------------------------------------------------------------
# Configuration
# --------------------------------------------------------------------------

GEMINI_API_KEY = os.environ.get("GEMINI_API_KEY", "").strip()
# You can override the model via an env var without touching code.
# Google retires/renames Gemini models periodically — if this one ever
# 404s again, check https://ai.google.dev/gemini-api/docs/models for the
# current generally-available (GA) model name and update here or via the
# GEMINI_MODEL environment variable (no code change needed).
GEMINI_MODEL = os.environ.get("GEMINI_MODEL", "gemini-3.6-flash")
GEMINI_URL = (
    f"https://generativelanguage.googleapis.com/v1beta/models/{GEMINI_MODEL}:generateContent"
)

# --------------------------------------------------------------------------
# Visitor analytics — lightweight, in-memory (no database needed).
# NOTE: this resets whenever the Render process restarts/redeploys/sleeps
# (free-tier dynos aren't persistent). That's fine for a rough "how many
# people are visiting and when" view; it just won't remember history across
# restarts. Ask me if you'd like this made persistent later (e.g. a small
# SQLite file or a free hosted DB) — happy to wire that up too.
# --------------------------------------------------------------------------
ADMIN_KEY = os.environ.get("ADMIN_KEY", "atharv2026")  # change this via Render's env var settings!
_visits: list[dict] = []
_visits_lock = threading.Lock()
MAX_STORED_VISITS = 20000  # keep memory bounded on a long-running free dyno

# Free, publicly-available Indian financial news RSS feeds.
# If any one of these ever changes its URL, the app keeps working with the rest
# (each feed is fetched in its own try/except block).
# Each feed is tagged with a default "category" so the Stock News / Commodity
# News pages can filter by SOURCE (precise) rather than guessing from
# keywords in the title (noisy) — the dedicated Moneycontrol Commodities feed
# is the app's own commodities desk, so anything from it is reliably
# commodity news. A per-article keyword override below also re-classifies
# any commodity-flavoured article that slips into a general "stock" feed
# (and vice-versa), so the split stays clean either way.
RSS_FEEDS = {
    "Moneycontrol": {"url": "https://www.moneycontrol.com/rss/business.xml", "category": "stock"},
    "Moneycontrol Markets": {"url": "https://www.moneycontrol.com/rss/marketreports.xml", "category": "stock"},
    "Economic Times": {"url": "https://economictimes.indiatimes.com/markets/rssfeeds/1977021501.cms", "category": "stock"},
    "Livemint": {"url": "https://www.livemint.com/rss/markets", "category": "stock"},
    "Business Standard": {"url": "https://www.business-standard.com/rss/markets-106.rss", "category": "stock"},
    "Financial Express": {"url": "https://www.financialexpress.com/market/feed/", "category": "stock"},
    "CNBC-TV18": {"url": "https://www.cnbctv18.com/commonfeeds/v1/cne/rss/market.xml", "category": "stock"},
    "Moneycontrol Commodities": {"url": "https://www.moneycontrol.com/rss/commodities.xml", "category": "commodity"},
}

# Any article (regardless of which feed it came from) whose title clearly
# reads as commodity news gets bucketed as "commodity" even if it came from
# a general "stock" feed — and, by elimination, anything NOT matching stays
# out of the commodity bucket, keeping Stock News free of gold/crude stories.
COMMODITY_TITLE_KEYWORDS = (
    "gold", "silver", "bullion", "crude oil", "crude prices", "mcx", "brent",
    "wti", "commodity", "commodities", "natural gas", "copper", "zinc",
    "aluminium", "opec", "precious metal",
)

FETCH_INTERVAL_SECONDS = 300     # re-pull RSS feeds at most every 5 minutes
MAX_STORED_ARTICLES = 3000       # keep a much larger accumulated history
REQUEST_TIMEOUT = 12

# Free, unofficial Yahoo Finance "chart" endpoint — no API key required.
# NOTE: this is an undocumented public endpoint. It's fine for a personal/
# free-tier project, but Yahoo can rate-limit or change it without notice.
# If it ever stops working, swap TICKER_SYMBOLS for a proper market-data
# provider (e.g. Twelve Data, Alpha Vantage, or NSE's own data feeds).
YAHOO_CHART_URL = "https://query1.finance.yahoo.com/v8/finance/chart/{symbol}"
YAHOO_HEADERS = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) MarketPulse/1.0"}
TICKER_SYMBOLS = {
    "sensex": "^BSESN",
    "nifty": "^NSEI",
    "usdinr": "INR=X",
    "crude": "CL=F",
}
TICKER_CACHE_SECONDS = 60

# NSE India's own (unofficial but official-source) JSON API. This needs a
# warmed-up session (cookies from a normal page load) before the API will
# respond — that's what _get_nse_session() does. This is the most accurate
# source we can get for free for individual share prices and the Nifty
# index; Sensex/gold/silver/crude/USD-INR aren't published by NSE so those
# stay on the Yahoo fallback above.
NSE_BASE = "https://www.nseindia.com"
NSE_QUOTE_API = "https://www.nseindia.com/api/quote-equity"
NSE_INDICES_API = "https://www.nseindia.com/api/allIndices"
NSE_HEADERS = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                  "(KHTML, like Gecko) Chrome/124.0 Safari/537.36",
    "Accept": "*/*",
    "Accept-Language": "en-US,en;q=0.9",
    "Referer": "https://www.nseindia.com/",
}
NSE_SESSION_TTL = 240  # re-warm cookies every 4 minutes
_nse_session_cache = {"session": None, "time": 0.0}

# Common Indian stocks the search bar / chips can resolve to an NSE symbol.
# alias (lowercase) -> (NSE symbol, display name). Add more any time —
# it's just a lookup table.
STOCK_SYMBOLS = {
    "reliance": ("RELIANCE", "Reliance Industries"),
    "tcs": ("TCS", "Tata Consultancy Services"),
    "tata consultancy": ("TCS", "Tata Consultancy Services"),
    "tata motors": ("TATAMOTORS", "Tata Motors"),
    "tata steel": ("TATASTEEL", "Tata Steel"),
    "tata power": ("TATAPOWER", "Tata Power"),
    "tata consumer": ("TATACONSUM", "Tata Consumer Products"),
    "tata elxsi": ("TATAELXSI", "Tata Elxsi"),
    "hdfc bank": ("HDFCBANK", "HDFC Bank"),
    "hdfc": ("HDFCBANK", "HDFC Bank"),
    "hdfc life": ("HDFCLIFE", "HDFC Life Insurance"),
    "hdfc amc": ("HDFCAMC", "HDFC Asset Management"),
    "infosys": ("INFY", "Infosys"),
    "sbi": ("SBIN", "State Bank of India"),
    "state bank of india": ("SBIN", "State Bank of India"),
    "sbi life": ("SBILIFE", "SBI Life Insurance"),
    "sbi cards": ("SBICARD", "SBI Cards & Payment Services"),
    "maruti": ("MARUTI", "Maruti Suzuki"),
    "maruti suzuki": ("MARUTI", "Maruti Suzuki"),
    "adani enterprises": ("ADANIENT", "Adani Enterprises"),
    "adani": ("ADANIENT", "Adani Enterprises"),
    "adani ports": ("ADANIPORTS", "Adani Ports & SEZ"),
    "adani green": ("ADANIGREEN", "Adani Green Energy"),
    "adani power": ("ADANIPOWER", "Adani Power"),
    "adani energy": ("ADANIENSOL", "Adani Energy Solutions"),
    "ambuja": ("AMBUJACEM", "Ambuja Cements"),
    "icici bank": ("ICICIBANK", "ICICI Bank"),
    "icici": ("ICICIBANK", "ICICI Bank"),
    "icici lombard": ("ICICIGI", "ICICI Lombard General Insurance"),
    "icici prudential": ("ICICIPRULI", "ICICI Prudential Life Insurance"),
    "axis bank": ("AXISBANK", "Axis Bank"),
    "wipro": ("WIPRO", "Wipro"),
    "bharti airtel": ("BHARTIARTL", "Bharti Airtel"),
    "airtel": ("BHARTIARTL", "Bharti Airtel"),
    "itc": ("ITC", "ITC"),
    "larsen": ("LT", "Larsen & Toubro"),
    "l&t": ("LT", "Larsen & Toubro"),
    "hindustan unilever": ("HINDUNILVR", "Hindustan Unilever"),
    "hul": ("HINDUNILVR", "Hindustan Unilever"),
    "kotak": ("KOTAKBANK", "Kotak Mahindra Bank"),
    "kotak bank": ("KOTAKBANK", "Kotak Mahindra Bank"),
    "bajaj finance": ("BAJFINANCE", "Bajaj Finance"),
    "bajaj finserv": ("BAJAJFINSV", "Bajaj Finserv"),
    "bajaj auto": ("BAJAJ-AUTO", "Bajaj Auto"),
    "bajaj holdings": ("BAJAJHLDNG", "Bajaj Holdings & Investment"),
    "sun pharma": ("SUNPHARMA", "Sun Pharmaceutical Industries"),
    "ntpc": ("NTPC", "NTPC"),
    "ongc": ("ONGC", "Oil and Natural Gas Corporation"),
    "coal india": ("COALINDIA", "Coal India"),
    "asian paints": ("ASIANPAINT", "Asian Paints"),
    "titan": ("TITAN", "Titan Company"),
    "hcl tech": ("HCLTECH", "HCL Technologies"),
    "hcltech": ("HCLTECH", "HCL Technologies"),
    "tech mahindra": ("TECHM", "Tech Mahindra"),
    "power grid": ("POWERGRID", "Power Grid Corporation"),
    "m&m": ("M&M", "Mahindra & Mahindra"),
    "mahindra": ("M&M", "Mahindra & Mahindra"),
    "jsw steel": ("JSWSTEEL", "JSW Steel"),
    "jsw energy": ("JSWENERGY", "JSW Energy"),
    "dr reddy": ("DRREDDY", "Dr. Reddy's Laboratories"),
    "cipla": ("CIPLA", "Cipla"),
    "divis lab": ("DIVISLAB", "Divi's Laboratories"),
    "eicher motors": ("EICHERMOT", "Eicher Motors"),
    "grasim": ("GRASIM", "Grasim Industries"),
    "hero motocorp": ("HEROMOTOCO", "Hero MotoCorp"),
    "hindalco": ("HINDALCO", "Hindalco Industries"),
    "indusind bank": ("INDUSINDBK", "IndusInd Bank"),
    "britannia": ("BRITANNIA", "Britannia Industries"),
    "apollo hospitals": ("APOLLOHOSP", "Apollo Hospitals"),
    "shree cement": ("SHREECEM", "Shree Cement"),
    "ultratech": ("ULTRACEMCO", "UltraTech Cement"),
    "nestle": ("NESTLEIND", "Nestle India"),
    "bpcl": ("BPCL", "Bharat Petroleum"),
    "ioc": ("IOC", "Indian Oil Corporation"),
    "indian oil": ("IOC", "Indian Oil Corporation"),
    "hpcl": ("HINDPETRO", "Hindustan Petroleum"),
    "vedanta": ("VEDL", "Vedanta"),
    "ltimindtree": ("LTIM", "LTIMindtree"),
    "pidilite": ("PIDILITIND", "Pidilite Industries"),
    "zomato": ("ETERNAL", "Eternal (Zomato)"),
    "eternal": ("ETERNAL", "Eternal (Zomato)"),
    "paytm": ("PAYTM", "One97 Communications (Paytm)"),
    "nykaa": ("NYKAA", "FSN E-Commerce (Nykaa)"),
    "irctc": ("IRCTC", "IRCTC"),
    "dmart": ("DMART", "Avenue Supermarts (DMart)"),
    "avenue supermarts": ("DMART", "Avenue Supermarts (DMart)"),
    "yes bank": ("YESBANK", "Yes Bank"),
    "pnb": ("PNB", "Punjab National Bank"),
    "canara bank": ("CANBK", "Canara Bank"),
    "bank of baroda": ("BANKBARODA", "Bank of Baroda"),
    "idfc first": ("IDFCFIRSTB", "IDFC First Bank"),
    "federal bank": ("FEDERALBNK", "Federal Bank"),
    "au small finance": ("AUBANK", "AU Small Finance Bank"),
    "hindustan aeronautics": ("HAL", "Hindustan Aeronautics"),
    "hal": ("HAL", "Hindustan Aeronautics"),
    "bhel": ("BHEL", "Bharat Heavy Electricals"),
    "bel": ("BEL", "Bharat Electronics"),
    "mazagon dock": ("MAZDOCK", "Mazagon Dock Shipbuilders"),
    "zydus": ("ZYDUSLIFE", "Zydus Lifesciences"),
    "lupin": ("LUPIN", "Lupin"),
    "aurobindo pharma": ("AUROPHARMA", "Aurobindo Pharma"),
    "biocon": ("BIOCON", "Biocon"),
    "godrej consumer": ("GODREJCP", "Godrej Consumer Products"),
    "godrej properties": ("GODREJPROP", "Godrej Properties"),
    "dabur": ("DABUR", "Dabur India"),
    "marico": ("MARICO", "Marico"),
    "colgate": ("COLPAL", "Colgate-Palmolive India"),
    "united spirits": ("MCDOWELL-N", "United Spirits"),
    "varun beverages": ("VBL", "Varun Beverages"),
    "vodafone idea": ("IDEA", "Vodafone Idea"),
    "vi": ("IDEA", "Vodafone Idea"),
    "dlf": ("DLF", "DLF"),
    "oberoi realty": ("OBEROIRLTY", "Oberoi Realty"),
    "indigo": ("INDIGO", "InterGlobe Aviation (IndiGo)"),
    "interglobe": ("INDIGO", "InterGlobe Aviation (IndiGo)"),
    "pi industries": ("PIIND", "PI Industries"),
    "upl": ("UPL", "UPL"),
    "siemens": ("SIEMENS", "Siemens"),
    "abb india": ("ABB", "ABB India"),
    "havells": ("HAVELLS", "Havells India"),
    "voltas": ("VOLTAS", "Voltas"),
    "trent": ("TRENT", "Trent"),
    "page industries": ("PAGEIND", "Page Industries"),
    "muthoot finance": ("MUTHOOTFIN", "Muthoot Finance"),
    "chola finance": ("CHOLAFIN", "Cholamandalam Investment & Finance"),
    "shriram finance": ("SHRIRAMFIN", "Shriram Finance"),
    "lic": ("LICI", "Life Insurance Corporation of India"),
    "life insurance corporation": ("LICI", "Life Insurance Corporation of India"),
    "bosch": ("BOSCHLTD", "Bosch"),
    "cummins": ("CUMMINSIND", "Cummins India"),
    "ashok leyland": ("ASHOKLEY", "Ashok Leyland"),
    "hero moto": ("HEROMOTOCO", "Hero MotoCorp"),
    "tvs motor": ("TVSMOTOR", "TVS Motor Company"),
    "bharat forge": ("BHARATFORG", "Bharat Forge"),
    "gail": ("GAIL", "GAIL India"),
    "sail": ("SAIL", "Steel Authority of India"),
    "nmdc": ("NMDC", "NMDC"),
    "nalco": ("NATIONALUM", "National Aluminium Company"),
    "jindal steel": ("JINDALSTEL", "Jindal Steel & Power"),
    "polycab": ("POLYCAB", "Polycab India"),
    "dixon": ("DIXON", "Dixon Technologies"),
    "persistent": ("PERSISTENT", "Persistent Systems"),
    "coforge": ("COFORGE", "Coforge"),
    "mphasis": ("MPHASIS", "Mphasis"),
    "lti": ("LTIM", "LTIMindtree"),
}

# --------------------------------------------------------------------------
# In-memory storage (simple + zero-setup; swap for a DB later if you want
# persistence across restarts).
# --------------------------------------------------------------------------

_lock = threading.Lock()
_news_store: dict[str, dict] = {}     # link -> article
_analysis_cache: dict[str, dict] = {} # cache_key -> Gemini analysis result
_last_fetch_time = 0.0

_ticker_cache: dict | None = None
_ticker_cache_time = 0.0

_prediction_cache: dict | None = None
_prediction_cache_time = 0.0
PREDICTION_CACHE_SECONDS = 900  # regenerate the AI market outlook at most every 15 min

_company_overview_cache: dict[str, dict] = {}  # "symbol:language" -> {"text":, "time":}
COMPANY_OVERVIEW_TTL = 24 * 3600  # a company's overview barely changes — cache for a day

# NSE publishes a plain CSV of every listed equity (symbol + company name).
# We pull this once a day and use it to resolve search queries against the
# *entire* NSE universe (~2,000 stocks), instead of only the curated
# STOCK_SYMBOLS shortlist above (which we still check first since it's faster
# and covers common company nicknames the official list doesn't, e.g. "HDFC").
EQUITY_LIST_URL = "https://nsearchives.nseindia.com/content/equities/EQUITY_L.csv"
EQUITY_MASTER_TTL = 24 * 3600  # this list barely changes — refresh once a day
_equity_master: dict[str, str] = {}   # SYMBOL -> Company Name
_equity_master_time = 0.0


# --------------------------------------------------------------------------
# Helpers
# --------------------------------------------------------------------------

def _clean_html(raw_html: str) -> str:
    """Strip HTML tags/entities that RSS summaries often contain."""
    if not raw_html:
        return ""
    try:
        text = BeautifulSoup(raw_html, "html.parser").get_text(separator=" ")
    except Exception:
        text = re.sub(r"<[^>]+>", " ", raw_html)
    return re.sub(r"\s+", " ", text).strip()


def _parse_published(entry) -> str:
    """Return an ISO-8601 UTC timestamp string for a feed entry, best-effort."""
    for key in ("published_parsed", "updated_parsed"):
        value = entry.get(key)
        if value:
            try:
                return datetime(*value[:6], tzinfo=timezone.utc).isoformat()
            except Exception:
                pass
    return datetime.now(timezone.utc).isoformat()


def fetch_all_feeds(force: bool = False) -> None:
    """Pull all configured RSS feeds into _news_store (throttled)."""
    global _last_fetch_time
    now = time.time()
    if not force and _news_store and (now - _last_fetch_time) < FETCH_INTERVAL_SECONDS:
        return

    for source_name, feed_info in RSS_FEEDS.items():
        url = feed_info["url"]
        default_category = feed_info["category"]
        try:
            parsed = feedparser.parse(url)
            if parsed.bozo and not parsed.entries:
                print(f"[market-pulse] WARNING: could not parse feed '{source_name}': {parsed.bozo_exception}")
                continue

            for entry in parsed.entries:
                link = entry.get("link", "").strip()
                title = entry.get("title", "").strip()
                if not link or not title:
                    continue

                summary = _clean_html(entry.get("summary", "") or entry.get("description", ""))
                article_id = hashlib.md5(link.encode("utf-8")).hexdigest()

                category = default_category
                title_lower = title.lower()
                if any(kw in title_lower for kw in COMMODITY_TITLE_KEYWORDS):
                    category = "commodity"

                with _lock:
                    _news_store[link] = {
                        "id": article_id,
                        "title": title,
                        "summary": summary[:600],
                        "link": link,
                        "source": source_name,
                        "published": _parse_published(entry),
                        "category": category,
                    }
        except Exception as exc:
            print(f"[market-pulse] WARNING: failed to fetch '{source_name}': {exc}")

    # Trim history so memory doesn't grow unbounded
    with _lock:
        if len(_news_store) > MAX_STORED_ARTICLES:
            newest = sorted(_news_store.values(), key=lambda a: a["published"], reverse=True)
            newest = newest[:MAX_STORED_ARTICLES]
            _news_store.clear()
            for a in newest:
                _news_store[a["link"]] = a

    _last_fetch_time = now


def _fetch_yahoo_quote(symbol: str) -> dict | None:
    """Return {'price': float, 'prev_close': float} for a Yahoo symbol, or None on failure."""
    try:
        url = YAHOO_CHART_URL.format(symbol=symbol)
        resp = requests.get(
            url,
            headers=YAHOO_HEADERS,
            params={"range": "1d", "interval": "5m"},
            timeout=REQUEST_TIMEOUT,
        )
        resp.raise_for_status()
        meta = resp.json()["chart"]["result"][0]["meta"]
        price = meta.get("regularMarketPrice")
        prev_close = meta.get("chartPreviousClose") or meta.get("previousClose")
        if price is None or prev_close is None:
            return None
        return {"price": float(price), "prev_close": float(prev_close)}
    except Exception as exc:
        print(f"[market-pulse] WARNING: yahoo quote failed for '{symbol}': {exc}")
        return None


NSE_TIMEOUT = 5  # fail fast — NSE often blocks cloud/datacenter IPs outright rather than erroring quickly


def _get_nse_session() -> requests.Session:
    """Reuse a warmed-up NSE session (cookies) for NSE_SESSION_TTL seconds."""
    now = time.time()
    if _nse_session_cache["session"] and (now - _nse_session_cache["time"]) < NSE_SESSION_TTL:
        return _nse_session_cache["session"]
    s = requests.Session()
    s.headers.update(NSE_HEADERS)
    try:
        s.get(NSE_BASE, timeout=NSE_TIMEOUT)  # sets the cookies the API needs
    except Exception as exc:
        print(f"[market-pulse] WARNING: NSE session warm-up failed: {exc}")
    _nse_session_cache["session"] = s
    _nse_session_cache["time"] = now
    return s


def _fetch_nse_index(index_name: str) -> dict | None:
    """Official NSE index snapshot (e.g. 'NIFTY 50') straight from NSE's own API.
    Fails fast (short timeout, single retry) — a Yahoo fallback covers the rest."""
    try:
        s = _get_nse_session()
        resp = s.get(NSE_INDICES_API, timeout=NSE_TIMEOUT)
        if resp.status_code != 200:
            _nse_session_cache["session"] = None
            s = _get_nse_session()
            resp = s.get(NSE_INDICES_API, timeout=NSE_TIMEOUT)
        resp.raise_for_status()
        for row in resp.json().get("data", []):
            if row.get("index", "").strip().upper() == index_name.upper():
                price, prev_close = row.get("last"), row.get("previousClose")
                if price is None or prev_close is None:
                    return None
                return {"price": float(price), "prev_close": float(prev_close)}
        return None
    except Exception as exc:
        print(f"[market-pulse] WARNING: NSE index fetch failed for '{index_name}': {exc}")
        return None


def _fetch_nse_quote(symbol: str) -> dict | None:
    """Official NSE live quote for an equity symbol (e.g. 'TCS', 'RELIANCE').
    Fails fast (short timeout, single retry) — _fetch_yahoo_equity_quote covers the rest."""
    try:
        s = _get_nse_session()
        resp = s.get(NSE_QUOTE_API, params={"symbol": symbol}, timeout=NSE_TIMEOUT)
        if resp.status_code != 200:
            _nse_session_cache["session"] = None
            s = _get_nse_session()
            resp = s.get(NSE_QUOTE_API, params={"symbol": symbol}, timeout=NSE_TIMEOUT)
        resp.raise_for_status()
        data = resp.json()
        price_info = data.get("priceInfo", {}) or {}
        info = data.get("info", {}) or {}
        high_low = price_info.get("intraDayHighLow", {}) or {}
        price = price_info.get("lastPrice")
        if price is None:
            return None
        return {
            "symbol": symbol,
            "company_name": info.get("companyName", symbol),
            "price": price,
            "change": price_info.get("change"),
            "pct_change": price_info.get("pChange"),
            "day_high": high_low.get("max"),
            "day_low": high_low.get("min"),
            "prev_close": price_info.get("previousClose"),
        }
    except Exception as exc:
        print(f"[market-pulse] WARNING: NSE quote failed for '{symbol}': {exc}")
        return None


def _fetch_yahoo_equity_quote(nse_symbol: str, company_name: str | None = None) -> dict | None:
    """Fallback price source for an individual NSE-listed stock via Yahoo (symbol + '.NS').
    Used whenever NSE's own API is unreachable (e.g. blocked from a cloud server)."""
    q = _fetch_yahoo_quote(f"{nse_symbol}.NS")
    if not q:
        return None
    pct = _pct_change(q["price"], q["prev_close"])
    return {
        "symbol": nse_symbol,
        "company_name": company_name or nse_symbol,
        "price": round(q["price"], 2),
        "change": round(q["price"] - q["prev_close"], 2),
        "pct_change": pct,
        "day_high": None,
        "day_low": None,
        "prev_close": round(q["prev_close"], 2),
    }


# --- BSE support -----------------------------------------------------------
# BSE doesn't publish a clean bulk equity-list JSON/CSV the way NSE does, but
# its own site search widget is a plain, fast, unauthenticated GET — so we
# use that directly for both search and scrip-code lookup, and a second BSE
# endpoint for the live quote itself. This covers the ~4,000+ BSE-only
# smaller-cap stocks that never show up on NSE.
BSE_SEARCH_URL = "https://api.bseindia.com/Msource/1D/getQouteSearch.aspx"
BSE_QUOTE_URL = "https://api.bseindia.com/BseIndiaAPI/api/StockReachGraph/w"
BSE_HEADERS = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                  "(KHTML, like Gecko) Chrome/124.0 Safari/537.36",
    "Accept": "application/json, text/plain, */*",
    "Origin": "https://www.bseindia.com",
    "Referer": "https://www.bseindia.com/",
}
BSE_TIMEOUT = 4  # kept short — this sits on the interactive search path, run in parallel with Yahoo below

YAHOO_SEARCH_URL = "https://query1.finance.yahoo.com/v1/finance/search"
SEARCH_TIMEOUT = 4  # short timeout for anything the user is actively waiting on while typing

# Short-lived cache for network-augmented search results (BSE/Yahoo lookups),
# keyed by lowercase query. Avoids repeating the same slow network search
# seconds later when a user picks a suggestion right after typing it.
SEARCH_CACHE_TTL = 300
_search_cache: dict[str, tuple[float, list[dict]]] = {}


def _search_yahoo_stocks(q: str, limit: int = 8, timeout: float = SEARCH_TIMEOUT) -> list[dict]:
    """Search Yahoo Finance for NSE/BSE-listed equities matching a name/ticker.
    Yahoo indexes virtually the entire NSE+BSE universe, and — unlike NSE's or
    BSE's own sites — is reliably reachable from a cloud server. This is the
    most dependable layer when the NSE list and BSE search both come up empty
    (which happens often, since NSE/BSE frequently block cloud/datacenter IPs
    outright). Matches are tagged exchange="YAHOO:NSE"/"YAHOO:BSE" so the
    quote-fetcher knows the returned symbol already has its .NS/.BO suffix.
    Uses a short timeout (this sits on the interactive search path, not the
    12s general REQUEST_TIMEOUT used for background RSS/quote calls)."""
    try:
        resp = requests.get(
            YAHOO_SEARCH_URL,
            headers=YAHOO_HEADERS,
            params={"q": q, "quotesCount": 20, "newsCount": 0},
            timeout=SEARCH_TIMEOUT,
        )
        resp.raise_for_status()
        results = []
        for item in resp.json().get("quotes", []) or []:
            yahoo_symbol = item.get("symbol", "")
            name = item.get("longname") or item.get("shortname") or ""
            if not yahoo_symbol or not name:
                continue
            if yahoo_symbol.endswith(".NS"):
                exch = "YAHOO:NSE"
            elif yahoo_symbol.endswith(".BO"):
                exch = "YAHOO:BSE"
            else:
                continue  # not an Indian-exchange listing — skip
            results.append({"symbol": yahoo_symbol, "name": name, "exchange": exch})
            if len(results) >= limit:
                break
        return results
    except Exception as exc:
        print(f"[market-pulse] WARNING: Yahoo stock search failed for '{q}': {exc}")
        return []


def _search_bse(query: str, limit: int = 8) -> list[dict]:
    """Search BSE-listed equities by name/symbol using BSE's own live search widget."""
    try:
        resp = requests.get(
            BSE_SEARCH_URL,
            params={"Type": "EQ", "text": query, "flag": "site"},
            headers=BSE_HEADERS,
            timeout=BSE_TIMEOUT,
        )
        resp.raise_for_status()
        soup = BeautifulSoup(resp.text, "html.parser")
        results = []
        for a in soup.find_all("a"):
            href = a.get("href", "")
            m = re.search(r"/(\d+)/", href)
            name = a.get_text(strip=True)
            if m and name:
                results.append({"symbol": m.group(1), "name": name, "exchange": "BSE"})
            if len(results) >= limit:
                break
        return results
    except Exception as exc:
        print(f"[market-pulse] WARNING: BSE search failed for '{query}': {exc}")
        return []


def _fetch_bse_quote(scripcode: str, company_name: str | None = None) -> dict | None:
    """Live BSE quote by scrip code (e.g. '532540' for TCS)."""
    try:
        resp = requests.get(
            BSE_QUOTE_URL,
            params={"scripcode": scripcode, "flag": "0", "fromdate": "", "todate": "", "seriesid": ""},
            headers=BSE_HEADERS,
            timeout=BSE_TIMEOUT,
        )
        resp.raise_for_status()
        data = resp.json()
        price = data.get("CurrVal")
        if price in (None, ""):
            return None
        price = float(price)
        prev_close_raw = data.get("PrevClose")
        prev_close = float(prev_close_raw) if prev_close_raw not in (None, "") else None
        return {
            "symbol": scripcode,
            "company_name": company_name or data.get("Scripname", scripcode),
            "price": round(price, 2),
            "change": round(price - prev_close, 2) if prev_close else None,
            "pct_change": _pct_change(price, prev_close) if prev_close else None,
            "day_high": None,
            "day_low": None,
            "prev_close": round(prev_close, 2) if prev_close else None,
        }
    except Exception as exc:
        print(f"[market-pulse] WARNING: BSE quote failed for scripcode '{scripcode}': {exc}")
        return None


def _match_stock(text: str) -> tuple[str | None, str | None, str]:
    """Match free text against a stock. Checks the curated STOCK_SYMBOLS shortlist
    first (covers common nicknames like 'HDFC' -> HDFC Bank), then NSE's full
    ~2,000-stock list, then falls back to BSE (covers thousands more smaller-cap,
    BSE-only stocks). Returns (symbol_or_scripcode, company_name, exchange)."""
    q = (text or "").strip().lower()
    if not q:
        return None, None, "NSE"
    if q in STOCK_SYMBOLS:
        sym, name = STOCK_SYMBOLS[q]
        return sym, name, "NSE"
    for alias, (symbol, name) in STOCK_SYMBOLS.items():
        if alias in q or q in alias:
            return symbol, name, "NSE"
    matches = _search_equity_master(q, limit=1)
    if matches:
        return matches[0]["symbol"], matches[0]["name"], matches[0]["exchange"]
    return None, None, "NSE"


def _fetch_stock_quote(symbol: str, company_name: str, exchange: str = "NSE") -> dict | None:
    """Best-effort share quote. NSE stocks: try NSE directly, then Yahoo as a
    fallback (more reliable from a cloud server). BSE-only stocks: BSE's own
    quote API. Yahoo-sourced matches: symbol already has its .NS/.BO suffix —
    query Yahoo directly."""
    if exchange.startswith("YAHOO:"):
        q = _fetch_yahoo_quote(symbol)
        if not q:
            return None
        pct = _pct_change(q["price"], q["prev_close"])
        return {
            "symbol": symbol.split(".")[0],
            "company_name": company_name,
            "price": round(q["price"], 2),
            "change": round(q["price"] - q["prev_close"], 2),
            "pct_change": pct,
            "day_high": None,
            "day_low": None,
            "prev_close": round(q["prev_close"], 2),
        }
    if exchange == "BSE":
        quote = _fetch_bse_quote(symbol, company_name)
        if quote and quote.get("price") is not None:
            return quote
        # BSE's own API is unofficial and often blocked from cloud servers —
        # Yahoo indexes BSE scrips too via "<scripcode>.BO", so try that next
        # rather than giving up and showing "price unavailable".
        q = _fetch_yahoo_quote(f"{symbol}.BO")
        if not q:
            return None
        pct = _pct_change(q["price"], q["prev_close"])
        return {
            "symbol": symbol,
            "company_name": company_name,
            "price": round(q["price"], 2),
            "change": round(q["price"] - q["prev_close"], 2),
            "pct_change": pct,
            "day_high": None,
            "day_low": None,
            "prev_close": round(q["prev_close"], 2),
        }
    quote = _fetch_nse_quote(symbol)
    if quote and quote.get("price") is not None:
        return quote
    return _fetch_yahoo_equity_quote(symbol, company_name)


def fetch_equity_master(force: bool = False) -> None:
    """Pull NSE's official list of every listed equity (~2,000 rows: symbol +
    company name), cached for EQUITY_MASTER_TTL. This is what lets search
    cover all of NSE, not just the curated STOCK_SYMBOLS shortlist."""
    global _equity_master, _equity_master_time
    now = time.time()
    if not force and _equity_master and (now - _equity_master_time) < EQUITY_MASTER_TTL:
        return
    try:
        resp = requests.get(EQUITY_LIST_URL, headers=YAHOO_HEADERS, timeout=REQUEST_TIMEOUT)
        resp.raise_for_status()
        reader = csv.DictReader(resp.text.splitlines())
        new_master = {}
        for row in reader:
            symbol = (row.get("SYMBOL") or "").strip().upper()
            name = (row.get("NAME OF COMPANY") or "").strip()
            if symbol and name:
                new_master[symbol] = name
        if new_master:
            _equity_master = new_master
            _equity_master_time = now
            print(f"[market-pulse] loaded {len(new_master)} NSE-listed equities")
    except Exception as exc:
        print(f"[market-pulse] WARNING: failed to fetch NSE equity master list: {exc}")
        # keep whatever was cached before (even if stale) rather than losing it


def _search_equity_master(q: str, limit: int = 8, allow_network: bool = True) -> list[dict]:
    """Search for a stock, cheapest/most-reliable source first:

    Tier 0: the curated STOCK_SYMBOLS shortlist (~90 major stocks) — zero
    network calls, always correct, so these never break no matter what NSE/
    BSE/Yahoo are doing.
    Tier 1: NSE's ~2,000-stock list (in-memory once loaded — instant).
    Tier 2 (allow_network=True only): BSE search + Yahoo search, run in
    parallel, for anything tiers 0-1 didn't cover.
    Tier 2-fast (allow_network=False only): a single quick Yahoo-only pass
    (short timeout) if we're still short — covers the live autocomplete
    dropdown without waiting on BSE's slower scrape, and without depending
    on NSE's list having loaded (it's blocked from many cloud IPs)."""
    fetch_equity_master()
    q_upper = q.strip().upper()
    q_lower = q.strip().lower()
    if not q_upper:
        return []

    combined: list[dict] = []
    seen_symbols = set()

    def _add(entry):
        key = entry["symbol"].upper()
        if key not in seen_symbols:
            combined.append(entry)
            seen_symbols.add(key)

    # Tier 0 — curated shortlist, exact alias match first, then partial.
    exact0, partial0 = [], []
    for alias, (symbol, name) in STOCK_SYMBOLS.items():
        entry = {"symbol": symbol, "name": name, "exchange": "NSE"}
        if alias == q_lower:
            exact0.append(entry)
        elif alias.startswith(q_lower) or q_lower in alias:
            partial0.append(entry)
    for entry in exact0 + partial0:
        _add(entry)

    # Tier 1 — NSE's full list, if it loaded.
    exact1, starts1, contains1 = [], [], []
    for symbol, name in _equity_master.items():
        name_upper = name.upper()
        entry = {"symbol": symbol, "name": name, "exchange": "NSE"}
        if symbol == q_upper:
            exact1.append(entry)
        elif symbol.startswith(q_upper) or name_upper.startswith(q_upper):
            starts1.append(entry)
        elif q_upper in symbol or q_upper in name_upper:
            contains1.append(entry)
    for entry in exact1 + starts1 + contains1:
        if len(combined) >= limit:
            break
        _add(entry)

    if len(combined) >= limit:
        return combined[:limit]

    if not allow_network:
        # Tier 2-fast: one quick Yahoo pass so the live dropdown still finds
        # stocks outside the curated shortlist + NSE list, without the
        # slower BSE scrape and without ever blocking on NSE being reachable.
        for entry in _search_yahoo_stocks(q, limit - len(combined)):
            _add(entry)
        return combined[:limit]

    cache_key = f"{q_upper}:{limit}"
    cached = _search_cache.get(cache_key)
    if cached and (time.time() - cached[0]) < SEARCH_CACHE_TTL:
        seen_names = {r["name"].lower() for r in combined}
        for r in cached[1]:
            if len(combined) >= limit:
                break
            if r["name"].lower() not in seen_names:
                combined.append(r)
                seen_names.add(r["name"].lower())
        return combined[:limit]

    # Run the BSE scrape and the Yahoo search AT THE SAME TIME instead of
    # sequentially — this alone roughly halves worst-case latency (was
    # BSE_TIMEOUT + a 12s Yahoo timeout back to back; now max(~4s, ~4s)).
    need = limit - len(combined)
    with ThreadPoolExecutor(max_workers=2) as pool:
        bse_future = pool.submit(_search_bse, q, need)
        yahoo_future = pool.submit(_search_yahoo_stocks, q, need)
        bse_results = bse_future.result()
        yahoo_results = yahoo_future.result()

    network_results = []
    seen_names = {r["name"].lower() for r in combined}
    for r in bse_results + yahoo_results:
        if r["name"].lower() not in seen_names:
            network_results.append(r)
            seen_names.add(r["name"].lower())

    _search_cache[cache_key] = (time.time(), network_results)
    combined.extend(network_results)
    return combined[:limit]




def _pct_change(price: float, prev_close: float) -> float:
    if not prev_close:
        return 0.0
    return round((price - prev_close) / prev_close * 100, 2)


def _direction(pct: float) -> str:
    if pct > 0.01:
        return "UP"
    if pct < -0.01:
        return "DOWN"
    return "FLAT"


def build_ticker() -> dict:
    """Fetch Sensex/Nifty/USD-INR/Crude, cached for TICKER_CACHE_SECONDS."""
    global _ticker_cache, _ticker_cache_time
    now = time.time()
    if _ticker_cache and (now - _ticker_cache_time) < TICKER_CACHE_SECONDS:
        return _ticker_cache

    quotes = {name: _fetch_yahoo_quote(sym) for name, sym in TICKER_SYMBOLS.items() if name != "nifty"}
    # Nifty: prefer NSE's own official index feed (most accurate); Yahoo as fallback only.
    quotes["nifty"] = _fetch_nse_index("NIFTY 50") or _fetch_yahoo_quote(TICKER_SYMBOLS["nifty"])
    result = {}

    for name in ("sensex", "nifty", "crude"):
        q = quotes.get(name)
        if q:
            pct = _pct_change(q["price"], q["prev_close"])
            result[name] = {"value": round(q["price"], 2), "change_pct": pct, "direction": _direction(pct)}
        else:
            result[name] = {"value": None, "change_pct": None, "direction": "FLAT"}

    usdinr_q = quotes.get("usdinr")
    if usdinr_q:
        pct = _pct_change(usdinr_q["price"], usdinr_q["prev_close"])
        result["usdinr"] = {"value": round(usdinr_q["price"], 2), "change_pct": pct, "direction": _direction(pct)}
    else:
        result["usdinr"] = {"value": None, "change_pct": None, "direction": "FLAT"}

    result["updated_at"] = datetime.now(timezone.utc).isoformat()
    _ticker_cache = result
    _ticker_cache_time = now
    return result


def call_gemini_for_analysis(title: str, summary: str, language: str) -> dict:
    """Ask Gemini to turn a headline into a structured, plain-language impact card."""
    if not GEMINI_API_KEY:
        raise RuntimeError("GEMINI_API_KEY is not set on the server")

    if language == "hinglish":
        lang_instruction = (
            "Write the 'simplified_summary' field in simple Hinglish "
            "(a natural mix of Hindi and English, written in Roman/English script), "
            "as if explaining to a friend who is new to investing."
        )
    else:
        lang_instruction = (
            "Write the 'simplified_summary' field in simple, plain, beginner-friendly English, "
            "avoiding financial jargon, as if explaining to someone new to investing."
        )

    prompt = f"""You are a cautious financial-news explainer for retail investors in the Indian stock market.

Read the news item below and respond with ONLY a single valid JSON object (no markdown
fences, no extra commentary) with EXACTLY this shape:

{{
  "simplified_summary": "2-4 short sentences in plain language explaining what happened and why it matters",
  "sentiment": "Bullish" | "Bearish" | "Neutral",
  "sectors": [{{"name": "sector name", "impact": "UP" | "DOWN" | "NEUTRAL"}}],
  "stocks": [{{"ticker": "NSE/BSE ticker or company short name", "name": "full company name", "impact": "UP" | "DOWN" | "NEUTRAL", "estimated_change": "e.g. +2% to +3.5%"}}],
  "disclaimer": "one short sentence noting these are illustrative, non-advisory estimates"
}}

Rules:
- Only include stocks/sectors that are plausibly, directly relevant to this specific news item. If none are identifiable, return empty arrays for "sectors" and "stocks" rather than guessing randomly.
- "estimated_change" must be a short illustrative RANGE (e.g. "-1% to -2%"), clearly not a guarantee.
- Keep the whole response concise.
- {lang_instruction}

News headline: {title}
News summary/context: {summary if summary else "(no additional summary provided)"}
"""

    payload = {
        "contents": [{"parts": [{"text": prompt}]}],
        "generationConfig": {
            "response_mime_type": "application/json",
        },
    }
    headers = {
        "Content-Type": "application/json",
        "x-goog-api-key": GEMINI_API_KEY,
    }

    resp = requests.post(GEMINI_URL, headers=headers, data=json.dumps(payload), timeout=30)
    resp.raise_for_status()
    body = resp.json()

    try:
        raw_text = body["candidates"][0]["content"]["parts"][0]["text"]
    except (KeyError, IndexError, TypeError) as exc:
        raise RuntimeError(f"Unexpected Gemini response shape: {body}") from exc

    raw_text = raw_text.strip()
    # Safety net in case the model wraps the JSON in a markdown fence anyway
    raw_text = re.sub(r"^```(?:json)?\s*", "", raw_text)
    raw_text = re.sub(r"\s*```$", "", raw_text)

    parsed = json.loads(raw_text)
    parsed.setdefault("simplified_summary", "")
    parsed.setdefault("sentiment", "Neutral")
    parsed.setdefault("sectors", [])
    parsed.setdefault("stocks", [])
    parsed.setdefault("disclaimer", "Estimates are illustrative only and not investment advice.")
    return parsed


def call_gemini_for_prediction(headlines: list, language: str) -> dict:
    """Ask Gemini for a short-term overall market outlook based on recent headlines."""
    if not GEMINI_API_KEY:
        raise RuntimeError("GEMINI_API_KEY is not set on the server")

    lang_instruction = (
        "Write every text field in simple Hinglish (Hindi+English mix, Roman script)."
        if language == "hinglish"
        else "Write every text field in simple, plain, beginner-friendly English."
    )
    headline_block = "\n".join(f"- {h}" for h in headlines[:12]) or "(no recent headlines available)"

    prompt = f"""You are a cautious market-outlook assistant for Indian retail investors.

Based ONLY on the recent headlines below, give a short-term (next few trading sessions) view.
Respond with ONLY a single valid JSON object (no markdown fences) with EXACTLY this shape:

{{
  "overall_outlook": "1-3 sentences on likely Sensex/Nifty direction and why",
  "sentiment": "Bullish" | "Bearish" | "Neutral",
  "sectors_up": [{{"name": "sector", "reason": "short reason"}}],
  "sectors_down": [{{"name": "sector", "reason": "short reason"}}],
  "key_risks": ["short risk 1", "short risk 2"],
  "disclaimer": "one short sentence noting this is an illustrative, non-advisory view"
}}

Rules:
- Base this only on the headlines given; do not invent unrelated events.
- Keep each field concise.
- {lang_instruction}

Recent headlines:
{headline_block}
"""

    payload = {
        "contents": [{"parts": [{"text": prompt}]}],
        "generationConfig": {"response_mime_type": "application/json"},
    }
    headers = {"Content-Type": "application/json", "x-goog-api-key": GEMINI_API_KEY}
    resp = requests.post(GEMINI_URL, headers=headers, data=json.dumps(payload), timeout=30)
    resp.raise_for_status()
    body = resp.json()

    try:
        raw_text = body["candidates"][0]["content"]["parts"][0]["text"]
    except (KeyError, IndexError, TypeError) as exc:
        raise RuntimeError(f"Unexpected Gemini response shape: {body}") from exc

    raw_text = re.sub(r"^```(?:json)?\s*", "", raw_text.strip())
    raw_text = re.sub(r"\s*```$", "", raw_text)
    parsed = json.loads(raw_text)
    parsed.setdefault("overall_outlook", "")
    parsed.setdefault("sentiment", "Neutral")
    parsed.setdefault("sectors_up", [])
    parsed.setdefault("sectors_down", [])
    parsed.setdefault("key_risks", [])
    parsed.setdefault("disclaimer", "Illustrative outlook only — not investment advice.")
    return parsed


def call_gemini_chat(history: list, message: str, language: str, context_text: str = "") -> str:
    """Send a chat turn (with prior history) to Gemini and return the reply text."""
    if not GEMINI_API_KEY:
        raise RuntimeError("GEMINI_API_KEY is not set on the server")

    lang_instruction = (
        "Reply in simple Hinglish (Hindi+English mix, Roman script)."
        if language == "hinglish"
        else "Reply in simple, plain English."
    )

    if context_text:
        data_note = (
            "You HAVE been given live market data below — it is real and current, and you have "
            "full permission to state it directly and confidently. Do not say you lack access to "
            "real-time data when the figure you need is already listed here.\n\n"
            f"LIVE DATA:\n{context_text}"
        )
    else:
        data_note = (
            "No specific live price was looked up for this message. If the user asks for a live "
            "price you don't have, say you don't have that particular figure right now, but still "
            "answer anything else about the company/sector/market from general knowledge."
        )

    system_text = (
        "You are the Market Pulse assistant — a friendly, plain-language guide to the Indian "
        "stock market for retail investors. Keep answers concise (short paragraphs, a few "
        "sentences) and avoid heavy jargon. Format for readability: use **bold** around key "
        "numbers, stock names, and important terms, and use short '- ' bullet points when "
        "listing more than two items. Don't overdo it — bold only what's genuinely important. "
        "You are not a licensed financial advisor; make clear that anything resembling a "
        "prediction or recommendation is illustrative only, not investment advice.\n\n"
        + data_note + "\n\n" + lang_instruction
    )

    contents = []
    for turn in history[-10:]:
        role = "user" if turn.get("role") == "user" else "model"
        text = (turn.get("content") or "").strip()
        if text:
            contents.append({"role": role, "parts": [{"text": text}]})
    contents.append({"role": "user", "parts": [{"text": message}]})

    payload = {
        "system_instruction": {"parts": [{"text": system_text}]},
        "contents": contents,
    }
    headers = {"Content-Type": "application/json", "x-goog-api-key": GEMINI_API_KEY}
    resp = requests.post(GEMINI_URL, headers=headers, data=json.dumps(payload), timeout=30)
    resp.raise_for_status()
    body = resp.json()
    try:
        return body["candidates"][0]["content"]["parts"][0]["text"].strip()
    except (KeyError, IndexError, TypeError) as exc:
        raise RuntimeError(f"Unexpected Gemini response shape: {body}") from exc


def call_gemini_company_overview(symbol: str, name: str, language: str) -> str:
    """Short, factual, plain-language overview of a company for someone who's never heard of it."""
    if not GEMINI_API_KEY:
        raise RuntimeError("GEMINI_API_KEY is not set on the server")

    lang_instruction = (
        "Write in simple Hinglish (Hindi+English mix, Roman script)."
        if language == "hinglish" else "Write in simple, plain English."
    )
    prompt = (
        f"Give a short, factual overview of the Indian company '{name}' (NSE symbol: {symbol}) "
        "for a retail investor who has never heard of it. Cover what the company does, its "
        "sector/industry, and 1-2 notable facts (e.g. market position, promoter group) only if "
        "you're reasonably confident of them. Keep it to 3-5 sentences, plain language, no bullet "
        "points, no markdown. If you're not confident about a specific figure (like exact revenue "
        "or market cap), speak in general terms instead of inventing one. " + lang_instruction
    )
    payload = {"contents": [{"parts": [{"text": prompt}]}]}
    headers = {"Content-Type": "application/json", "x-goog-api-key": GEMINI_API_KEY}
    resp = requests.post(GEMINI_URL, headers=headers, data=json.dumps(payload), timeout=30)
    resp.raise_for_status()
    body = resp.json()
    try:
        return body["candidates"][0]["content"]["parts"][0]["text"].strip()
    except (KeyError, IndexError, TypeError) as exc:
        raise RuntimeError(f"Unexpected Gemini response shape: {body}") from exc


# --------------------------------------------------------------------------
# Upcoming market-moving events
# --------------------------------------------------------------------------
# NOTE: These are illustrative placeholders. RBI / Fed / earnings calendars
# change every year — update this list periodically (or replace it with a
# call to an events API) with the latest confirmed dates from:
#   RBI:  https://www.rbi.org.in
#   Fed:  https://www.federalreserve.gov/monetarypolicy/fomccalendars.htm
#   NSE:  https://www.nseindia.com
EVENTS = [
    {
        "category": "RBI Policy",
        "name": "RBI Monetary Policy Committee (MPC) Meeting",
        "note": "Repo rate decision — check rbi.org.in for the confirmed date each cycle.",
    },
    {
        "category": "US Fed",
        "name": "US Federal Reserve FOMC Meeting",
        "note": "Fed rate decision — affects FII flows into Indian equities.",
    },
    {
        "category": "Earnings",
        "name": "Q-Results Season (Nifty 50 companies)",
        "note": "Quarterly results season — update tickers/dates as each quarter approaches.",
    },
    {
        "category": "Budget",
        "name": "Union Budget",
        "note": "Announced 1 Feb each year by the Finance Ministry.",
    },
    {
        "category": "Inflation Data",
        "name": "India CPI / WPI Release",
        "note": "Monthly inflation print — moves rate-sensitive sectors.",
    },
]


# --------------------------------------------------------------------------
# Routes — frontend
# --------------------------------------------------------------------------

def _client_ip() -> str:
    xff = request.headers.get("X-Forwarded-For", "")
    if xff:
        return xff.split(",")[0].strip()
    return request.remote_addr or "unknown"


def _record_visit() -> None:
    """Log a page visit for the admin analytics view. Wrapped defensively —
    analytics must never be able to break an actual page load."""
    try:
        now = datetime.now(timezone.utc)
        ip_hash = hashlib.md5(_client_ip().encode("utf-8")).hexdigest()[:10]
        with _visits_lock:
            _visits.append({"ts": now.isoformat(), "ip_hash": ip_hash})
            if len(_visits) > MAX_STORED_VISITS:
                del _visits[: len(_visits) - MAX_STORED_VISITS]
    except Exception:
        pass


@app.route("/")
def serve_index():
    _record_visit()
    return send_from_directory(BASE_DIR, "index.html")


# --------------------------------------------------------------------------
# Routes — API
# --------------------------------------------------------------------------

@app.route("/api/health")
def health():
    return jsonify({"status": "ok", "gemini_configured": bool(GEMINI_API_KEY), "model": GEMINI_MODEL})


@app.route("/api/news")
def api_news():
    """
    Query params:
      q        - free-text search across title/summary/source/ticker-like words
      days     - only return articles from the last N days (defaults to all stored)
      category - "stock" or "commodity": only articles tagged with that category
                 (tagged by feed source + title keywords at fetch time — see
                 RSS_FEEDS/COMMODITY_TITLE_KEYWORDS — far more precise than a
                 free-text keyword search, which is why the Stock/Commodity
                 News pages use this instead of `q`)
    """
    fetch_all_feeds()

    q = request.args.get("q", "").strip().lower()
    days = request.args.get("days", type=int)
    category = request.args.get("category", "").strip().lower()

    with _lock:
        articles = list(_news_store.values())

    if category in ("stock", "commodity"):
        articles = [a for a in articles if a.get("category") == category]

    if q:
        # Multi-word queries (e.g. a broad category search like "gold silver
        # crude oil commodity") match if ANY keyword is present — requiring
        # the whole phrase verbatim would almost never match a real headline.
        # Short/common words are dropped so they don't drown results in noise.
        STOPWORDS = {"and", "the", "of", "in", "on", "for", "to", "a", "an", "or"}
        keywords = [w for w in q.split() if len(w) >= 3 and w not in STOPWORDS]
        if not keywords:
            keywords = [q]
        articles = [
            a for a in articles
            if any(
                kw in a["title"].lower() or kw in a["summary"].lower() or kw in a["source"].lower()
                for kw in keywords
            )
        ]

    if days:
        cutoff = datetime.now(timezone.utc) - timedelta(days=days)

        def _within(a):
            try:
                return datetime.fromisoformat(a["published"]) >= cutoff
            except Exception:
                return True

        articles = [a for a in articles if _within(a)]

    articles.sort(key=lambda a: a["published"], reverse=True)
    return jsonify({"count": len(articles), "articles": articles})


@app.route("/api/analyze", methods=["POST"])
def api_analyze():
    data = request.get_json(force=True, silent=True) or {}
    title = (data.get("title") or "").strip()
    summary = (data.get("summary") or "").strip()
    link = (data.get("link") or "").strip()
    language = (data.get("language") or "english").strip().lower()

    if not title:
        return jsonify({"error": "'title' is required"}), 400

    cache_key = hashlib.md5(f"{link}|{title}|{language}".encode("utf-8")).hexdigest()
    with _lock:
        cached = _analysis_cache.get(cache_key)
    if cached:
        return jsonify(cached)

    try:
        analysis = call_gemini_for_analysis(title, summary, language)
    except requests.HTTPError as exc:
        return jsonify({"error": f"Gemini API error: {exc.response.status_code} {exc.response.text[:300]}"}), 502
    except Exception as exc:
        return jsonify({"error": f"AI analysis failed: {exc}"}), 502

    with _lock:
        _analysis_cache[cache_key] = analysis
    return jsonify(analysis)


@app.route("/api/events")
def api_events():
    return jsonify({"events": EVENTS})


@app.route("/api/ticker")
def api_ticker():
    """Live-ish Sensex/Nifty/USD-INR/Crude snapshot (best-effort, cached)."""
    return jsonify(build_ticker())


@app.route("/api/prediction")
def api_prediction():
    """AI-generated short-term market outlook based on the most recent headlines."""
    global _prediction_cache, _prediction_cache_time
    language = (request.args.get("language") or "english").strip().lower()

    fetch_all_feeds()
    with _lock:
        articles = sorted(_news_store.values(), key=lambda a: a["published"], reverse=True)
    headlines = [a["title"] for a in articles[:12]]

    cache_key = f"{language}:{'|'.join(headlines)}"
    now = time.time()
    if (
        _prediction_cache
        and _prediction_cache.get("_cache_key") == cache_key
        and (now - _prediction_cache_time) < PREDICTION_CACHE_SECONDS
    ):
        return jsonify({k: v for k, v in _prediction_cache.items() if k != "_cache_key"})

    try:
        prediction = call_gemini_for_prediction(headlines, language)
    except requests.HTTPError as exc:
        return jsonify({"error": f"Gemini API error: {exc.response.status_code} {exc.response.text[:300]}"}), 502
    except Exception as exc:
        return jsonify({"error": f"AI prediction failed: {exc}"}), 502

    prediction["_cache_key"] = cache_key
    _prediction_cache = prediction
    _prediction_cache_time = now
    return jsonify({k: v for k, v in prediction.items() if k != "_cache_key"})


@app.route("/api/stock/overview")
def api_stock_overview():
    """AI-generated plain-language 'about this company' blurb, cached per symbol+language."""
    symbol = (request.args.get("symbol") or "").strip().upper()
    name = (request.args.get("name") or symbol).strip()
    language = (request.args.get("language") or "english").strip().lower()
    if not symbol:
        return jsonify({"error": "'symbol' query param is required"}), 400

    cache_key = f"{symbol}:{language}"
    now = time.time()
    cached = _company_overview_cache.get(cache_key)
    if cached and (now - cached["time"]) < COMPANY_OVERVIEW_TTL:
        return jsonify({"overview": cached["text"]})

    try:
        text = call_gemini_company_overview(symbol, name, language)
    except requests.HTTPError as exc:
        return jsonify({"error": f"Gemini API error: {exc.response.status_code} {exc.response.text[:300]}"}), 502
    except Exception as exc:
        return jsonify({"error": f"Overview failed: {exc}"}), 502

    _company_overview_cache[cache_key] = {"text": text, "time": now}
    return jsonify({"overview": text})


@app.route("/api/stocks/search")
def api_stocks_search():
    """Autocomplete: instant, in-memory NSE lookup only (no BSE/Yahoo network
    calls — this fires on every keystroke, so it must stay fast). BSE-only
    stocks still resolve fine when the user actually searches/selects one,
    via _match_stock()'s network-augmented lookup used by /api/stock."""
    q = (request.args.get("q") or "").strip()
    if len(q) < 2:
        return jsonify({"results": []})
    raw = _search_equity_master(q, limit=10, allow_network=False)
    cleaned = [
        {
            "symbol": r["symbol"].split(".")[0],
            "name": r["name"],
            "exchange": r["exchange"].replace("YAHOO:", ""),
        }
        for r in raw
    ]
    return jsonify({"results": cleaned})


@app.route("/api/stock")
def api_stock():
    """
    Look up a share by name/ticker across NSE + BSE and return its live quote
    (NSE/BSE direct, Yahoo as fallback for NSE-listed stocks) plus recent
    related headlines.
    Query params: q - stock name or keyword (e.g. "tata motors", "hdfc")
    """
    q = (request.args.get("q") or "").strip()
    if not q:
        return jsonify({"error": "'q' query param is required"}), 400

    matched_symbol, matched_name, matched_exchange = _match_stock(q)
    if not matched_symbol:
        return jsonify({"matched": False, "quote": None, "news": []})

    quote = _fetch_stock_quote(matched_symbol, matched_name, matched_exchange)
    display_exchange = matched_exchange.replace("YAHOO:", "")

    fetch_all_feeds()
    with _lock:
        articles = list(_news_store.values())
    needle = matched_name.lower().split()[0]
    related = [
        a for a in articles
        if matched_name.lower() in a["title"].lower() or needle in a["title"].lower()
    ]
    related.sort(key=lambda a: a["published"], reverse=True)

    return jsonify({
        "matched": True,
        "symbol": quote["symbol"] if quote else matched_symbol.split(".")[0],
        "company_name": matched_name,
        "exchange": display_exchange,
        "quote": quote,
        "news": related[:25],
    })


@app.route("/api/chat", methods=["POST"])
def api_chat():
    """
    Simple stateless chatbot — the client sends the full history each turn.
    Before calling Gemini, we look for a stock mention in the message and, if
    found, fetch its real quote — plus the latest Sensex/Nifty snapshot — and
    hand that to the model as live context so it can answer directly instead
    of saying it has no access to real-time data.
    """
    data = request.get_json(force=True, silent=True) or {}
    message = (data.get("message") or "").strip()
    history = data.get("history") or []
    language = (data.get("language") or "english").strip().lower()

    if not message:
        return jsonify({"error": "'message' is required"}), 400
    if not isinstance(history, list):
        history = []

    context_lines = []
    symbol, name, exchange = _match_stock(message)
    if symbol:
        quote = _fetch_stock_quote(symbol, name, exchange)
        if quote and quote.get("price") is not None:
            context_lines.append(
                f"{name} ({symbol}, {exchange}): last price ₹{quote['price']}, "
                f"change {quote.get('change')} ({quote.get('pct_change')}%), "
                f"previous close ₹{quote.get('prev_close')}."
            )
    try:
        ticker = build_ticker()
        if ticker.get("sensex", {}).get("value") is not None:
            context_lines.append(f"Sensex: {ticker['sensex']['value']} ({ticker['sensex']['direction']}).")
        if ticker.get("nifty", {}).get("value") is not None:
            context_lines.append(f"Nifty 50: {ticker['nifty']['value']} ({ticker['nifty']['direction']}).")
    except Exception:
        pass
    context_text = "\n".join(context_lines)

    try:
        reply = call_gemini_chat(history, message, language, context_text)
    except requests.HTTPError as exc:
        return jsonify({"error": f"Gemini API error: {exc.response.status_code} {exc.response.text[:300]}"}), 502
    except Exception as exc:
        return jsonify({"error": f"Chat failed: {exc}"}), 502

    return jsonify({"reply": reply})


# --------------------------------------------------------------------------
# Routes — admin / visitor analytics
# --------------------------------------------------------------------------

@app.route("/api/analytics")
def api_analytics():
    """Visit counts + a daily/hourly time series, for the /admin dashboard.
    Protected by a simple ?key= check against ADMIN_KEY (set via Render env
    vars) — not bulletproof security, but keeps random visitors from finding
    it by accident."""
    if request.args.get("key", "") != ADMIN_KEY:
        return jsonify({"error": "unauthorized"}), 401

    with _visits_lock:
        visits = list(_visits)

    total = len(visits)
    unique_visitors = len({v["ip_hash"] for v in visits})

    now = datetime.now(timezone.utc)
    today_str = now.strftime("%Y-%m-%d")

    daily_counts: dict[str, int] = {}
    for i in range(13, -1, -1):
        day = (now - timedelta(days=i)).strftime("%Y-%m-%d")
        daily_counts[day] = 0
    for v in visits:
        day = v["ts"][:10]
        if day in daily_counts:
            daily_counts[day] += 1

    hourly_counts: dict[str, int] = {f"{h:02d}": 0 for h in range(24)}
    for v in visits:
        if v["ts"][:10] == today_str:
            try:
                hour = datetime.fromisoformat(v["ts"]).strftime("%H")
                hourly_counts[hour] += 1
            except Exception:
                pass

    return jsonify({
        "total_visits": total,
        "unique_visitors": unique_visitors,
        "today_visits": daily_counts.get(today_str, 0),
        "daily": [{"date": d, "count": c} for d, c in daily_counts.items()],
        "hourly_today": [{"hour": h, "count": c} for h, c in hourly_counts.items()],
    })


ADMIN_PAGE_HTML = """<!DOCTYPE html>
<html><head>
<meta charset="UTF-8"/>
<meta name="viewport" content="width=device-width, initial-scale=1.0"/>
<title>SignalX — Visitor Analytics</title>
<style>
  body{ margin:0; font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',sans-serif; background:#0f1117; color:#e8eaf0; padding:24px; }
  h1{ font-size:20px; margin-bottom:4px; }
  .sub{ color:#8890a0; font-size:13px; margin-bottom:24px; }
  .stat-row{ display:flex; gap:12px; flex-wrap:wrap; margin-bottom:28px; }
  .stat-card{ background:#171a24; border:1px solid #262b3a; border-radius:12px; padding:16px 20px; flex:1; min-width:140px; }
  .stat-num{ font-size:28px; font-weight:700; }
  .stat-label{ font-size:12px; color:#8890a0; margin-top:4px; }
  .chart-card{ background:#171a24; border:1px solid #262b3a; border-radius:12px; padding:20px; margin-bottom:20px; }
  .chart-title{ font-size:14px; font-weight:600; margin-bottom:16px; }
  .bar{ fill:#14b8a6; }
  .bar:hover{ fill:#f59e0b; }
  .axis-label{ fill:#8890a0; font-size:9px; }
  .refresh-btn{ background:#14b8a6; color:#0f1117; border:none; border-radius:8px; padding:8px 16px; font-size:13px; font-weight:600; cursor:pointer; }
  .locked{ text-align:center; margin-top:80px; }
</style>
</head>
<body>
  <h1>📊 SignalX Visitor Analytics</h1>
  <div class="sub">Live, in-memory stats — resets on server restart. <button class="refresh-btn" onclick="load()">↻ Refresh</button></div>

  <div class="stat-row" id="statRow"></div>

  <div class="chart-card">
    <div class="chart-title">Visits — last 14 days</div>
    <svg id="dailyChart" width="100%" height="200" viewBox="0 0 700 200"></svg>
  </div>

  <div class="chart-card">
    <div class="chart-title">Visits by hour — today</div>
    <svg id="hourlyChart" width="100%" height="180" viewBox="0 0 700 180"></svg>
  </div>

<script>
const KEY = new URLSearchParams(window.location.search).get("key") || "";

function drawBarChart(svgEl, data, labelKey, valueKey, height) {
  const w = 700, h = height, padL = 30, padB = 24, padT = 10;
  const max = Math.max(1, ...data.map(d => d[valueKey]));
  const barW = (w - padL - 10) / data.length;
  let svg = "";
  data.forEach((d, i) => {
    const barH = ((h - padB - padT) * d[valueKey]) / max;
    const x = padL + i * barW + 2;
    const y = h - padB - barH;
    svg += '<rect class="bar" x="' + x + '" y="' + y + '" width="' + (barW - 4) + '" height="' + barH + '" rx="2"><title>' + d[labelKey] + ": " + d[valueKey] + '</title></rect>';
    if (i % Math.max(1, Math.ceil(data.length / 14)) === 0) {
      svg += '<text class="axis-label" x="' + x + '" y="' + (h - 6) + '">' + d[labelKey].slice(-5) + '</text>';
    }
  });
  svg += '<line x1="' + padL + '" y1="' + (h - padB) + '" x2="' + w + '" y2="' + (h - padB) + '" stroke="#262b3a"/>';
  svgEl.innerHTML = svg;
}

async function load() {
  const res = await fetch("/api/analytics?key=" + encodeURIComponent(KEY));
  if (!res.ok) {
    document.body.innerHTML = '<div class="locked"><h2>🔒 Unauthorized</h2><p style="color:#8890a0;">Add <code>?key=YOUR_ADMIN_KEY</code> to the URL.</p></div>';
    return;
  }
  const data = await res.json();

  document.getElementById("statRow").innerHTML =
    '<div class="stat-card"><div class="stat-num">' + data.total_visits + '</div><div class="stat-label">Total visits (since last restart)</div></div>' +
    '<div class="stat-card"><div class="stat-num">' + data.unique_visitors + '</div><div class="stat-label">Unique visitors (approx)</div></div>' +
    '<div class="stat-card"><div class="stat-num">' + data.today_visits + '</div><div class="stat-label">Visits today</div></div>';

  drawBarChart(document.getElementById("dailyChart"), data.daily, "date", "count", 200);
  drawBarChart(document.getElementById("hourlyChart"), data.hourly_today.map(h => ({ hour: h.hour + ":00", count: h.count })), "hour", "count", 180);
}
load();
setInterval(load, 30000);
</script>
</body>
</html>"""


@app.route("/admin")
def admin_page():
    """Simple visitor-analytics dashboard. Visit /admin?key=YOUR_ADMIN_KEY
    (set ADMIN_KEY in Render's environment variables — defaults to
    'atharv2026', please change it!)."""
    if request.args.get("key", "") != ADMIN_KEY:
        return (
            "<div style='font-family:sans-serif;text-align:center;margin-top:80px;'>"
            "<h2>🔒 Unauthorized</h2><p style='color:#888;'>Add <code>?key=YOUR_ADMIN_KEY</code> to the URL.</p></div>"
        ), 401
    return ADMIN_PAGE_HTML


# --------------------------------------------------------------------------
# Entrypoint
# --------------------------------------------------------------------------

if __name__ == "__main__":
    port = int(os.environ.get("PORT", 5000))
    app.run(host="0.0.0.0", port=port, debug=False)
