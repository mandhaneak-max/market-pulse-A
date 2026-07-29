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

# Free, publicly-available Indian financial news RSS feeds.
# If any one of these ever changes its URL, the app keeps working with the rest
# (each feed is fetched in its own try/except block).
RSS_FEEDS = {
    "Moneycontrol": "https://www.moneycontrol.com/rss/business.xml",
    "Moneycontrol Markets": "https://www.moneycontrol.com/rss/marketreports.xml",
    "Economic Times": "https://economictimes.indiatimes.com/markets/rssfeeds/1977021501.cms",
    "Livemint": "https://www.livemint.com/rss/markets",
    "Business Standard": "https://www.business-standard.com/rss/markets-106.rss",
    "Financial Express": "https://www.financialexpress.com/market/feed/",
    "CNBC-TV18": "https://www.cnbctv18.com/commonfeeds/v1/cne/rss/market.xml",
}

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
    "gold": "GC=F",     # USD per troy ounce — converted to INR/gram below
    "silver": "SI=F",   # USD per troy ounce — converted to INR/10g below
}
TICKER_CACHE_SECONDS = 60
TROY_OUNCE_IN_GRAMS = 31.1034768

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
    "hdfc bank": ("HDFCBANK", "HDFC Bank"),
    "hdfc": ("HDFCBANK", "HDFC Bank"),
    "infosys": ("INFY", "Infosys"),
    "sbi": ("SBIN", "State Bank of India"),
    "state bank of india": ("SBIN", "State Bank of India"),
    "maruti": ("MARUTI", "Maruti Suzuki"),
    "maruti suzuki": ("MARUTI", "Maruti Suzuki"),
    "adani enterprises": ("ADANIENT", "Adani Enterprises"),
    "adani": ("ADANIENT", "Adani Enterprises"),
    "icici bank": ("ICICIBANK", "ICICI Bank"),
    "icici": ("ICICIBANK", "ICICI Bank"),
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
    "bajaj finance": ("BAJFINANCE", "Bajaj Finance"),
    "sun pharma": ("SUNPHARMA", "Sun Pharmaceutical Industries"),
    "ntpc": ("NTPC", "NTPC"),
    "ongc": ("ONGC", "Oil and Natural Gas Corporation"),
    "coal india": ("COALINDIA", "Coal India"),
    "asian paints": ("ASIANPAINT", "Asian Paints"),
    "titan": ("TITAN", "Titan Company"),
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

    for source_name, url in RSS_FEEDS.items():
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

                with _lock:
                    _news_store[link] = {
                        "id": article_id,
                        "title": title,
                        "summary": summary[:600],
                        "link": link,
                        "source": source_name,
                        "published": _parse_published(entry),
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
BSE_TIMEOUT = 5


YAHOO_SEARCH_URL = "https://query1.finance.yahoo.com/v1/finance/search"


def _search_yahoo_stocks(q: str, limit: int = 8) -> list[dict]:
    """Search Yahoo Finance for NSE/BSE-listed equities matching a name/ticker.
    Yahoo indexes virtually the entire NSE+BSE universe, and — unlike NSE's or
    BSE's own sites — is reliably reachable from a cloud server. This is the
    most dependable layer when the NSE list and BSE search both come up empty
    (which happens often, since NSE/BSE frequently block cloud/datacenter IPs
    outright). Matches are tagged exchange="YAHOO:NSE"/"YAHOO:BSE" so the
    quote-fetcher knows the returned symbol already has its .NS/.BO suffix."""
    try:
        resp = requests.get(
            YAHOO_SEARCH_URL,
            headers=YAHOO_HEADERS,
            params={"q": q, "quotesCount": 20, "newsCount": 0},
            timeout=REQUEST_TIMEOUT,
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
        return _fetch_bse_quote(symbol, company_name)
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


def _search_equity_master(q: str, limit: int = 8) -> list[dict]:
    """Search NSE's ~2,000-stock list first (fast, cached); top up with a live
    BSE search for anything NSE doesn't have (BSE-only smaller-cap stocks),
    so combined coverage spans both exchanges (~6,000-7,000 companies)."""
    fetch_equity_master()
    q_upper = q.strip().upper()
    if not q_upper:
        return []

    exact, starts, contains = [], [], []
    for symbol, name in _equity_master.items():
        name_upper = name.upper()
        entry = {"symbol": symbol, "name": name, "exchange": "NSE"}
        if symbol == q_upper:
            exact.append(entry)
        elif symbol.startswith(q_upper) or name_upper.startswith(q_upper):
            starts.append(entry)
        elif q_upper in symbol or q_upper in name_upper:
            contains.append(entry)
    combined = (exact + starts + contains)[:limit]

    if len(combined) < limit:
        seen_names = {r["name"].lower() for r in combined}
        for r in _search_bse(q, limit=limit - len(combined)):
            if r["name"].lower() not in seen_names:
                combined.append(r)
                seen_names.add(r["name"].lower())

    if len(combined) < limit:
        seen_names = {r["name"].lower() for r in combined}
        for r in _search_yahoo_stocks(q, limit=limit - len(combined)):
            if r["name"].lower() not in seen_names:
                combined.append(r)
                seen_names.add(r["name"].lower())

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
    """Fetch Sensex/Nifty/Gold/USD-INR/Crude/Silver, cached for TICKER_CACHE_SECONDS."""
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
    usdinr_rate = usdinr_q["price"] if usdinr_q else None
    if usdinr_q:
        pct = _pct_change(usdinr_q["price"], usdinr_q["prev_close"])
        result["usdinr"] = {"value": round(usdinr_q["price"], 2), "change_pct": pct, "direction": _direction(pct)}
    else:
        result["usdinr"] = {"value": None, "change_pct": None, "direction": "FLAT"}

    # Gold/silver futures (COMEX, via Yahoo) are the international spot price,
    # in USD per troy ounce — noticeably lower than what MCX/domestic bullion
    # actually trades at, because Indian prices bake in import duty + GST +
    # a dealer premium on top of the international price. There is no free
    # live MCX price feed available (genuine MCX data access costs upwards of
    # ₹20 lakh/year), so instead of showing the (misleadingly low) raw
    # international conversion, we apply the standard ~10% duty+GST markup
    # widely used for back-of-envelope domestic estimates. This still won't
    # match the exact MCX tick, but it lands in the right ballpark instead of
    # being systematically ~10% under it.
    DOMESTIC_METAL_PREMIUM = 1.10
    METAL_UNITS = {"gold": (10, "10g"), "silver": (1000, "kg")}
    for name, (grams, unit_label) in METAL_UNITS.items():
        q = quotes.get(name)
        if q and usdinr_rate:
            price_inr = (q["price"] / TROY_OUNCE_IN_GRAMS) * usdinr_rate * grams * DOMESTIC_METAL_PREMIUM
            prev_inr = (q["prev_close"] / TROY_OUNCE_IN_GRAMS) * usdinr_rate * grams * DOMESTIC_METAL_PREMIUM
            pct = _pct_change(price_inr, prev_inr)
            result[name] = {
                "value": round(price_inr, 2),
                "change_pct": pct,
                "direction": _direction(pct),
                "unit": f"INR/{unit_label}",
            }
        else:
            result[name] = {"value": None, "change_pct": None, "direction": "FLAT", "unit": f"INR/{unit_label}"}

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

@app.route("/")
def serve_index():
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
      q     - free-text search across title/summary/source/ticker-like words
      days  - only return articles from the last N days (defaults to all stored)
    """
    fetch_all_feeds()

    q = request.args.get("q", "").strip().lower()
    days = request.args.get("days", type=int)

    with _lock:
        articles = list(_news_store.values())

    if q:
        articles = [
            a for a in articles
            if q in a["title"].lower() or q in a["summary"].lower() or q in a["source"].lower()
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
    """Live-ish Sensex/Nifty/Gold/USD-INR/Crude/Silver snapshot (best-effort, cached)."""
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
    """Autocomplete: search across NSE + BSE (~6,000-7,000 companies combined) by symbol or name."""
    q = (request.args.get("q") or "").strip()
    if len(q) < 2:
        return jsonify({"results": []})
    raw = _search_equity_master(q, limit=10)
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
# Entrypoint
# --------------------------------------------------------------------------

if __name__ == "__main__":
    port = int(os.environ.get("PORT", 5000))
    app.run(host="0.0.0.0", port=port, debug=False)
