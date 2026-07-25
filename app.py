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
    "Economic Times": "https://economictimes.indiatimes.com/markets/rssfeeds/1977021501.cms",
    "Livemint": "https://www.livemint.com/rss/markets",
    "Business Standard": "https://www.business-standard.com/rss/markets-106.rss",
}

FETCH_INTERVAL_SECONDS = 300     # re-pull RSS feeds at most every 5 minutes
MAX_STORED_ARTICLES = 500        # keep the last N articles as our "history"
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


def _match_stock(text: str) -> tuple[str | None, str | None]:
    """Match free text against STOCK_SYMBOLS aliases. Returns (symbol, company_name) or (None, None)."""
    q = (text or "").strip().lower()
    if not q:
        return None, None
    if q in STOCK_SYMBOLS:
        return STOCK_SYMBOLS[q]
    for alias, (symbol, name) in STOCK_SYMBOLS.items():
        if alias in q or q in alias:
            return symbol, name
    return None, None


def _fetch_stock_quote(symbol: str, company_name: str) -> dict | None:
    """Best-effort share quote: try NSE (most accurate) then Yahoo (more reliable from the cloud)."""
    quote = _fetch_nse_quote(symbol)
    if quote and quote.get("price") is not None:
        return quote
    return _fetch_yahoo_equity_quote(symbol, company_name)


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

    # Gold/silver futures are quoted in USD per troy ounce — convert to INR/gram
    # (illustrative retail-style figures, not official bullion rates).
    for name, per_grams in (("gold", 1), ("silver", 10)):
        q = quotes.get(name)
        if q and usdinr_rate:
            price_inr_per_gram = (q["price"] / TROY_OUNCE_IN_GRAMS) * usdinr_rate * per_grams
            prev_inr_per_gram = (q["prev_close"] / TROY_OUNCE_IN_GRAMS) * usdinr_rate * per_grams
            pct = _pct_change(price_inr_per_gram, prev_inr_per_gram)
            result[name] = {
                "value": round(price_inr_per_gram, 2),
                "change_pct": pct,
                "direction": _direction(pct),
                "unit": f"INR/{per_grams}g",
            }
        else:
            result[name] = {"value": None, "change_pct": None, "direction": "FLAT", "unit": f"INR/{per_grams}g"}

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
        "stock market for retail investors. Keep answers concise and avoid heavy jargon. "
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


@app.route("/api/stock")
def api_stock():
    """
    Look up a share by name/ticker (matched against STOCK_SYMBOLS) and return
    its live quote (NSE, falling back to Yahoo if NSE is unreachable) plus
    recent related headlines.
    Query params: q - stock name or keyword (e.g. "tata motors", "hdfc")
    """
    q = (request.args.get("q") or "").strip()
    if not q:
        return jsonify({"error": "'q' query param is required"}), 400

    matched_symbol, matched_name = _match_stock(q)
    if not matched_symbol:
        return jsonify({"matched": False, "quote": None, "news": []})

    quote = _fetch_stock_quote(matched_symbol, matched_name)

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
        "symbol": matched_symbol,
        "company_name": matched_name,
        "quote": quote,
        "news": related[:10],
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
    symbol, name = _match_stock(message)
    if symbol:
        quote = _fetch_stock_quote(symbol, name)
        if quote and quote.get("price") is not None:
            context_lines.append(
                f"{name} ({symbol}): last price ₹{quote['price']}, "
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
