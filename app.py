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
# Check https://ai.google.dev/gemini-api/docs/models for the current list
# of available model names if this one is ever retired.
GEMINI_MODEL = os.environ.get("GEMINI_MODEL", "gemini-2.5-flash")
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

# --------------------------------------------------------------------------
# In-memory storage (simple + zero-setup; swap for a DB later if you want
# persistence across restarts).
# --------------------------------------------------------------------------

_lock = threading.Lock()
_news_store: dict[str, dict] = {}     # link -> article
_analysis_cache: dict[str, dict] = {} # cache_key -> Gemini analysis result
_last_fetch_time = 0.0


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
            "temperature": 0.4,
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


# --------------------------------------------------------------------------
# Entrypoint
# --------------------------------------------------------------------------

if __name__ == "__main__":
    port = int(os.environ.get("PORT", 5000))
    app.run(host="0.0.0.0", port=port, debug=False)
