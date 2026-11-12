"""
Website Uptime Checker v11a - Streamlit Dashboard

Upload a CSV of website URLs, or point it at a site to crawl all of that
site's internal pages, and check which ones are up or down. Optionally
emails an address when a site goes down. Built to run locally or on
Streamlit Community Cloud.
"""

import base64
import hashlib
import hmac
import json
import os
import re
import shutil
import socket
import ssl
import ipaddress
import logging
import random
import subprocess
import types
import sys
import tempfile
import threading
import time
import io
import smtplib
from collections import deque
from email.mime.text import MIMEText
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
from html import escape as html_escape
from urllib.parse import quote, urljoin, urlparse, urlunparse

import pandas as pd
import requests
import streamlit as st
from bs4 import BeautifulSoup

# Resource and retry limits must be declared before functions that use them in
# default arguments (Python evaluates default arguments when the function is defined).
MAX_ANALYZE_BYTES = 2_000_000
MAX_RESPONSE_BYTES = int(os.environ.get("UPTIME_MAX_RESPONSE_BYTES", str(MAX_ANALYZE_BYTES)))
MAX_REDIRECTS = 5
DEFAULT_RETRIES = 1

try:
    import certifi
except ImportError:  # certifi ships with requests; this is only a safety net
    certifi = None

try:
    from selenium import webdriver
    from selenium.webdriver.chrome.options import Options as ChromeOptions
    from selenium.common.exceptions import WebDriverException, TimeoutException
    SELENIUM_AVAILABLE = True
except ImportError:
    SELENIUM_AVAILABLE = False

st.set_page_config(page_title="Website Uptime Checker v11a", page_icon="🌐", layout="wide")


def normalize_client_host(host: str) -> str:
    """Return a canonical exact host for client account scope checks."""
    host = str(host or "").strip().lower().rstrip(".")
    if host.startswith("www."):
        host = host[4:]
    try:
        host = host.encode("idna").decode("ascii")
    except UnicodeError as exc:
        raise ValueError(f"Invalid client hostname: {host}") from exc
    if (not host or len(host) > 253 or ":" in host or ".." in host
            or not re.fullmatch(r"[a-z0-9](?:[a-z0-9.-]*[a-z0-9])?", host)
            or any(not label or len(label) > 63 or label.startswith("-") or label.endswith("-")
                   for label in host.split("."))):
        raise ValueError(f"Invalid client hostname: {host}")
    return host


def load_client_accounts() -> dict:
    """Load per-client PBKDF2 password hashes and exact hostname allowlists."""
    raw = os.environ.get("UPTIME_CLIENT_USERS", "").strip()
    if not raw:
        return {}
    try:
        configured = json.loads(raw)
    except json.JSONDecodeError as exc:
        raise ValueError("UPTIME_CLIENT_USERS must contain valid JSON.") from exc
    if not isinstance(configured, dict):
        raise ValueError("UPTIME_CLIENT_USERS must be a JSON object keyed by username.")

    accounts = {}
    for username, account in configured.items():
        if (not isinstance(username, str) or not username.strip() or username != username.strip()
                or len(username) > 64
                or not isinstance(account, dict)):
            raise ValueError("Each client account must have a username and an account object.")
        password_hash = account.get("password_hash")
        hosts = account.get("hosts")
        if not isinstance(password_hash, str):
            raise ValueError(f"Client account {username!r} is missing a password_hash.")
        parts = password_hash.split("$")
        if len(parts) != 4 or parts[0] != "pbkdf2_sha256":
            raise ValueError(f"Client account {username!r} has an unsupported password hash.")
        try:
            iterations = int(parts[1])
            salt = bytes.fromhex(parts[2])
            digest = bytes.fromhex(parts[3])
        except ValueError as exc:
            raise ValueError(f"Client account {username!r} has a malformed password hash.") from exc
        if not 100_000 <= iterations <= 2_000_000 or not 16 <= len(salt) <= 64 or len(digest) != 32:
            raise ValueError(f"Client account {username!r} has an invalid password hash configuration.")
        if not isinstance(hosts, list) or not hosts:
            raise ValueError(f"Client account {username!r} must have at least one allowed hostname.")
        try:
            allowed_hosts = frozenset(normalize_client_host(host) for host in hosts)
        except (TypeError, ValueError) as exc:
            raise ValueError(f"Client account {username!r} has an invalid hostname allowlist.") from exc
        accounts[username.strip()] = {
            "password_hash": password_hash,
            "hosts": allowed_hosts,
        }
    return accounts


def verify_client_password(password: str, password_hash: str) -> bool:
    _, iterations, salt_hex, digest_hex = password_hash.split("$")
    candidate = hashlib.pbkdf2_hmac(
        "sha256",
        password.encode("utf-8"),
        bytes.fromhex(salt_hex),
        int(iterations),
    ).hex()
    return hmac.compare_digest(candidate, digest_hex)


try:
    CLIENT_ACCOUNTS = load_client_accounts()
except ValueError as exc:
    st.error(f"Client login configuration error: {exc}")
    st.stop()

if not CLIENT_ACCOUNTS:
    st.error(
        "Client logins are not configured. Set UPTIME_CLIENT_USERS with each client's "
        "password hash and allowed hostnames before starting the app."
    )
    st.stop()

_client_username = st.session_state.get("client_username")
if _client_username not in CLIENT_ACCOUNTS:
    if _client_username is not None:
        st.session_state.clear()
    with st.form("client_login"):
        st.subheader("Client login")
        login_username = st.text_input("Username", max_chars=64)
        login_password = st.text_input("Password", type="password", max_chars=1024)
        login_submitted = st.form_submit_button("Log in", type="primary")
    if login_submitted:
        account = CLIENT_ACCOUNTS.get(login_username.strip())
        if account and verify_client_password(login_password, account["password_hash"]):
            st.session_state["client_username"] = login_username.strip()
            st.rerun()
        st.error("Invalid username or password.")
    st.stop()

CLIENT_ACCOUNT = CLIENT_ACCOUNTS[_client_username]
CLIENT_ALLOWED_HOSTS = CLIENT_ACCOUNT["hosts"]

HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
        "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36"
    ),
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
    "Accept-Language": "en-US,en;q=0.9",
}


def build_headers(url: str) -> dict:
    """Headers for a single request. NOTE: this previously added a same-site
    Referer header, but that was reverted — a self-referencing Referer on the
    very first request to a site (which is what every check here is) is a
    pattern real browsers never produce, and it turned out to trigger bot
    detection on some sites rather than avoid it. Keeping this as a thin
    wrapper (rather than using HEADERS directly everywhere) in case a real
    per-request header need comes up later."""
    return dict(HEADERS)


# ---------------------------------------------------------------------------
# Crawler key (X-ASAP-Key) handling and the rules that come with it
# ---------------------------------------------------------------------------
# The key is sent as an `X-ASAP-Key` request header, never in the URL, on every
# HTTP request this app makes to the site you are checking, including each hop
# of a redirect chain. It is loaded from a local secrets file or an environment
# variable (not hardcoded here) so it never ends up in a repo. The key is used
# server-side only: it is never shown in the UI or sent to the browser.
#
# Which domains receive it is decided by what you enter, not by a fixed list:
#   * Crawl a website: the domain you type in is trusted. Every page on that
#     exact host gets the key; links to any other host do not.
#   * Upload a CSV: off by default; optionally each URL's own host is trusted.
# Matching is on the exact host (www. is ignored), not on subdomains. A
# redirect that leaves the trusted host drops the header.
#
# Requests that carry the key also follow the site owner's conditions. These are
# enforced in KeyedSession.send(), so every request and every redirect hop is
# covered and no other code path can bypass them:
#   * https only, GET/HEAD only (no write requests)
#   * a stable, identifying User-Agent instead of a browser one
#   * a cap on requests per second to that host
#   * robots.txt is read and obeyed (including Crawl-delay)
#   * RFQ and contact paths are not requested

KEY_HEADER_NAME = "X-ASAP-Key"
DEFAULT_USER_AGENT = "UptimeChecker/1.0"
KEY_CONFIG = {
    "key": "",
    "hosts": [],                          # hosts approved to receive the crawler key
    "policy_hosts": [],                   # CSV/site hosts where crawl rules apply even without a key
    "user_agent": DEFAULT_USER_AGENT,
    "rps": 1.0,                           # max requests per second per trusted host
    "blocked_paths": ["rfq", "/contact"],  # fragments of a path or query that are never requested
}


def _secret(name: str) -> str:
    try:
        value = st.secrets["crawler"][name]
        if value:
            return str(value).strip()
    except Exception:
        pass
    return ""


def load_x_key() -> str:
    return _secret("x_key") or os.environ.get("UPTIME_X_KEY", "").strip()


def load_user_agent() -> str:
    return _secret("user_agent") or os.environ.get("UPTIME_USER_AGENT", "").strip() or DEFAULT_USER_AGENT


def parse_path_list(text: str) -> list:
    return [p.strip().lower() for p in (text or "").split(",") if p.strip()]


def key_host_of(url: str) -> str:
    """Normalized host used for key scoping: lowercase, no port, no leading www."""
    host = (urlparse(url).hostname or "").lower()
    return host[4:] if host.startswith("www.") else host


def url_gets_key(url: str) -> bool:
    """True if this exact URL should carry the X-ASAP-Key header: a key is loaded,
    the host is exactly one the user entered, and the connection is https so
    the key is never sent in clear text."""
    if not KEY_CONFIG["key"] or not KEY_CONFIG["hosts"]:
        return False
    if urlparse(url).scheme != "https":
        return False
    host = key_host_of(url)
    return bool(host) and host in KEY_CONFIG["hosts"]


class PolicyBlocked(requests.exceptions.RequestException):
    """Raised instead of sending a request the site owner's conditions forbid."""


class ScanLimitReached(PolicyBlocked):
    pass


class RequestBudget:
    def __init__(
        self, max_requests: int, max_seconds: float, allowed_hosts=None,
        security_hosts=None, security_enabled=None,
    ):
        self.max_requests = max(1, int(max_requests))
        self.deadline = time.monotonic() + max(1.0, float(max_seconds))
        self.requests_made = 0
        self.allowed_hosts = None if allowed_hosts is None else frozenset(allowed_hosts)
        self.security_hosts = None if security_hosts is None else frozenset(security_hosts)
        self.security_enabled = security_enabled
        self._lock = threading.Lock()

    def consume(self, timeout: float) -> float:
        with self._lock:
            remaining = self.deadline - time.monotonic()
            if remaining <= 0:
                raise ScanLimitReached("Scan stopped: time limit reached")
            if self.requests_made >= self.max_requests:
                raise ScanLimitReached(f"Scan stopped: request limit of {self.max_requests} reached")
            self.requests_made += 1
            return min(float(timeout), remaining)

    def remaining_seconds(self) -> float:
        return max(0.0, self.deadline - time.monotonic())


# --- rate cap ----------------------------------------------------------------

class HostThrottle:
    """Spaces request start times per host so the rate never exceeds the cap,
    however many threads are making requests."""

    def __init__(self):
        self._lock = threading.Lock()
        self._next = {}

    def wait(self, host: str, interval: float) -> None:
        if interval <= 0:
            return
        with self._lock:
            now = time.monotonic()
            slot = max(self._next.get(host, 0.0), now)
            self._next[host] = slot + interval
        if slot > now:
            time.sleep(slot - now)


THROTTLE = HostThrottle()
WAIT = threading.local()  # time a thread spent waiting on policy/throttle, so response times exclude it


# --- robots.txt (RFC 9309 matching: wildcards, $, longest rule wins) ---------

def robots_token() -> str:
    return (KEY_CONFIG["user_agent"].split("/")[0].split() or ["*"])[0].lower()


class RobotsRules:
    def __init__(self, text: str = "", disallow_all: bool = False, reason: str = ""):
        self.disallow_all = disallow_all
        self.reason = reason
        self.crawl_delay = 0.0
        self._rules = []  # (allow, compiled regex, pattern length)
        if text:
            self._parse(text)

    def _parse(self, text: str) -> None:
        token = robots_token()
        groups, agents, rules, delay, in_rules = [], [], [], None, False

        def flush():
            if agents:
                groups.append((list(agents), list(rules), delay))

        for raw in text.splitlines():
            line = raw.split("#", 1)[0].strip()
            if ":" not in line:
                continue
            field, value = (part.strip() for part in line.split(":", 1))
            field = field.lower()
            if field == "user-agent":
                if in_rules:
                    flush()
                    agents, rules, delay, in_rules = [], [], None, False
                agents.append(value.lower())
            elif field in ("allow", "disallow"):
                in_rules = True
                rules.append((field == "allow", value))
            elif field == "crawl-delay":
                in_rules = True
                try:
                    delay = float(value)
                except ValueError:
                    pass
        flush()

        specific = [g for g in groups if any(a != "*" and a in token for a in g[0])]
        chosen = specific or [g for g in groups if "*" in g[0]]
        for _agents, group_rules, group_delay in chosen:
            if group_delay:
                self.crawl_delay = max(self.crawl_delay, group_delay)
            for allow, pattern in group_rules:
                if not pattern:
                    continue  # empty Disallow/Allow has no effect
                anchored = pattern.endswith("$")
                body = pattern[:-1] if anchored else pattern
                regex = "".join(".*" if ch == "*" else re.escape(ch) for ch in body) + ("$" if anchored else "")
                self._rules.append((allow, re.compile(regex), len(pattern)))

    def allows(self, path_and_query: str) -> bool:
        if self.disallow_all:
            return False
        allowed, best = True, -1
        for allow, rx, length in self._rules:
            if rx.match(path_and_query) and (length > best or (length == best and allow)):
                allowed, best = allow, length
        return allowed


ROBOTS_CACHE = {}
ROBOTS_LOCK = threading.RLock()


def _load_robots(base: str, request_budget=None) -> RobotsRules:
    """Fetch robots.txt once per host. Anything other than a clean 200 (or a plain
    404/410, meaning there is no file) is treated as 'cannot verify', so nothing
    is requested rather than guessing."""
    try:
        r = http_get(base + "/robots.txt", timeout=15, request_budget=request_budget)
    except ScanLimitReached:
        raise
    except requests.exceptions.RequestException as e:
        return RobotsRules(disallow_all=True, reason=f"Skipped: robots.txt could not be fetched ({type(e).__name__}), so nothing was requested")
    if r.status_code in (404, 410):
        return RobotsRules()
    if r.status_code == 200:
        head = r.text[:600].lower()
        if "<html" in head or "<!doctype" in head:
            return RobotsRules(disallow_all=True, reason="Skipped: robots.txt returned a web page, not rules (likely a bot-protection challenge; check the key)")
        return RobotsRules(text=r.text)
    hint = " (this usually means the request was blocked; check the key)" if r.status_code in (202, 401, 403, 405) else ""
    return RobotsRules(disallow_all=True, reason=f"Skipped: robots.txt unavailable (HTTP {r.status_code}){hint}, so nothing was requested")


def get_robots_rules(parsed, request_budget=None) -> RobotsRules:
    base = f"{parsed.scheme}://{parsed.netloc.lower()}"
    with ROBOTS_LOCK:
        rules = ROBOTS_CACHE.get(base)
        if rules is None:
            ROBOTS_CACHE[base] = RobotsRules()  # placeholder so a redirect during the fetch can't recurse
            try:
                rules = _load_robots(base, request_budget=request_budget)
            except Exception:
                ROBOTS_CACHE.pop(base, None)
                raise
            ROBOTS_CACHE[base] = rules
    return rules


# --- the session that enforces all of it --------------------------------------

class KeyedSession(requests.Session):
    """requests.Session that, for approved hosts, adds the X-ASAP-Key header, uses
    the identifying User-Agent, and enforces the site owner's conditions.

    Plain `headers=` on requests.get() is copied onto every redirect hop
    unchanged, which would send the key to whatever host a redirect points at.
    Re-evaluating per hop (rebuild_auth runs on every redirect, and send() runs
    for every hop) keeps everything on for in-scope hops and strips the key the
    moment a redirect leaves the approved host."""

    def __init__(self, request_budget=None):
        super().__init__()
        self.request_budget = request_budget

    def _apply_key(self, prepared):
        if url_gets_key(prepared.url):
            prepared.headers[KEY_HEADER_NAME] = KEY_CONFIG["key"]
            prepared.headers["User-Agent"] = KEY_CONFIG["user_agent"]
        else:
            prepared.headers.pop(KEY_HEADER_NAME, None)
            prepared.headers["User-Agent"] = HEADERS["User-Agent"]

    def prepare_request(self, request):
        prepared = super().prepare_request(request)
        self._apply_key(prepared)
        return prepared

    def rebuild_auth(self, prepared_request, response):
        super().rebuild_auth(prepared_request, response)
        self._apply_key(prepared_request)

    def _enforce_policy(self, request):
        method = (request.method or "GET").upper()
        if method not in ("GET", "HEAD"):
            raise PolicyBlocked("Blocked: write requests are never sent with the crawler key")
        parsed = urlparse(request.url)
        path = parsed.path or "/"
        if path.lower() == "/robots.txt":
            return  # always allowed: needed to read the rules
        # "rfq" has no leading slash so /straightrfq/ and ?type=rfq match as well as /rfq.
        searchable = (path + ("?" + parsed.query if parsed.query else "")).lower()
        for fragment in KEY_CONFIG["blocked_paths"]:
            if fragment in searchable:
                raise PolicyBlocked(f"Skipped: path matches an excluded RFQ/contact pattern ({fragment})")
        rules = get_robots_rules(parsed, request_budget=self.request_budget)
        if rules.disallow_all:
            raise PolicyBlocked(rules.reason)
        target = path + (("?" + parsed.query) if parsed.query else "")
        if not rules.allows(target):
            raise PolicyBlocked("Skipped: disallowed by robots.txt")

    def send(self, request, **kwargs):
        # Enforce agreed crawl rules for CSV/site targets even when the key opt-in
        # is off. Only explicitly selected target hosts are policy-scoped.
        policy_host = key_host_of(request.url) in set(KEY_CONFIG.get("policy_hosts", []))
        if url_gets_key(request.url) or policy_host:
            t0 = time.perf_counter()
            self._enforce_policy(request)
            parsed = urlparse(request.url)
            rules = ROBOTS_CACHE.get(f"{parsed.scheme}://{parsed.netloc.lower()}")
            crawl_delay = min(rules.crawl_delay, 60.0) if rules else 0.0
            interval = max(1.0 / max(KEY_CONFIG["rps"], 0.01), crawl_delay)
            THROTTLE.wait(key_host_of(request.url), interval)
            WAIT.total = getattr(WAIT, "total", 0.0) + (time.perf_counter() - t0)
        if self.request_budget is not None:
            timeout = kwargs.get("timeout", 30)
            if isinstance(timeout, tuple):
                connect_timeout, read_timeout = timeout
            else:
                connect_timeout = read_timeout = timeout
            bounded_timeout = self.request_budget.consume(read_timeout)
            kwargs["timeout"] = (min(connect_timeout, bounded_timeout), bounded_timeout)
        return super().send(request, **kwargs)


def _validate_public_url(url: str, request_budget=None, allowed_hosts=None) -> str:
    """Validate a target before every network hop. Public Internet targets only by default.

    Set UPTIME_ALLOW_PRIVATE_TARGETS=true only in a controlled, trusted deployment where
    scanning private infrastructure is explicitly authorized. Network egress controls are
    still required to fully mitigate DNS rebinding and browser subresource SSRF.
    """
    url = normalize_url(url)
    try:
        parsed = urlparse(url)
        if parsed.scheme not in ("http", "https"):
            raise PolicyBlocked("Blocked: only http:// and https:// URLs are allowed")
        if parsed.username or parsed.password:
            raise PolicyBlocked("Blocked: URLs containing credentials are not allowed")
        host = parsed.hostname
        if not host or any(ch.isspace() for ch in host):
            raise PolicyBlocked("Blocked: invalid or missing hostname")
        port = parsed.port
        if port is not None and not (1 <= port <= 65535):
            raise PolicyBlocked("Blocked: invalid port")
    except ValueError:
        raise PolicyBlocked("Blocked: malformed URL or port")

    scoped_hosts = allowed_hosts
    if scoped_hosts is None and request_budget is not None:
        scoped_hosts = request_budget.allowed_hosts
    if scoped_hosts is not None:
        try:
            scoped_host = normalize_client_host(host)
        except ValueError as exc:
            raise PolicyBlocked("Blocked: target hostname is outside the logged-in account's scope") from exc
        if scoped_host not in scoped_hosts:
            raise PolicyBlocked("Blocked: target hostname is outside the logged-in account's scope")

    if host.lower() in {"localhost", "localhost.localdomain"} or host.lower().endswith(".localhost"):
        if os.environ.get("UPTIME_ALLOW_PRIVATE_TARGETS", "false").lower() != "true":
            raise PolicyBlocked("Blocked: localhost targets are disabled")
    if os.environ.get("UPTIME_ALLOW_PRIVATE_TARGETS", "false").lower() == "true":
        return url

    try:
        # Reject IP literals and DNS names resolving to any non-public address.
        literal = ipaddress.ip_address(host.strip("[]"))
        addresses = [literal]
    except ValueError:
        try:
            infos = socket.getaddrinfo(host, port or (443 if parsed.scheme == "https" else 80), type=socket.SOCK_STREAM)
            addresses = [ipaddress.ip_address(item[4][0].split("%", 1)[0]) for item in infos]
        except (OSError, ValueError):
            raise requests.exceptions.ConnectionError("DNS resolution failed")
    if not addresses:
        raise requests.exceptions.ConnectionError("DNS returned no addresses")
    for address in addresses:
        if not address.is_global:
            raise PolicyBlocked("Blocked: target resolves to a private, local, reserved, or non-public IP address")
    return url


def _bounded_read(response, max_bytes=MAX_RESPONSE_BYTES, request_budget=None):
    """Read at most max_bytes + 1 decoded bytes; close oversized responses promptly."""
    chunks, total = [], 0
    for chunk in response.iter_content(chunk_size=65536):
        if request_budget is not None and request_budget.remaining_seconds() <= 0:
            response.close()
            raise ScanLimitReached("Scan stopped: time limit reached")
        if not chunk:
            continue
        total += len(chunk)
        if total > max_bytes:
            response.close()
            raise requests.exceptions.ContentDecodingError(
                f"Response exceeded configured limit of {max_bytes} bytes"
            )
        chunks.append(chunk)
    response._content = b"".join(chunks)
    response._content_consumed = True
    return response


def http_get(url: str, timeout: float, max_redirects: int = MAX_REDIRECTS, request_budget=None):
    """Bounded GET with per-hop URL/DNS validation, safe redirect handling and body limits.

    Redirects are handled manually so every Location is revalidated before it is requested.
    A response is fully read only up to MAX_RESPONSE_BYTES, including decoded compression.
    """
    current = normalize_url(url)
    key_hop_diagnostics = []  # host + yes/no only; never record the key value
    with KeyedSession(request_budget=request_budget) as session:
        for hop in range(max_redirects + 1):
            current = _validate_public_url(current, request_budget=request_budget)
            parsed = urlparse(current)
            # Apply a conservative host throttle to all targets, not only key-scoped hosts.
            t0 = time.perf_counter()
            THROTTLE.wait((parsed.hostname or "").lower(), 0.25)
            WAIT.total = getattr(WAIT, "total", 0.0) + (time.perf_counter() - t0)
            # Record the decision for this exact hop before sending. The key itself is
            # never included in diagnostics; redirects are assessed independently.
            key_hop_diagnostics.append((urlparse(current).hostname or "unknown", url_gets_key(current)))
            response = session.get(current, headers=build_headers(current), timeout=(min(timeout, 10), timeout),
                                   allow_redirects=False, stream=True)
            if response.status_code in (301, 302, 303, 307, 308):
                location = response.headers.get("Location")
                response.close()
                if not location:
                    raise requests.exceptions.TooManyRedirects("Redirect response had no Location header")
                if hop >= max_redirects:
                    raise requests.exceptions.TooManyRedirects(f"More than {max_redirects} redirects")
                current = urljoin(current, location)
                continue
            response = _bounded_read(response, request_budget=request_budget)
            # Expose safe per-hop diagnostics to the result row (host names and booleans only).
            response._crawler_key_diagnostics = [
                f"{host}: {'sent' if sent else 'not sent'}" for host, sent in key_hop_diagnostics
            ]
            # Preserve final response URL and decoded content for existing analysis/reporting.
            return response
    raise requests.exceptions.TooManyRedirects(f"More than {max_redirects} redirects")


NON_HTML_EXTENSIONS = (
    ".jpg", ".jpeg", ".png", ".gif", ".svg", ".ico", ".webp", ".bmp",
    ".pdf", ".zip", ".rar", ".7z", ".doc", ".docx", ".xls", ".xlsx", ".ppt", ".pptx",
    ".css", ".js", ".mp4", ".mp3", ".avi", ".mov", ".wmv",
    ".woff", ".woff2", ".ttf", ".eot", ".xml", ".json", ".rss",
)

# ---------------------------------------------------------------------------
# Passive security checks
# ---------------------------------------------------------------------------
# Everything here reads what the scan already receives: response headers and page
# content of pages that were fetched anyway. On top of that there is exactly one
# TLS handshake and one request for /.well-known/security.txt per site, both
# subject to the same rate cap (and, for the request, robots.txt) as everything
# else. Nothing is probed, guessed, fuzzed, submitted or exploited, no ports are
# scanned, and no logins are attempted. It applies only to the site you crawl (or
# the sites in your CSV), never to external links found along the way.

SECURITY_CONFIG = {"enabled": False, "hosts": set(), "hostnames": []}
UNCONFIRMED_STATUSES = ("Unknown", "Blocked", "Restricted", "Challenged")
SERVER_RECHECK_SECONDS = int(os.environ.get("UPTIME_SERVER_RECHECK_SECONDS", "90"))  # gap before a 5xx is checked again
MAX_WORKERS_ONE_SITE = 2
SNAPSHOT_MAX_ROWS = 15  # page lines per table in the client snapshot; the technical report has all of them
MIN_RATING_COVERAGE = 0.5  # a rating needs the passive checks to have seen at least this share of requested pages
SEVERITY_ORDER = {"High": 0, "Medium": 1, "Low": 2, "Info": 3}
logger = logging.getLogger("uptime_checker")
if not logger.handlers:
    _handler = logging.StreamHandler()
    _handler.setFormatter(logging.Formatter("%(asctime)s %(levelname)s %(message)s"))
    logger.addHandler(_handler)
logger.setLevel(os.environ.get("UPTIME_LOG_LEVEL", "WARNING").upper())

THEMES = {
    "private": "Private, encrypted connections",
    "browser": "Browser protections",
    "sessions": "Visitor sessions (cookies)",
    "exposure": "Information the site gives away",
    "sharing": "Sharing data with other websites",
    "certificate": "Security certificate",
    "contact": "Reporting a problem to you",
    "other": "Other",
}


def _f(severity, title, theme, fix, business, how):
    return {"severity": severity, "title": title, "theme": theme, "fix": fix, "business": business, "how": how}


# Each check says what it means for the business and exactly how it is done, so the
# reports, the "what we check" handout and the code can never drift apart.
FINDINGS = {
    "plain-http": _f("High", "Page served over unencrypted HTTP", "private",
        "Serve every page over HTTPS and redirect HTTP to HTTPS.",
        "Anything a visitor sends or reads can be seen or changed by others on the same network, and browsers show a 'Not secure' warning that costs trust.",
        "Looks at the final address the page loaded from, after any redirects, and flags it if it starts with http:// instead of https://."),
    "http-no-redirect": _f("High", "HTTP address does not redirect to HTTPS", "private",
        "Redirect every http:// request to the same address on https://.",
        "Visitors who type the address or follow an old link can stay on an unencrypted connection, where traffic can be read or changed.",
        "Requests the site's http:// address once and checks whether it leads to https://."),
    "http-redirect-indirect": _f("Low", "HTTP redirect does not go straight to HTTPS on the same host", "private",
        "Make the first redirect go to https:// on the same host, then redirect to any preferred host.",
        "An indirect first step can leave part of the visit unencrypted, or stop HSTS from being set for the original host.",
        "Requests the site's http:// address once and reads the first redirect."),
    "hsts-missing": _f("Medium", "Strict-Transport-Security (HSTS) header missing", "private",
        "Send Strict-Transport-Security: max-age=31536000; includeSubDomains once all subdomains support HTTPS.",
        "Without this instruction, a visitor can be tricked into using an unprotected version of the site.",
        "Reads the Strict-Transport-Security response header on every HTTPS page and flags it if it is absent."),
    "hsts-short": _f("Low", "HSTS max-age is shorter than six months", "private",
        "Raise max-age to at least 15768000 (six months); 31536000 is typical.",
        "The protection expires too quickly to be reliable.",
        "Reads the max-age value in the Strict-Transport-Security header and flags it if it is under 15,768,000 seconds (six months)."),
    "csp-missing": _f("Medium", "Content-Security-Policy header missing", "browser",
        "Add a Content-Security-Policy to limit where scripts, frames and other content can load from. Including frame-ancestors in the same policy also provides clickjacking protection.",
        "If someone slips malicious code into a page, nothing stops it loading content from anywhere, which puts customers' data at risk.",
        "Reads the Content-Security-Policy response header and flags it if it is absent."),
    "csp-report-only": _f("Low", "Content-Security-Policy is report-only", "browser",
        "Enforce the policy once the reports show no legitimate breakage.",
        "The rules are being tested but not enforced, so they give no protection yet.",
        "Flags pages that send Content-Security-Policy-Report-Only but no enforced Content-Security-Policy."),
    "csp-unsafe": _f("Low", "Content-Security-Policy allows 'unsafe-inline' or 'unsafe-eval'", "browser",
        "Replace inline scripts with nonces or hashes so unsafe-inline/unsafe-eval can be removed.",
        "The rules contain loopholes that let injected code run.",
        "Searches the Content-Security-Policy for 'unsafe-inline' or 'unsafe-eval'."),
    "clickjacking": _f("Medium", "No clickjacking protection (X-Frame-Options or CSP frame-ancestors)", "browser",
        "Add a Content-Security-Policy frame-ancestors directive, such as frame-ancestors 'self'. X-Frame-Options: SAMEORIGIN can be added for older browsers.",
        "Another website could display this one invisibly and trick visitors into clicking buttons they cannot see, such as approving a payment.",
        "Checks for an X-Frame-Options header or a frame-ancestors rule in the Content-Security-Policy, and flags the page if neither is present."),
    "nosniff-missing": _f("Low", "X-Content-Type-Options: nosniff missing", "browser",
        "Send X-Content-Type-Options: nosniff.",
        "Browsers may guess what a file is and run something that was meant to be harmless.",
        "Reads the X-Content-Type-Options header and flags it unless it is 'nosniff'."),
    "referrer-policy-missing": _f("Low", "Referrer-Policy header missing", "browser",
        "Send a Referrer-Policy such as strict-origin-when-cross-origin.",
        "More of a page's address, which can include private details, may be passed to other sites when a visitor clicks away.",
        "Reads the Referrer-Policy header and flags it if it is absent."),
    "permissions-policy-missing": _f("Info", "Permissions-Policy header missing", "browser",
        "Consider a Permissions-Policy that disables browser features the site does not use.",
        "Browser features the site never uses, such as camera or location, are not switched off, which would limit what injected code could do.",
        "Reads the Permissions-Policy (or older Feature-Policy) header and notes it if it is absent."),
    "server-version": _f("Low", "Server software version disclosed", "exposure",
        "Configure the server to omit version numbers from the Server header.",
        "Telling the world the exact server software and version helps an attacker look up weaknesses known for that version.",
        "Reads the Server response header and flags it if it contains a version number."),
    "powered-by": _f("Low", "Technology or framework version disclosed in response headers", "exposure",
        "Remove X-Powered-By and X-AspNet* headers.",
        "The technology behind the site, and often its version, is advertised to anyone who looks.",
        "Reads the X-Powered-By, X-AspNet-Version and X-AspNetMvc-Version headers and flags any that are present."),
    "cookie-no-secure": _f("Medium", "Cookies set without the Secure attribute", "sessions",
        "Add the Secure attribute so cookies are only sent over HTTPS.",
        "A visitor's 'logged in' note can travel over an unprotected connection, where it can be intercepted.",
        "Reads each Set-Cookie header on HTTPS pages and flags cookies without the Secure attribute. Reports cookie names only, never values."),
    "cookie-no-httponly": _f("Low", "Cookies set without the HttpOnly attribute", "sessions",
        "Add HttpOnly to cookies that page scripts do not need to read.",
        "Scripts on the page can read the note, so malicious code could steal a visitor's session.",
        "Reads each Set-Cookie header and flags cookies without HttpOnly. Names only."),
    "cookie-no-samesite": _f("Low", "Cookies set without a SameSite attribute", "sessions",
        "Set SameSite=Lax (or Strict) unless cross-site use is required.",
        "Other websites can cause a visitor's browser to attach their session to actions they did not intend.",
        "Flags cookies that carry no SameSite attribute. Names only."),
    "cookie-samesite-none-insecure": _f("Medium", "Cookies use SameSite=None without Secure", "sessions",
        "SameSite=None requires the Secure attribute.",
        "A contradictory setting: the cookie may travel between sites but is not protected in transit.",
        "Flags cookies marked SameSite=None that are not also marked Secure."),
    "cors-credentials-wildcard": _f("Medium", "CORS allows any origin together with credentials", "sharing",
        "Do not combine Access-Control-Allow-Origin: * with Allow-Credentials: true; allow specific origins.",
        "Any website could ask this one for a logged-in visitor's private data.",
        "Flags responses that send Access-Control-Allow-Origin: * together with Access-Control-Allow-Credentials: true."),
    "mixed-active": _f("Medium", "HTTPS page loads scripts, frames or stylesheets over HTTP", "private",
        "Load all active content over HTTPS.",
        "A secure page that loads scripts or styles insecurely is only as strong as its weakest piece; tampered code could take over the page.",
        "Reads each HTTPS page's HTML and flags script, iframe, stylesheet, object and embed tags whose address begins with http://."),
    "mixed-passive": _f("Low", "HTTPS page loads images or media over HTTP", "private",
        "Load images and media over HTTPS.",
        "Images or media loaded insecurely trigger browser warnings and can be swapped by an attacker.",
        "Flags image, audio, video and source tags whose address begins with http:// on an HTTPS page."),
    "form-http": _f("Medium", "Form submits to an HTTP address", "private",
        "Point form actions at HTTPS URLs.",
        "Whatever customers type into the form, such as quote requests and contact details, travels unprotected.",
        "Flags HTML forms whose action address begins with http://. Forms are never submitted."),
    "dir-listing": _f("Medium", "Directory listing appears to be enabled", "exposure",
        "Disable automatic directory indexes on the web server.",
        "A folder shows a list of every file inside it, like an open filing cabinet, which can reveal backups or internal documents.",
        "Flags pages whose title begins with 'Index of /', the standard sign of an automatic directory listing."),
    "error-output": _f("Low", "Possible error or debug output in page (verify manually)", "exposure",
        "Turn off verbose error output in production and show a generic error page.",
        "Crash messages can expose internal details, such as file locations or database errors, that help an attacker.",
        "Searches the page text for well-known error and stack-trace patterns. Marked 'verify manually' because a page about errors can trigger it."),
    "generator-version": _f("Low", "Software version disclosed in page (generator meta tag)", "exposure",
        "Remove the version from the generator meta tag.",
        "The site advertises the exact version of its publishing software.",
        "Reads the 'generator' meta tag in the page and flags it if it contains a version number."),
    "challenge-page": _f("Info", "Security checks skipped: the response was a bot-protection challenge page", "other",
        "Check that the crawler key is accepted for this site; a challenge page says nothing about the real site.",
        "The site answered with a 'prove you are human' page, so the real site could not be assessed.",
        "Recognises the markers of common bot-protection challenge pages and skips every other check for that page."),
    "tls-invalid": _f("High", "TLS certificate failed verification", "certificate",
        "Install a valid certificate that matches the host name and chains to a trusted authority.",
        "Browsers warn visitors or block them, and the connection cannot be trusted.",
        "Makes one secure connection to the site and verifies the certificate against trusted authorities and the site name."),
    "tls-expired": _f("High", "TLS certificate has expired", "certificate",
        "Renew the certificate now and automate renewal.",
        "Visitors meet a full-page browser warning until it is renewed.",
        "On the same connection, verification fails because the certificate's end date has passed."),
    "tls-expiring-14": _f("High", "TLS certificate expires in under 14 days", "certificate",
        "Renew the certificate and automate renewal.",
        "An outage is imminent unless it is renewed, and it is entirely avoidable.",
        "Reads the certificate's expiry date from the same connection and counts the days remaining."),
    "tls-expiring-30": _f("Medium", "TLS certificate expires in under 30 days", "certificate",
        "Renew the certificate and automate renewal.",
        "An early warning: renewing now avoids a visitor-facing outage.",
        "Reads the certificate's expiry date from the same connection and counts the days remaining."),
    "tls-ok": _f("Info", "TLS certificate is valid", "certificate", "",
        "The certificate is valid and not close to expiry.",
        "Makes one secure connection to the site and verifies the certificate and its expiry date."),
    "security-txt-missing": _f("Info", "No security.txt published (RFC 9116)", "contact",
        "Publish /.well-known/security.txt with a security contact so researchers know where to report issues.",
        "Without a published security contact, someone who spots a problem has nowhere obvious to report it.",
        "Requests /.well-known/security.txt once and looks for a 'Contact:' line."),
}

# Supplemental finding metadata; safe to add without changing the existing report structure.
FINDINGS.setdefault("sri-missing", {
    "severity": "Low", "title": "Cross-origin script/style without Subresource Integrity",
    "theme": "sharing", "fix": "Where stable third-party assets support it, add integrity and crossorigin attributes; otherwise document the trust decision.",
    "business": "A compromised third-party asset can affect visitors.",
    "how": "Passive inspection of HTML references only; the checker does not fetch or validate the referenced asset."
})

ERROR_PATTERNS = [
    r"traceback \(most recent call last\)",
    r"you have an error in your sql syntax",
    r"sqlstate\[",
    r"ora-\d{5}:",
    r"fatal error:.{0,200} on line \d+",
    r"warning:.{0,200} on line \d+",
    r"unhandled exception",
]


def make_finding(fid: str, detail: str = "") -> dict:
    info = FINDINGS[fid]
    return {"id": fid, "detail": detail, **info}


def looks_like_challenge(text: str, title: str) -> bool:
    low = text[:200000].lower()
    # "cf-chl" alone is too broad: normal pages with a Turnstile widget can contain it.
    return ("awswafcookiedomainlist" in low or "gokuprops" in low
            or "_cf_chl_opt" in low or "cf-chl-bypass" in low
            or "just a moment" in title.lower() or "human verification" in title.lower())


def response_is_challenge(resp) -> bool:
    """True when the response is a bot-protection interstitial rather than the page itself.
    Such a response can be a 2xx, so a status code alone cannot be trusted here."""
    h = resp.headers
    if (h.get("x-amzn-waf-action") or "").strip().lower() == "challenge":
        return True
    if (h.get("cf-mitigated") or "").strip().lower() == "challenge":
        return True
    if "html" not in (h.get("Content-Type") or "").lower() or len(resp.content) > MAX_ANALYZE_BYTES:
        return False
    text = resp.text
    match = re.search(r"<title[^>]*>(.*?)</title>", text[:200000], re.I | re.S)
    return looks_like_challenge(text, match.group(1).strip() if match else "")


def _analyze(resp) -> tuple:
    """Passive checks on one response that was fetched anyway. Returns (findings, meta); meta
    records what applied to the page, so the report can also say what passed."""
    findings = []
    add = lambda fid, detail="": findings.append(make_finding(fid, detail))
    h = resp.headers
    https = (resp.url or "").lower().startswith("https://")

    ctype = (h.get("Content-Type") or "").lower()
    soup, title, text = None, "", ""
    if "html" in ctype and len(resp.content) <= MAX_ANALYZE_BYTES:
        text = resp.text
        soup = BeautifulSoup(text, "html.parser")
        title = soup.title.get_text(strip=True) if soup.title else ""
        if looks_like_challenge(text, title):
            return [make_finding("challenge-page")], {"https": https, "html": True, "cookies": 0, "challenge": True}

    if not https:
        add("plain-http")
    else:
        hsts = h.get("Strict-Transport-Security")
        if not hsts:
            add("hsts-missing")
        else:
            m = re.search(r"max-age\s*=\s*(\d+)", hsts, re.I)
            if not m or int(m.group(1)) < 15768000:
                add("hsts-short", hsts[:80])

    csp = h.get("Content-Security-Policy")
    if not csp:
        add("csp-report-only" if h.get("Content-Security-Policy-Report-Only") else "csp-missing")
    elif re.search(r"'unsafe-(inline|eval)'", csp, re.I):
        add("csp-unsafe")
    if not h.get("X-Frame-Options") and not (csp and re.search(r"frame-ancestors", csp, re.I)):
        add("clickjacking")
    if (h.get("X-Content-Type-Options") or "").strip().lower() != "nosniff":
        add("nosniff-missing")
    if not h.get("Referrer-Policy"):
        add("referrer-policy-missing")
    if not h.get("Permissions-Policy") and not h.get("Feature-Policy"):
        add("permissions-policy-missing")

    server = h.get("Server") or ""
    if re.search(r"\d+\.\d+", server):
        add("server-version", server[:80])
    for name in ("X-Powered-By", "X-AspNet-Version", "X-AspNetMvc-Version"):
        if h.get(name):
            add("powered-by", f"{name}: {h.get(name)[:80]}")
    if (h.get("Access-Control-Allow-Origin") or "").strip() == "*" and \
            (h.get("Access-Control-Allow-Credentials") or "").strip().lower() == "true":
        add("cors-credentials-wildcard")

    # Cookies: names and attributes only, never values.
    raw = getattr(getattr(resp, "raw", None), "headers", None)
    cookies = raw.getlist("Set-Cookie") if raw is not None and hasattr(raw, "getlist") else \
        ([h["Set-Cookie"]] if "Set-Cookie" in h else [])
    no_secure, no_httponly, no_samesite, none_insecure = [], [], [], []
    for c in cookies:
        parts = [x.strip() for x in c.split(";")]
        name = parts[0].split("=", 1)[0].strip()[:60]
        attrs = {x.split("=", 1)[0].strip().lower(): (x.split("=", 1)[1].strip().lower() if "=" in x else "") for x in parts[1:]}
        if https and "secure" not in attrs:
            no_secure.append(name)
        if "httponly" not in attrs:
            no_httponly.append(name)
        samesite = attrs.get("samesite")
        if samesite is None:
            no_samesite.append(name)
        elif samesite == "none" and "secure" not in attrs:
            none_insecure.append(name)
    for fid, names in (("cookie-no-secure", no_secure), ("cookie-no-httponly", no_httponly),
                       ("cookie-no-samesite", no_samesite), ("cookie-samesite-none-insecure", none_insecure)):
        if names:
            add(fid, "Cookie(s): " + ", ".join(names[:8]))

    if soup is not None:
        if title.lower().startswith("index of /"):
            add("dir-listing", title[:80])
        if https:
            active, passive = [], []
            for tag, attr in (("script", "src"), ("iframe", "src"), ("link", "href"), ("object", "data"), ("embed", "src")):
                for el in soup.find_all(tag, attrs={attr: True}):
                    if tag == "link" and "stylesheet" not in [r.lower() for r in (el.get("rel") or [])]:
                        continue
                    if str(el.get(attr, "")).lower().startswith("http://"):
                        active.append(el.get(attr))
            for tag in ("img", "audio", "video", "source"):
                for el in soup.find_all(tag, attrs={"src": True}):
                    if str(el.get("src", "")).lower().startswith("http://"):
                        passive.append(el.get("src"))
            if active:
                add("mixed-active", f"{len(active)} resource(s), e.g. {str(active[0])[:90]}")
            if passive:
                add("mixed-passive", f"{len(passive)} resource(s), e.g. {str(passive[0])[:90]}")
            missing_sri = []
            for el in soup.find_all(["script", "link"]):
                if el.name == "link" and "stylesheet" not in [r.lower() for r in (el.get("rel") or [])]:
                    continue
                src = el.get("src") if el.name == "script" else el.get("href")
                if src and urlparse(urljoin(resp.url or "", str(src))).netloc and not el.get("integrity"):
                    if urlparse(urljoin(resp.url or "", str(src))).netloc.lower() != urlparse(resp.url or "").netloc.lower():
                        missing_sri.append(str(src)[:90])
            if missing_sri:
                add("sri-missing", f"{len(missing_sri)} cross-origin script/stylesheet resource(s) lack integrity metadata; e.g. {missing_sri[0]}")
            for form in soup.find_all("form"):
                action = str(form.get("action") or (resp.url or ""))
                if https and urlparse(urljoin(resp.url or "", action)).scheme.lower() == "http":
                    add("form-http", action[:90])
                    break
            for form in soup.find_all("form", attrs={"action": True}):
                if str(form.get("action", "")).lower().startswith("http://"):
                    add("form-http", str(form.get("action"))[:90])
                    break
        gen = soup.find("meta", attrs={"name": re.compile(r"^generator$", re.I)})
        if gen and re.search(r"\d+\.\d+", gen.get("content", "") or ""):
            add("generator-version", gen.get("content", "")[:80])
        for pattern in ERROR_PATTERNS:
            if re.search(pattern, text, re.I | re.S):
                add("error-output", "Matched a known error-message pattern")
                break
    return findings, {"https": https, "html": soup is not None, "cookies": len(cookies), "challenge": False}


def analyze_response(resp) -> list:
    return _analyze(resp)[0]


def scan_target_of(url: str) -> str:
    """'host' for the default HTTPS port, 'host:port' otherwise. Site-level checks
    must go to the port the site is actually served on."""
    parsed = urlparse(normalize_url(url))
    host = (parsed.hostname or "").lower()
    try:
        port = parsed.port
    except ValueError:
        port = None
    return f"{host}:{port}" if host and port and port != 443 else host


def check_tls(target: str, timeout: float = 8.0, request_budget=None) -> dict:
    """One TLS handshake: certificate validity, expiry and protocol (port 443 unless the target names one)."""
    hostname, _, port_text = target.partition(":")
    port = int(port_text) if port_text.isdigit() else 443
    info = {"hostname": target, "error": "", "error_kind": "", "days_left": None,
            "not_after": "", "issuer": "", "version": "", "cipher": ""}
    cafile = os.environ.get("REQUESTS_CA_BUNDLE") or (certifi.where() if certifi else None)
    try:
        # TLS diagnostics open a raw socket, so apply the same public-target policy first.
        _validate_public_url(f"https://{target}/", request_budget=request_budget)
        ctx = ssl.create_default_context(cafile=cafile)
        if url_gets_key(f"https://{target}/"):
            THROTTLE.wait(key_host_of(f"https://{target}/"), 1.0 / max(KEY_CONFIG["rps"], 0.01))
        with socket.create_connection((hostname, port), timeout=timeout) as sock:
            with ctx.wrap_socket(sock, server_hostname=hostname) as tls:
                cert = tls.getpeercert()
                info["version"] = tls.version() or ""
                info["cipher"] = (tls.cipher() or [""])[0]
    except PolicyBlocked as e:
        info["error_kind"] = "blocked"
        info["error"] = str(e)[:150]
        return info
    except ssl.SSLCertVerificationError as e:
        info["error_kind"] = "verify"
        info["error"] = (getattr(e, "verify_message", "") or str(e))[:150]
        return info
    except (ssl.SSLError, OSError) as e:
        info["error_kind"] = "unreachable"
        info["error"] = f"TLS check not completed ({type(e).__name__})"
        return info
    expires = ssl.cert_time_to_seconds(cert["notAfter"])
    info["days_left"] = int((expires - time.time()) // 86400)
    info["not_after"] = datetime.fromtimestamp(expires, tz=timezone.utc).strftime("%Y-%m-%d")
    issuer = {k: v for rdn in cert.get("issuer", ()) for (k, v) in rdn}
    info["issuer"] = issuer.get("organizationName") or issuer.get("commonName") or ""
    return info


def check_security_txt(target: str, timeout: float = 10.0, request_budget=None) -> tuple:
    """(state, note): one GET of /.well-known/security.txt, under the same rules as any other request."""
    try:
        if request_budget is None:
            r = http_get(f"https://{target}/.well-known/security.txt", timeout)
        else:
            r = http_get(f"https://{target}/.well-known/security.txt", timeout, request_budget=request_budget)
    except ScanLimitReached as e:
        return "not checked", str(e)
    except PolicyBlocked as e:
        return "not checked", str(e)
    except requests.exceptions.RequestException as e:
        return "not checked", f"request failed ({type(e).__name__})"
    if r.status_code == 200 and "contact:" in r.text.lower() and "<html" not in r.text[:300].lower():
        return "present", ""
    if r.status_code in (404, 410):
        return "missing", ""
    return "not checked", f"HTTP {r.status_code}"


REDIRECT_CODES = (301, 302, 303, 307, 308)


def check_http_redirect(target: str, timeout: float = 8.0, request_budget=None) -> dict:
    """Follow the site's http:// address until it reaches https:// or stops. A refusal or failed
    connection proves nothing about redirects, so those are reported as not confirmed."""
    hostname, _, port = target.partition(":")
    if port:
        return {"state": "not-checked", "detail": "Not checked: site uses a custom port"}
    current = f"http://{hostname}/"
    try:
        with KeyedSession(request_budget=request_budget) as session:
            for hop in range(MAX_REDIRECTS + 1):
                current = _validate_public_url(current, request_budget=request_budget)
                THROTTLE.wait(hostname.lower(), 0.25)
                response = session.get(current, headers=build_headers(current), timeout=(min(timeout, 10), timeout),
                                       allow_redirects=False, stream=True)
                code, location = response.status_code, response.headers.get("Location")
                response.close()
                if code in REDIRECT_CODES and location:
                    following = urljoin(current, location)
                    parsed = urlparse(following)
                    if parsed.scheme.lower() == "https":
                        direct = hop == 0 and (parsed.hostname or "").lower() == hostname.lower()
                        return {"state": "ok" if direct else "indirect",
                                "detail": f"Redirects to {following}" + ("" if direct else f" after {hop + 1} redirect(s)")}
                    current = following
                    continue
                if 200 <= code < 300:
                    return {"state": "none", "detail": f"Served over HTTP at {current} (HTTP {code})"}
                return {"state": "not-confirmed", "detail": f"Not confirmed: http:// request got HTTP {code}"}
        return {"state": "not-confirmed", "detail": "Not confirmed: too many redirects"}
    except PolicyBlocked as exc:
        return {"state": "not-checked", "detail": f"Not checked: {str(exc)[:120]}"}
    except requests.exceptions.RequestException as exc:
        return {"state": "not-confirmed", "detail": f"Not confirmed: http:// request failed ({type(exc).__name__})"}


MOZILLA_API = "https://observatory-api.mdn.mozilla.net/api/v2/scan"


def fetch_mozilla_grade(target: str, timeout: float = 45.0, post=None) -> dict:
    """Ask Mozilla HTTP Observatory for its grade. Mozilla's service scans the site itself, so this
    call goes only to Mozilla, and it never carries the crawler key."""
    hostname = target.partition(":")[0]
    post = post or requests.post
    try:
        _validate_public_url(f"https://{hostname}/", request_budget=request_budget)
        response = post(MOZILLA_API, params={"host": hostname}, headers={"User-Agent": DEFAULT_USER_AGENT}, timeout=timeout)
        data = response.json()
    except (requests.exceptions.RequestException, ValueError) as exc:
        return {"grade": "", "error": f"Mozilla request failed ({type(exc).__name__})"}
    if not isinstance(data, dict):
        return {"grade": "", "error": "Mozilla returned an unexpected response"}
    if response.status_code != 200 or data.get("error") or not data.get("grade"):
        return {"grade": "", "error": str(data.get("message") or data.get("error") or f"Mozilla returned HTTP {response.status_code}")[:160]}
    details = str(data.get("details_url") or "")
    if not details.startswith("https://developer.mozilla.org/"):
        details = f"https://developer.mozilla.org/en-US/observatory/analyze?host={quote(hostname)}"
    return {"grade": str(data["grade"])[:3], "score": data.get("score"), "details_url": details,
            "scanned_at": str(data.get("scanned_at") or "")[:10], "error": ""}


def attach_mozilla_grades(host_security: dict, pause: float = 1.0, fetch=None, sleep_func=None) -> None:
    """One request at a time, because this is a shared public service."""
    fetch = fetch or fetch_mozilla_grade
    sleep_func = sleep_func or time.sleep
    for index, (host, checks) in enumerate(sorted(host_security.items())):
        if index:
            sleep_func(pause)
        checks["mozilla"] = fetch(host)


def host_findings(tls: dict, txt_state: str, redirect: dict = None) -> list:
    out = []
    state = (redirect or {}).get("state")
    if state == "none":
        out.append(make_finding("http-no-redirect", redirect.get("detail", "")))
    elif state == "indirect":
        out.append(make_finding("http-redirect-indirect", redirect.get("detail", "")))
    if tls["error_kind"] == "verify":
        out.append(make_finding("tls-expired" if "expired" in tls["error"].lower() else "tls-invalid", tls["error"]))
    elif tls["error_kind"] == "blocked":
        # A blocked private target is not a TLS weakness; the check was intentionally skipped.
        pass
    elif tls["days_left"] is not None:
        d = tls["days_left"]
        detail = f"Expires {tls['not_after']} ({d} days); issuer {tls['issuer'] or 'unknown'}; {tls['version']}"
        fid = "tls-expired" if d < 0 else "tls-expiring-14" if d < 14 else "tls-expiring-30" if d < 30 else "tls-ok"
        out.append(make_finding(fid, detail))
    if txt_state == "missing":
        out.append(make_finding("security-txt-missing"))
    return out


def run_host_checks(targets: list, timeout: float = 8.0, request_budget=None) -> dict:
    def one(host):
        remaining = request_budget.remaining_seconds() if request_budget is not None else timeout
        if remaining <= 0:
            tls = {"host": host, "days_left": None, "not_after": "", "issuer": "", "version": "",
                   "error_kind": "blocked", "error": "Scan time limit reached before TLS check"}
        else:
            tls = check_tls(host, min(timeout, remaining), request_budget=request_budget)
        state, note = check_security_txt(host, request_budget=request_budget)
        redirect = check_http_redirect(host, min(timeout, 8.0), request_budget=request_budget)
        return host, {"tls": tls, "security_txt": state, "security_txt_note": note, "redirect": redirect,
                      "findings": host_findings(tls, state, redirect)}
    if not targets:
        return {}
    with ThreadPoolExecutor(max_workers=min(6, len(targets))) as pool:
        return dict(pool.map(one, targets))


# ---------------------------------------------------------------------------
# Grouping, CSV and the HTML scan report
# ---------------------------------------------------------------------------

def group_findings(results: list, host_security: dict) -> list:
    """One entry per finding type, with every page (or site) it affects."""
    groups = {}

    def add(f, where, scope):
        g = groups.setdefault(f["id"], {**{k: f[k] for k in ("id", "severity", "title", "fix", "theme", "business", "how")},
                                        "scope": scope, "items": []})
        g["items"].append((where, f["detail"]))

    for r in results:
        for f in (r.get("_security") or []):
            add(f, r["URL"], "Page")
    for host, hs in (host_security or {}).items():
        for f in hs["findings"]:
            add(f, host, "Site")
    return sorted(groups.values(), key=lambda g: (SEVERITY_ORDER[g["severity"]], -len(g["items"]), g["title"]))


def findings_csv(results: list, host_security: dict) -> str:
    out = io.StringIO()
    rows = [["Site", "Scope", "Severity", "Finding", "Affected", "Detail", "Recommendation"]]
    for g in group_findings(results, host_security):
        for where, detail in g["items"]:
            site = key_host_of(where if "://" in where else f"https://{where}/")
            rows.append([site, g["scope"], g["severity"], g["title"], where, detail, g["fix"]])
    pd.DataFrame(rows[1:], columns=rows[0]).to_csv(out, index=False)
    return out.getvalue()


def build_report_html(results: list, info: dict, host_security: dict, branding: dict = None) -> str:
    """A self-contained, printable report. Every dynamic value is escaped, because
    URLs, headers and error text all come from the sites being scanned."""
    e = html_escape
    branding = branding or {}
    n_total = len(results)
    up = [r for r in results if r["Status"] == "Up"]
    down = [r for r in results if r["Status"] == "Down"]
    skipped = [r for r in results if r["Status"] == "Skipped"]
    unconfirmed = [r for r in results if r["Status"] in UNCONFIRMED_STATUSES]
    server_errors = [r for r in results if r["Status"] == "Degraded"]
    recovered = [r for r in results if r.get("_server_error_recovered")]
    avg_rt = (sum(r["Response Time (ms)"] for r in up if r.get("Response Time (ms)") is not None) /
              max(1, len([r for r in up if r.get("Response Time (ms)") is not None]))) if up else None
    groups = group_findings(results, host_security)
    sev_counts = {s: sum(1 for g in groups if g["severity"] == s) for s in ("High", "Medium", "Low")}
    cov = coverage_stats(results)
    analysis_states = {}
    for r in results:
        if r.get("Link Type") != "External" and r["Status"] != "Skipped":
            state = r.get("Security Analysis") or "Not recorded"
            analysis_states[state] = analysis_states.get(state, 0) + 1
    browser_n = sum(1 for r in results if r.get("_browser_used"))
    stealth_n = sum(1 for r in results if r.get("_stealth_used"))

    def row(cells):
        return "<tr>" + "".join(f"<td>{c}</td>" for c in cells) + "</tr>"

    detail_rows = [
        ("Scan type", {"crawl": "Site crawl", "quick": "Quick health check"}.get(info.get("mode"), "CSV list of URLs")),
        ("Target", info.get("target", "")),
        ("Started", info.get("started", "")),
        ("Finished", info.get("finished", "")),
        ("Engine version", info.get("engine_version", "11a")),
        ("Response-size cap", f"{info.get('max_response_bytes', MAX_RESPONSE_BYTES):,} bytes"),
        ("Redirect cap", info.get("max_redirects", MAX_REDIRECTS)),
    ]
    if info.get("mode") == "crawl":
        detail_rows += [("Crawl limits", f"up to {info.get('max_pages')} pages, depth {info.get('max_depth')}"),
                        ("External links checked", "yes (link status only, never crawled)" if info.get("include_external") else "no")]
    if info.get("key_hosts"):
        detail_rows += [("Crawler key", "used for: " + ", ".join(info["key_hosts"]) + " (the key itself is never recorded)"),
                        ("User-Agent with key", info.get("user_agent", "")),
                        ("Rate cap", f"{info.get('rps')} request(s) per second per site"),
                        ("robots.txt", "obeyed, including Crawl-delay"),
                        ("Paths never requested", ", ".join(info.get("blocked_paths") or []) or "none")]
    if info.get("one_site_at_a_time"):
        detail_rows.append(("Multi-site pacing", f"one site at a time, at most {MAX_WORKERS_ONE_SITE} parallel checks, {info.get('site_pause', 0)}s between sites"))
    detail_rows.append(("Server error recheck", f"once, about {info.get('server_recheck_seconds', SERVER_RECHECK_SECONDS)} seconds after the first failure"))
    detail_rows += [("Browser double-check of down pages", "on" if info.get("browser_confirm") else "off"),
                    ("Passive security checks", "on" if info.get("security_enabled") else "off")]

    sev_class = {"High": "high", "Medium": "med", "Low": "low", "Info": "info"}
    sec_rows = []
    for g in groups:
        if g["severity"] == "Info" and g["id"] in ("tls-ok",):
            continue
        shown = "".join(f"<li>{e(str(w))}{(' <span class=muted>(' + e(d) + ')</span>') if d else ''}</li>" for w, d in g["items"][:25])
        more = f"<li class=muted>+{len(g['items']) - 25} more (see the findings CSV)</li>" if len(g["items"]) > 25 else ""
        sec_rows.append(row([f"<span class='badge {sev_class[g['severity']]}'>{e(g['severity'])}</span>",
                             f"<b>{e(g['title'])}</b><br><span class=muted>{e(g['fix'])}</span><br><span class=muted><i>How we check:</i> {e(g['how'])}</span>",
                             f"{len(g['items'])} {'site' if g['scope'] == 'Site' else 'page'}(s)",
                             f"<ul>{shown}{more}</ul>"]))

    host_rows = []
    for host, hs in sorted((host_security or {}).items()):
        t = hs["tls"]
        if t["error_kind"] == "verify":
            tls_txt = f"Verification failed: {e(t['error'])}"
        elif t["days_left"] is not None:
            tls_txt = f"Valid until {e(t['not_after'])} ({t['days_left']} days), issuer {e(t['issuer'] or 'unknown')}, {e(t['version'])}"
        else:
            tls_txt = e(t["error"] or "not checked")
        txt = hs["security_txt"] + (f" ({hs['security_txt_note']})" if hs["security_txt_note"] else "")
        redirect_txt = (hs.get("redirect") or {}).get("detail", "Not checked")
        moz = hs.get("mozilla")
        moz_cells = ([mozilla_text(moz) if moz.get("grade") else e(moz.get("error") or "Not available")] if moz
                     else (["Not requested"] if any(h.get("mozilla") for h in host_security.values()) else []))
        host_rows.append(row([e(host), tls_txt, e(txt), e(redirect_txt)] + moz_cells))

    down_rows = [row([e(r["URL"]), e(str(r.get("Link Type", ""))), e(str(r.get("Found On", ""))),
                      e(str(r.get("Status Code") or "")), e(r.get("Error", ""))]) for r in down]
    skip_reasons = {}
    for r in skipped:
        skip_reasons[r.get("Error", "")] = skip_reasons.get(r.get("Error", ""), 0) + 1
    skip_rows = [row([e(reason), str(count)]) for reason, count in sorted(skip_reasons.items(), key=lambda x: -x[1])]

    css = """
body{font:15px/1.5 -apple-system,Segoe UI,Roboto,Arial,sans-serif;color:#1a1a1a;max-width:1000px;margin:2rem auto;padding:0 1rem}
h1{margin-bottom:.2rem}h2{margin-top:2rem;border-bottom:1px solid #ddd;padding-bottom:.3rem}
.muted{color:#666;font-size:.9em}.cards{display:flex;flex-wrap:wrap;gap:.6rem;margin:1rem 0}
.card{border:1px solid #ddd;border-radius:8px;padding:.6rem 1rem;min-width:110px}.card b{font-size:1.5rem;display:block}
table{border-collapse:collapse;width:100%;margin:.6rem 0}th,td{border:1px solid #ddd;padding:.4rem .6rem;text-align:left;vertical-align:top;word-break:break-word}
th{background:#f5f5f5}ul{margin:0;padding-left:1.1rem}
.badge{padding:.1rem .5rem;border-radius:4px;color:#fff;font-weight:600;font-size:.85em}
.high{background:#b71c1c}.med{background:#e65100}.low{background:#f9a825;color:#222}.info{background:#607d8b}
@media print{body{margin:0}h2{page-break-after:avoid}tr{page-break-inside:avoid}}
"""
    parts = [f"<!doctype html><html lang=en><head><meta charset=utf-8><title>Technical scan report</title><style>{css}</style></head><body>",
             brand_header(branding) + f"<h1>Technical scan report</h1><p class=muted>{e(info.get('target', ''))} &middot; generated {e(info.get('finished', ''))}"
             + (f" &middot; by {e(branding['company'])}" if branding.get("company") else "") + "</p>",
             "<div class=cards>",
             f"<div class=card><b>{n_total}</b>checked</div><div class=card><b>{len(up)}</b>up</div>"
             f"<div class=card><b>{len(down)}</b>down</div><div class=card><b>{len(skipped)}</b>skipped</div>"
             f"<div class=card><b>{'%.0f ms' % avg_rt if avg_rt is not None else 'n/a'}</b>avg response</div></div>"]
    if info.get("security_enabled"):
        parts.append("<div class=cards>"
                     f"<div class=card><b>{sev_counts['High']}</b>high</div><div class=card><b>{sev_counts['Medium']}</b>medium</div>"
                     f"<div class=card><b>{sev_counts['Low']}</b>low</div><div class=card><b>{cov['analyzed']} of {cov['eligible']}</b>pages analyzed</div></div>"
                     "<p class=muted>Counts are of distinct finding types, not of affected pages.</p>")
    parts.append("<h2>Scan details</h2><table>" + "".join(row([f"<b>{e(k)}</b>", e(str(v))]) for k, v in detail_rows) + "</table>")

    parts.append("<h2>Availability</h2>")
    parts.append(("<table><tr><th>URL</th><th>Type</th><th>Found on</th><th>Status</th><th>Error</th></tr>" + "".join(down_rows) + "</table>")
                 if down_rows else "<p>No page or link was confirmed down.</p>")
    if server_errors:
        parts.append(f"<p><b>Server errors</b> ({len(server_errors)}): failed more than once during the scan.</p>"
                     "<table><tr><th>URL</th><th>Status code</th><th>Detail</th></tr>"
                     + "".join(row([e(r["URL"]), e(str(r.get("Status Code") or "")), e(r.get("Error", ""))]) for r in server_errors) + "</table>")
    if recovered:
        parts.append(f"<p><b>Recovered server errors</b> ({len(recovered)}): failed at first, then worked on the delayed recheck. Worth watching if they repeat across scans.</p>"
                     "<table><tr><th>URL</th><th>First status code</th></tr>"
                     + "".join(row([e(r["URL"]), e(str(r["_server_error_recovered"]))]) for r in recovered) + "</table>")
    if unconfirmed:
        parts.append(f"<p><b>Not confirmed</b> ({len(unconfirmed)}): these are neither confirmed working nor confirmed broken.</p>"
                     "<table><tr><th>URL</th><th>Status</th><th>Reason</th></tr>"
                     + "".join(row([e(r["URL"]), e(r["Status"]), e(r.get("Error", ""))]) for r in unconfirmed) + "</table>")
    if skip_rows:
        parts.append("<p><b>Not requested</b> (these were skipped on purpose and are not counted as down):</p>"
                     "<table><tr><th>Reason</th><th>URLs</th></tr>" + "".join(skip_rows) + "</table>")

    if info.get("security_enabled"):
        parts.append("<h2>Security analysis coverage</h2><table><tr><th>Result</th><th>Pages</th></tr>"
                     + "".join(row([e(k), str(v)]) for k, v in sorted(analysis_states.items(), key=lambda x: -x[1])) + "</table>")
        site_names = sorted({r.get("Site") for r in results if r.get("Site") and r.get("Link Type") != "External"})
        if site_names:
            site_rows = []
            for name in site_names:
                site_results = [r for r in results if r.get("Site") == name]
                c = coverage_stats(site_results)
                site_rows.append(row([e(name), str(sum(1 for r in site_results if r["Status"] == "Up")),
                                      str(sum(1 for r in site_results if r["Status"] == "Down")),
                                      str(sum(1 for r in site_results if r["Status"] == "Degraded")),
                                      str(sum(1 for r in site_results if r["Status"] in UNCONFIRMED_STATUSES)),
                                      str(sum(1 for r in site_results if r["Status"] == "Skipped")),
                                      f"{c['analyzed']} of {c['eligible']}"]
                                     + [e(control_short(ids, cookies_only, c)[0]) for _, ids, cookies_only, _ in CONTROL_ROWS]))
            parts.append("<h2>Results by site</h2><table><tr><th>Site</th><th>Up</th><th>Down</th><th>Server errors</th><th>Not confirmed</th>"
                         "<th>Skipped</th><th>Pages analyzed</th>" + "".join(f"<th>{e(c[0])}</th>" for c in CONTROL_ROWS) + "</tr>" + "".join(site_rows) + "</table>")
            parts.append(f"<p class=muted>{e(COVERAGE_INTRO)}</p><ul>"
                         + "".join(f"<li><b>{e(c[0])}:</b> {e(c[3])}</li>" for c in CONTROL_ROWS) + "</ul>")
        parts.append("<h2>Security findings (passive)</h2>")
        parts.append(("<table><tr><th>Severity</th><th>Finding and recommendation</th><th>Affects</th><th>Where</th></tr>" + "".join(sec_rows) + "</table>")
                     if sec_rows else "<p>No findings from the passive checks.</p>")
        if host_rows:
            parts.append("<h2>Site-level checks</h2><table><tr><th>Site</th><th>TLS certificate</th><th>security.txt</th><th>HTTP redirect</th>"
                         + ("<th>Mozilla grade</th>" if any(h.get("mozilla") for h in host_security.values()) else "") + "</tr>" + "".join(host_rows) + "</table>")

    parts.append("<h2>Method and limits</h2><ul>"
                 "<li>Availability is a plain HTTP GET per page, following redirects, with the crawler's rate cap and robots.txt rules applied where a crawler key is used.</li>"
                 "<li>Security checks are <b>passive</b>: they read the response headers and page content of pages that were fetched anyway, plus one TLS handshake, one request for security.txt and one http:// redirect check per site. Nothing is probed, fuzzed, submitted or exploited, and no ports are scanned.</li>"
                 "<li>Checks cover HTTPS use, HSTS, Content-Security-Policy, clickjacking protection, MIME sniffing, referrer and permissions policy, cookie attributes, information disclosure in headers and meta tags, mixed content, insecure forms, directory listings, visible error output, CORS, certificate validity and security.txt.</li>"
                 + (f"<li>{browser_n} page(s) were also opened in a headless browser, which ran their scripts and loaded their assets. Security checks for those pages used the browser's real response headers and the rendered HTML. Crawl rules covered the page requested; its assets and browser-followed redirects were not rate limited.</li>" if browser_n else "")
                 + (f"<li>{stealth_n} page(s) were retried with a browser configured to hide automation signals. This was manually selected and is not used on scan targets.</li>" if stealth_n else "")
                 + f"<li>{'Other pages were' if browser_n else 'Pages are'} not rendered, JavaScript {'was' if browser_n else 'is'} not executed, and nothing behind a login is seen. A clean report is not proof of security and this is not a penetration test.</li>"
                 "<li>Cookie names are reported, never their values. The crawler key is never included.</li></ul>")
    if brand_footer(branding):
        parts.append(f"<p class=muted style='margin-top:2rem;border-top:1px solid #ddd;padding-top:.7rem'>{brand_footer(branding)}</p>")
    parts.append("</body></html>")
    return "".join(parts)


# ---------------------------------------------------------------------------
# Client snapshot (the free review) and the "what we check" handout
# ---------------------------------------------------------------------------
# The technical report above is for IT teams. The snapshot is written for the
# business owner: an overall rating, the few things to do first, what is already
# working, and what each finding means in plain language. Everything it says about
# how the scan was conducted is taken from what actually happened in that scan.

DEFAULT_CTA = ("This snapshot is a free, non-intrusive review of what your website shows every visitor. "
               "If you would like help prioritising or fixing any of the items above, or a deeper review, "
               "please let us know.")
THEME_ORDER = ["private", "browser", "sessions", "exposure", "sharing", "certificate", "contact", "other"]

# (what to say when it passes, finding ids that would fail it, when the rule applies)
PASS_RULES = [
    ("Pages are delivered over a secure (HTTPS) connection", ["plain-http"], "always"),
    ("Browsers are told to always use the secure version of the site (HSTS)", ["hsts-missing", "hsts-short"], "https"),
    ("A Content-Security-Policy limits where page content can load from", ["csp-missing", "csp-report-only", "csp-unsafe"], "always"),
    ("The site is protected against clickjacking", ["clickjacking"], "always"),
    ("Browsers are stopped from guessing file types", ["nosniff-missing"], "always"),
    ("A referrer policy limits what is shared when visitors click away", ["referrer-policy-missing"], "always"),
    ("Server and software versions are not advertised", ["server-version", "powered-by", "generator-version"], "always"),
    ("Cookies are set with protective attributes", ["cookie-no-secure", "cookie-no-httponly", "cookie-no-samesite", "cookie-samesite-none-insecure"], "cookies"),
    ("Secure pages load all of their content securely", ["mixed-active", "mixed-passive", "form-http"], "https_html"),
    ("No directory listings or error messages are visible", ["dir-listing", "error-output"], "html"),
    ("The site does not over-share data with other websites", ["cors-credentials-wildcard"], "always"),
]


def _applies(kind: str, meta: dict) -> bool:
    return {"always": True, "https": bool(meta.get("https")), "cookies": meta.get("cookies", 0) > 0,
            "html": bool(meta.get("html")), "https_html": bool(meta.get("https") and meta.get("html"))}[kind]


def analyzed_pages(results: list) -> list:
    """Pages the passive checks actually saw (a bot-challenge page does not count)."""
    return [r for r in results if r.get("_security") is not None and not (r.get("_security_meta") or {}).get("challenge")]


def passed_checks(results: list, host_security: dict) -> list:
    """What is working: a check passes only if it applied and was clean on every page it applied to."""
    pages = analyzed_pages(results)
    out = []
    for label, fail_ids, kind in PASS_RULES:
        scope = [r for r in pages if _applies(kind, r.get("_security_meta") or {})]
        if scope and not any(f["id"] in fail_ids for r in scope for f in r["_security"]):
            out.append(f"{label} ({len(scope)} page{'s' if len(scope) != 1 else ''} checked)")
    for host, hs in sorted((host_security or {}).items()):
        tls = hs["tls"]
        if tls.get("days_left") is not None and tls["days_left"] >= 30 and not tls.get("error_kind"):
            out.append(f"The security certificate for {host} is valid ({tls['days_left']} days remaining)")
        if hs["security_txt"] == "present":
            out.append(f"A security contact is published for {host} (security.txt)")
    return out


def coverage_stats(results: list) -> dict:
    """How much of a scan the passive checks really saw. Only requested site pages count."""
    eligible = [r for r in results if r.get("Link Type") != "External" and r["Status"] != "Skipped"]
    analyzed = analyzed_pages(eligible)
    return {"eligible": len(eligible), "analyzed": len(analyzed), "pages": analyzed,
            "share": (len(analyzed) / len(eligible)) if eligible else 0.0}


def overall_rating(groups: list, coverage: dict) -> tuple:
    """(label, css class, why). The rule is simple and is printed in the report."""
    if coverage["analyzed"] == 0:
        return "Not assessed", "na", "No pages could be analyzed, so no rating is given. Any items listed still apply."
    if coverage["share"] < MIN_RATING_COVERAGE:
        return ("Not assessed", "na", f"Only {coverage['analyzed']} of {coverage['eligible']} pages could be analyzed, "
                "which is too few for a rating. Any items listed still apply.")
    issues = [g for g in groups if g["severity"] != "Info"]
    if any(g["severity"] == "High" for g in issues):
        return "Needs attention", "high", "At least one high-priority item should be fixed soon."
    if any(g["severity"] == "Medium" for g in issues):
        return "Room to improve", "med", "No urgent items, but there are real gaps worth planning to close."
    return "Strong", "good", "Only minor, good-practice improvements remain."


FUSIONWORKS_NAME = "FusionWorks AI"
DEFAULT_LOGO_URI = "data:image/png;base64,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"  # FusionWorks logo, so reports are branded with no setup
LOGO_TYPES = {"png": "image/png", "jpg": "image/jpeg", "jpeg": "image/jpeg", "webp": "image/webp", "svg": "image/svg+xml"}
MAX_LOGO_BYTES = 1_000_000


def logo_data_uri(data: bytes, extension: str) -> str:
    """The logo as a data URI, so each report stays one self-contained file. Returns "" if the
    file is not really an image of that type. An <img> never runs scripts inside an SVG."""
    extension = (extension or "").lower().lstrip(".")
    if extension not in LOGO_TYPES or not data or len(data) > MAX_LOGO_BYTES:
        return ""
    valid = {"png": data[:8] == b"\x89PNG\r\n\x1a\n", "jpg": data[:3] == b"\xff\xd8\xff", "jpeg": data[:3] == b"\xff\xd8\xff",
             "webp": data[:4] == b"RIFF" and data[8:12] == b"WEBP", "svg": b"<svg" in data[:4000].lower()}
    if not valid[extension]:
        return ""
    return f"data:{LOGO_TYPES[extension]};base64,{base64.b64encode(data).decode('ascii')}"


def saved_logo_candidates() -> list:
    configured = os.environ.get("UPTIME_REPORT_LOGO", "").strip()
    return ([configured] if configured else []) + [os.path.join(_APP_DIR, f"report_logo.{ext}") for ext in LOGO_TYPES]


def load_saved_logo() -> str:
    for path in saved_logo_candidates():
        try:
            with open(path, "rb") as f:
                uri = logo_data_uri(f.read(MAX_LOGO_BYTES + 1), os.path.splitext(path)[1])
            if uri:
                return uri
        except OSError:
            continue
    return ""


def save_logo(data: bytes, extension: str) -> bool:
    """Keep the uploaded logo beside the app so later sessions and timed scans use it."""
    extension = extension.lower().lstrip(".")
    try:
        for ext in LOGO_TYPES:
            path = os.path.join(_APP_DIR, f"report_logo.{ext}")
            if ext != extension and os.path.exists(path):
                os.remove(path)
        with open(os.path.join(_APP_DIR, f"report_logo.{extension}"), "wb") as f:
            f.write(data)
        return True
    except OSError:
        return False


BRAND_CHOICES = {"fusionworks": "FusionWorks AI", "custom": "Custom name"}


def brand_choice_path() -> str:
    return os.path.join(_APP_DIR, "report_logo_choice.txt")


def brand_name_path() -> str:
    return os.path.join(_APP_DIR, "report_brand_name.txt")


def load_brand_choice() -> str:
    """The saved choice. "none" and "custom" from earlier versions both become Custom name."""
    try:
        with open(brand_choice_path(), encoding="utf-8") as f:
            choice = f.read().strip()
        if choice in BRAND_CHOICES:
            return choice
        if choice == "none":
            return "custom"
    except OSError:
        pass
    return "custom" if load_saved_logo() else "fusionworks"


def save_brand_choice(choice: str) -> bool:
    try:
        with open(brand_choice_path(), "w", encoding="utf-8") as f:
            f.write(choice)
        return True
    except OSError:
        return False


def load_brand_name(default: str = "") -> str:
    try:
        with open(brand_name_path(), encoding="utf-8") as f:
            return f.read().strip()[:80]
    except OSError:
        return default


def save_brand_name(name: str) -> bool:
    try:
        with open(brand_name_path(), "w", encoding="utf-8") as f:
            f.write(name.strip()[:80])
        return True
    except OSError:
        return False


def remove_saved_logo() -> None:
    for ext in LOGO_TYPES:
        try:
            os.remove(os.path.join(_APP_DIR, f"report_logo.{ext}"))
        except OSError:
            pass


def resolve_branding(choice: str, name: str = "", cta: str = "", uploaded: str = "", saved: str = "") -> dict:
    """Everything a report says about who prepared it. There is one source for the name, so the
    two options cannot mix, and a blank custom name means reports carry no branding at all."""
    if choice == "fusionworks":
        return {"company": FUSIONWORKS_NAME, "logo_data": DEFAULT_LOGO_URI, "cta": cta, "accent": True}
    return {"company": str(name or "").strip()[:80], "logo_data": uploaded or saved, "cta": cta, "accent": False}


def report_css(branding: dict) -> str:
    """The blue headings are FusionWorks branding, so other reports use a neutral grey."""
    return SNAPSHOT_CSS if (branding or {}).get("accent") else SNAPSHOT_CSS.replace("#034cfb", "#d0d0d0")


def brand_header(branding: dict) -> str:
    """The logo when there is one, otherwise the company name. Styled inline for every report."""
    company = html_escape(branding.get("company", ""))
    if branding.get("logo_data"):
        return (f"<div style='margin-bottom:1.1rem'><img src=\"{html_escape(branding['logo_data'])}\" alt=\"{company}\" "
                "style='max-height:64px;max-width:300px;height:auto;width:auto'></div>")
    if company:
        return ("<div style='font-size:2rem;line-height:1.2;font-weight:800;letter-spacing:.01em;color:#1f3a5f;"
                f"padding-bottom:.55rem;margin-bottom:1.1rem;border-bottom:3px solid #1f3a5f;overflow-wrap:anywhere'>{company}</div>")
    return ""


def brand_footer(branding: dict) -> str:
    company = html_escape((branding or {}).get("company", ""))
    return f"Prepared by {company}" if company else ""


def load_branding_defaults() -> dict:
    """Defaults from [report] in secrets, or UPTIME_REPORT_* environment variables. The company
    value is the starting custom name. Contact details are not used in reports."""
    out = {}
    for key in ("company", "cta"):
        value = ""
        try:
            value = str(st.secrets["report"][key]).strip()
        except Exception:
            pass
        out[key] = value or os.environ.get(f"UPTIME_REPORT_{key.upper()}", "").strip()
    return out


SNAPSHOT_CSS = """
body{font:16px/1.55 -apple-system,Segoe UI,Roboto,Arial,sans-serif;color:#1d1d1f;max-width:900px;margin:2rem auto;padding:0 1.2rem}
h1{margin:.2rem 0}h2{margin-top:2.2rem;border-bottom:2px solid #034cfb;padding-bottom:.3rem}h3{margin-top:1.6rem;color:#333}
.brand{font-weight:700;letter-spacing:.04em;text-transform:uppercase;color:#555;font-size:.85rem}
.muted{color:#666;font-size:.92em}.cards{display:flex;flex-wrap:wrap;gap:.7rem;margin:1rem 0}
.card{border:1px solid #ddd;border-radius:10px;padding:.7rem 1.1rem;min-width:130px}.card b{font-size:1.6rem;display:block}
.rating{border-radius:12px;padding:1rem 1.4rem;color:#fff;margin:1rem 0}.rating b{font-size:1.8rem;display:block}
.rating.high{background:#b71c1c}.rating.med{background:#e65100}.rating.good{background:#2e7d32}.rating.na{background:#607d8b}
.badge{padding:.1rem .55rem;border-radius:4px;color:#fff;font-weight:600;font-size:.82em;white-space:nowrap}
.badge.good{background:#2e7d32}.badge.high{background:#b71c1c}.badge.med{background:#e65100}.badge.low{background:#f9a825;color:#222}.badge.info{background:#607d8b}
.finding{border:1px solid #ddd;border-radius:10px;padding:.8rem 1.1rem;margin:.8rem 0}.finding p{margin:.35rem 0}
.good-list li{margin:.3rem 0}.good-list li::marker{content:"\\2713  ";color:#2e7d32}
table{border-collapse:collapse;width:100%;margin:.6rem 0;font-size:.93em}th,td{border:1px solid #ddd;padding:.45rem .6rem;text-align:left;vertical-align:top;word-break:break-word}
th{background:#f5f5f5}.cta{background:#f4f8ff;border:1px solid #cfe0ff;border-radius:12px;padding:1rem 1.4rem;margin-top:1.5rem}
footer{margin-top:2.5rem;font-size:.85rem;color:#666;border-top:1px solid #ddd;padding-top:.8rem}
@media print{body{margin:0}h2{page-break-after:avoid}.finding,tr{page-break-inside:avoid}}
"""


def _checks_table() -> str:
    """Every check, grouped by theme: what it means and how it is done."""
    e = html_escape
    parts = []
    for theme in THEME_ORDER:
        rows = [(fid, d) for fid, d in FINDINGS.items()
                if d["theme"] == theme and fid not in ("challenge-page", "tls-ok")]
        if not rows:
            continue
        parts.append(f"<h3>{e(THEMES[theme])}</h3><table><tr><th>Check</th><th>Rating</th><th>Why it matters</th><th>How we check</th></tr>")
        cls = {"High": "high", "Medium": "med", "Low": "low", "Info": "info"}
        for _fid, d in rows:
            parts.append(f"<tr><td><b>{e(d['title'])}</b></td><td><span class='badge {cls[d['severity']]}'>{e(d['severity'])}</span></td>"
                         f"<td>{e(d['business'])}</td><td>{e(d['how'])}</td></tr>")
        parts.append("</table>")
    return "".join(parts)


RATING_RANK = {"Needs attention": 0, "Room to improve": 1, "Not assessed": 2, "Strong": 3}
RATING_CLASS = {"Needs attention": "high", "Room to improve": "med", "Not assessed": "info", "Strong": "good"}
REFUSED_STATUSES = ("Blocked", "Restricted", "Challenged")
SEVERITY_CLASS = {"High": "high", "Medium": "med", "Low": "low", "Info": "info"}
CONTROL_ROWS = [
    ("Content-Security-Policy", ("csp-missing", "csp-report-only", "csp-unsafe"), False,
     "Review the enforced CSP on the homepage and important application pages; test changes in report-only mode before enforcement."),
    ("Clickjacking protection", ("clickjacking",), False,
     "Confirm each relevant response has X-Frame-Options or a CSP frame-ancestors directive, including redirect destinations."),
    ("Cookie attributes", ("cookie-no-secure", "cookie-no-httponly", "cookie-no-samesite", "cookie-samesite-none-insecure"), True,
     "Review every Set-Cookie response, including redirects and login/session endpoints. Use Secure on HTTPS cookies, HttpOnly where JavaScript access is unnecessary, and an appropriate SameSite value."),
]
COVERAGE_INTRO = ("No finding is not the same as a confirmed pass. This snapshot summarizes the responses assessed by this passive scan. "
                  "It does not guarantee that every redirect hop or every cookie-setting endpoint was separately examined; "
                  "verify these controls directly before treating them as passed.")


def count_word(k: int, word: str) -> str:
    plural = word + ("es" if word.endswith("s") else "s")
    return f"{k} {word if k == 1 else plural}"


def client_view(results: list, host_security: dict) -> dict:
    """Everything the client report states about one site or one set of pages."""
    groups = group_findings(results, host_security)
    issues = [g for g in groups if g["severity"] in ("High", "Medium")]
    issues = [g for g in issues if g["id"] != "tls-ok"]
    coverage = coverage_stats(results)
    rating, rcls, rwhy = overall_rating(issues, coverage)
    pages = [r for r in results if r.get("Link Type") != "External"]
    checked = [r for r in pages if r["Status"] != "Skipped"]
    up = [r for r in checked if r["Status"] == "Up"]
    # Normal auto-renewing certificates can sit under 90 days for life, so the date is shown
    # for information and only the scanner's own 30 and 14 day findings raise an alert.
    tls_valid = [hs.get("tls") or {} for hs in (host_security or {}).values()]
    tls_valid = sorted((t for t in tls_valid if t.get("days_left") is not None), key=lambda t: t["days_left"])
    return {
        "groups": groups, "issues": issues, "coverage": coverage, "rating": rating, "rcls": rcls, "rwhy": rwhy,
        "n": {s: sum(1 for g in issues if g["severity"] == s) for s in ("High", "Medium", "Low")},
        "checked": checked, "up": up,
        "broken": [r for r in results if r["Status"] == "Down"],
        "server_errors": [r for r in results if r["Status"] == "Degraded"],
        "unconfirmed": [r for r in results if r["Status"] in UNCONFIRMED_STATUSES],
        "challenged": sum(1 for r in checked if r["Status"] == "Challenged"),
        "skipped": [r for r in results if r["Status"] == "Skipped"],
        "external": sum(1 for r in results if r.get("Link Type") == "External"),
        "pct": f"{round(100 * len(up) / len(checked))}%" if checked else "n/a",
        "tls_days": tls_valid[0]["days_left"] if tls_valid else None,
        "tls_expiry": tls_valid[0].get("not_after", "") if tls_valid else "",
        "mozilla": next((hs["mozilla"] for hs in (host_security or {}).values() if hs.get("mozilla")), None),
    }


def _render_how_we_checked(results: list, info: dict) -> str:
    """Every statement here depends on what this scan actually did."""
    e = html_escape
    browser_n = sum(1 for r in results if r.get("_browser_used"))
    stealth_n = sum(1 for r in results if r.get("_stealth_used"))
    out = ["<h2>How we checked</h2><ul>"
           "<li>We only read what the website already shows every visitor: page headers, page content, the public security certificate, two standard files (robots.txt and security.txt), and whether the site's http:// address leads to https://.</li>"
           "<li>We did not log in, submit any form, guess any address, or try to break anything. Every request was a simple read.</li>"]
    if info.get("mode") == "crawl" or (info.get("mode") == "csv" and info.get("max_depth")):
        out.append(f"<li>We followed each site's own links, up to {e(str(info.get('max_pages', '')))} pages per site. There may be more pages than we reviewed.</li>")
    if info.get("key_hosts"):
        out.append("<li>This review followed the crawl rules agreed with the site owner: an identified crawler, a limit on request rate, and respect for the site's robots.txt.</li>")
    if browser_n:
        out.append(f"<li>{count_word(browser_n, 'page')} that a plain request could not read or confirm {'was' if browser_n == 1 else 'were'} also opened in an automated browser, "
                   "which runs the page's scripts and loads its images. Security checks for those pages used the response the browser received and the page after its scripts ran. "
                   "The crawl rules applied to each page opened. The files that page then loaded were requested by the browser, outside those rate limits.</li>")
    rechecked = sum(1 for r in results if str(r.get("Server Error Check", "")).startswith(("Recovered", "Failed", "Inconclusive")))
    if rechecked:
        out.append(f"<li>{count_word(rechecked, 'page')} with a server error {'was' if rechecked == 1 else 'were'} checked again after a short delay. Pages that recovered are not listed as problems.</li>")
    if info.get("mozilla_grades"):
        out.append("<li>Mozilla grades come from Mozilla HTTP Observatory, a separate public service. Its scanner visits each site itself, outside the crawl rules above, and its scan history is public.</li>")
    if stealth_n:
        out.append(f"<li>{count_word(stealth_n, 'link')} to other websites {'was' if stealth_n == 1 else 'were'} retried using a browser configured to appear less automated.</li>")
    out.append(f"<li>{'Other than that, we' if browser_n else 'We'} did not display pages or run their scripts, and we cannot see anything behind a login. A clean result is not proof of security, and this is not a penetration test.</li>"
               "<li><b>How we rate:</b> <i>Needs attention</i> means at least one high-priority item; <i>Room to improve</i> means no high-priority items but at least one medium; "
               f"<i>Strong</i> means only minor improvements remain; <i>Not assessed</i> means the security checks reached fewer than {round(MIN_RATING_COVERAGE * 100)}% of requested pages.</li></ul>")
    return "".join(out)


def _render_next_steps(branding: dict) -> str:
    e = html_escape
    out = ["<h2>Next steps</h2><div class=cta>"]
    cta = branding.get("cta") or DEFAULT_CTA
    out.append("".join(f"<p>{e(line)}</p>" for line in cta.splitlines() if line.strip()))
    if branding.get("company"):
        out.append(f"<p><b>{e(branding['company'])}</b></p>")
    out.append("</div>")
    return "".join(out)


def _render_skipped(skipped: list) -> str:
    if not skipped:
        return ""
    k = len(skipped)
    return f"<p class=muted>{count_word(k, 'address')} {'was' if k == 1 else 'were'} deliberately not requested, so {'it is' if k == 1 else 'they are'} not part of this review.</p>"


def client_report_sites(results: list, host_security: dict, info: dict) -> dict:
    """Split one scan by site: {site: (rows, host checks)}. www and non-www are one site, and a
    site that was listed but never reached still appears, so a gap cannot pass unnoticed."""
    sites = {}
    for name in (info.get("sites") or []):
        key = key_host_of(f"https://{name}/")
        if key:
            sites.setdefault(key, ([], {}))
    for r in results:
        if r.get("Link Type") == "External" or not str(r.get("URL") or "").strip():
            continue
        key = r.get("Site") or key_host_of(normalize_url(r["URL"]))
        sites.setdefault(key, ([], {}))[0].append(r)
    for host, hs in (host_security or {}).items():
        key = key_host_of(f"https://{host}/")
        sites.setdefault(key, ([], {}))[1][host] = hs
    return sites


def problem_label(r: dict) -> str:
    """A client-facing name for why a page is not confirmed working."""
    status, code = r["Status"], r.get("Status Code")
    error = str(r.get("Error") or "").lower()
    if status == "Down":
        return {404: "Page not found", 410: "Page removed"}.get(code, f"Error {code}" if code else "Page unavailable")
    if status == "Degraded":
        return "Security certificate error" if "tls" in error else (f"Server error {code}" if code else "Server error")
    if status == "Challenged":
        return "Stopped by bot protection"
    if status == "Blocked":
        return "Automated check refused"
    if status == "Restricted":
        return "Login or access restriction"
    if "delayed recheck did not run" in error:
        return f"Server error {code}, not rechecked" if code else "Server error, not rechecked"
    return "Timed out" if "timed out" in error else "Could not be reached"


def page_label(r: dict) -> str:
    if r.get("Link Type") == "External":
        return str(r["URL"])
    parsed = urlparse(r["URL"])
    path = parsed.path or "/"
    if parsed.query:
        path += "?" + parsed.query
    return "Home page" if path == "/" else path


def link_sources(r: dict) -> list:
    """The pages linking to a result, as short paths. CSV entries have no linking page."""
    sources = []
    for source in str(r.get("Found On") or "").split(";"):
        source = source.strip()
        if source == "(starting page)":
            sources.append("Scan list")
        elif source.startswith(("http://", "https://")):
            sources.append(urlparse(source).path.rstrip("/") or "Home page")
    return sources


def consolidate_pages(rows: list) -> list:
    """Same page and same problem across sites becomes one line, largest first."""
    groups = {}
    for r in rows:
        key = (page_label(r), problem_label(r))
        site = "Link to another website" if r.get("Link Type") == "External" else (r.get("Site") or key_host_of(r["URL"]))
        group = groups.setdefault(key, {"sites": set(), "sources": set()})
        group["sites"].add(site)
        group["sources"].update(link_sources(r))
    return sorted(({"page": k[0], "problem": k[1], "sites": sorted(v["sites"]), "sources": sorted(v["sources"])}
                   for k, v in groups.items()),
                  key=lambda g: (-len(g["sites"]), g["problem"], g["page"]))


def sources_text(sources: list) -> str:
    if not sources:
        return "Not recorded"
    # The home page is the most useful place to start fixing a link, so it comes first.
    ordered = sorted(sources, key=lambda x: (x != "Home page", x))
    return ", ".join(ordered[:3]) + (f" and {len(ordered) - 3} more" if len(ordered) > 3 else "")


def sites_text(names: list, total: int) -> str:
    if total > 1 and len(names) >= total:
        return "Both sites" if total == 2 else f"All {total} sites"
    shown = ", ".join(names[:3])
    return f"{shown} and {len(names) - 3} more" if len(names) > 3 else shown


def _render_page_table(groups: list, total_sites: int, show_sources: bool = False) -> str:
    e = html_escape
    show_sites = total_sites > 1
    head = ("<table><tr><th>Page</th><th>Problem</th>" + ("<th>Sites</th>" if show_sites else "")
            + ("<th>Linked from</th>" if show_sources else "") + "</tr>")
    rows = []
    for g in groups[:SNAPSHOT_MAX_ROWS]:
        rows.append(f"<tr><td>{e(g['page'])}</td><td>{e(g['problem'])}</td>"
                    + (f"<td>{e(sites_text(g['sites'], total_sites))}</td>" if show_sites else "")
                    + (f"<td>{e(sources_text(g['sources']))}</td>" if show_sources else "") + "</tr>")
    more = len(groups) - SNAPSHOT_MAX_ROWS
    note = f"<p class=muted>+{more} more in the technical report.</p>" if more > 0 else ""
    return head + "".join(rows) + "</table>" + note


def build_recommendations(views: dict) -> list:
    """Findings and availability actions as one priority list. Each states the action and why."""
    recs = {}
    for name, v in views.items():
        for g in v["issues"]:
            rec = recs.setdefault(g["id"], {"title": g["title"], "severity": g["severity"], "fix": g["fix"],
                                            "why": g["business"], "sites": [], "pages": 0, "details": []})
            rec["sites"].append(name)
            if g["scope"] == "Page":
                rec["pages"] += len(g["items"])
            else:
                rec["details"] += [str(d).split(";")[0] + (f" ({where})" if len(views) > 1 else "") for where, d in g["items"] if d]
    recs = list(recs.values())

    def add(title, severity, fix, why, rows=None, names=None):
        recs.append({"title": title, "severity": severity, "fix": fix, "why": why, "pages": len(rows or []),
                     "sites": names if names is not None else sorted({r.get("Site") or key_host_of(r["URL"]) for r in rows})})

    down = [r for v in views.values() for r in v["broken"]]
    server = [r for v in views.values() for r in v["server_errors"]]
    review = [r for v in views.values() for r in v["unconfirmed"]]
    incomplete = sorted(name for name, v in views.items() if v["rating"] == "Not assessed")
    if down:
        home_down = any(page_label(r) == "Home page" for r in down)
        add(f"{count_word(len(down), 'broken page')}", "High" if home_down else "Medium",
            "Restore each page listed above, or redirect it to the closest working page, and update any links pointing to it.",
            "Visitors who reach these pages hit a dead end, which loses enquiries and can reduce search visibility.", rows=down)
    if server:
        home_error = any(page_label(r) == "Home page" for r in server)
        add(f"{count_word(len(server), 'page')} with repeated server errors", "High" if home_error else "Medium",
            "Check the application logs and, where a load balancer is used, its target health. Fix the cause, then recheck these pages.",
            "These pages failed more than once during the review. Server errors stop visitors using a page and can be an early sign of a wider fault.", rows=server)
    if incomplete:
        add(f"Security review incomplete on {count_word(len(incomplete), 'site')}", "Medium",
            "Allow the agreed crawler through each site's bot protection, then rerun the review.",
            f"These sites have no security rating because under {round(MIN_RATING_COVERAGE * 100)}% of their pages could be checked, so unknown gaps may remain.",
            names=incomplete)
    if review:
        add(f"{count_word(len(review), 'page')} could not be confirmed", "Low",
            "Open each page from a normal browser and network. If visitors are blocked, adjust the bot-protection rule. "
            "If they are not, allow the agreed crawler so the next review can confirm them.",
            "The automated check could not tell whether these pages work, and a block that also affects customers would cost enquiries.", rows=review)
    return sorted(recs, key=lambda rec: (SEVERITY_ORDER[rec["severity"]], -len(rec["sites"]), rec["title"]))


def mozilla_text(result: dict) -> str:
    """Escaped report text for one Mozilla result, always named as Mozilla's."""
    e = html_escape
    score = f", score {e(str(result['score']))}" if result.get("score") is not None else ""
    url = e(result.get("details_url", ""), quote=True)
    label = f"Mozilla HTTP Observatory grade {e(result['grade'])}{score}"
    dated = f" ({e(result['scanned_at'])})" if result.get("scanned_at") else ""
    return (f'<a href="{url}">{label}</a>' if url else label) + dated


def _render_recommendations(recs: list, total_sites: int) -> str:
    e = html_escape
    out = []
    for i, rec in enumerate(recs, 1):
        where = sites_text(rec["sites"], total_sites) if total_sites > 1 else ""
        pages = count_word(rec["pages"], "page") if rec["pages"] else ""
        details = rec.get("details") or []
        affects = " · ".join(x for x in (where if not details else "", pages, "; ".join(details[:3])) if x)
        if len(details) > 3:
            affects += f" and {len(details) - 3} more"
        out.append(f"<div class=finding><p><b>{i}. {e(rec['title'])}</b> <span class='badge {SEVERITY_CLASS[rec['severity']]}'>{e(rec['severity'])}</span></p>"
                   f"<p><b>Recommendation:</b> {e(rec['fix'])}</p><p><b>Why it matters:</b> {e(rec['why'])}</p>"
                   + (f"<p class=muted><b>Affects:</b> {e(affects)}</p>" if affects else "") + "</div>")
    return "".join(out)


def build_client_report_html(results: list, info: dict, host_security: dict, branding: dict = None) -> str:
    """The presentable view of a scan: what is down, what to do, and why. Page-level detail
    belongs in the technical report. Every dynamic value is escaped. Sites are rated separately,
    so a scan of several sites has no single merged rating."""
    e = html_escape
    branding = branding or {}
    sites = client_report_sites(results, host_security, info)
    views = {name: client_view(rows, hs) for name, (rows, hs) in sites.items()}
    total = len(views)
    single = total <= 1
    date = (info.get("finished") or "")[:10]
    label = info.get("site") or info.get("target", "") if single else (info.get("client_name") or f"{total} websites")
    ordered = sorted(views, key=lambda name: (RATING_RANK[views[name]["rating"]], -views[name]["n"]["High"],
                                              -views[name]["n"]["Medium"], name))
    checked = sum(len(v["checked"]) for v in views.values())
    up = sum(len(v["up"]) for v in views.values())
    analyzed = sum(v["coverage"]["analyzed"] for v in views.values())
    eligible = sum(v["coverage"]["eligible"] for v in views.values())
    external_down = [r for r in results if r.get("Link Type") == "External" and r["Status"] == "Down"]
    down_rows = [r for v in views.values() for r in v["broken"]] + external_down
    server_rows = [r for v in views.values() for r in v["server_errors"]]
    review_rows = [r for v in views.values() for r in v["unconfirmed"]]
    down_sites = {r.get("Site") or key_host_of(r["URL"]) for r in down_rows if r.get("Link Type") != "External"}
    server_sites = {r.get("Site") or key_host_of(r["URL"]) for r in server_rows}
    recs = build_recommendations(views)
    pct = f"{round(100 * up / checked)}%" if checked else "n/a"

    summary = []
    if down_rows:
        verb = "is" if len(down_rows) == 1 else "are"
        summary.append(f"{count_word(len(down_rows), 'page')} {verb} confirmed broken" + ("." if single else f" across {count_word(len(down_sites), 'site')}."))
    else:
        summary.append("No page was confirmed broken.")
    if server_rows:
        summary.append(f"{count_word(len(server_rows), 'page')} failed repeatedly with server errors" + ("." if single else f" on {count_word(len(server_sites), 'site')}."))
    if review_rows:
        summary.append(f"{count_word(len(review_rows), 'more page')} could not be confirmed either way.")
    if not single:
        mix = {r: sum(1 for v in views.values() if v["rating"] == r) for r in RATING_RANK}
        summary.append(f"Security ratings: {mix['Needs attention']} need attention, {mix['Room to improve']} room to improve, "
                       f"{mix['Strong']} strong, {mix['Not assessed']} not assessed.")
    if recs:
        summary.append(f"We recommend {count_word(len(recs), 'action')}, in priority order below.")
    if single and views and views[ordered[0]]["tls_expiry"]:
        v = views[ordered[0]]
        summary.append(f"The security certificate runs until {v['tls_expiry']} ({count_word(v['tls_days'], 'day')} left).")
    smaller = {}
    for v in views.values():
        for g in v["groups"]:
            if g["severity"] == "Low":
                smaller[g["id"]] = g["title"]

    out = [f"<!doctype html><html lang=en><head><meta charset=utf-8><title>Website Health &amp; Security Snapshot: {e(label)}</title>"
           f"<style>{report_css(branding)}.table-wrap{{overflow-x:auto}}.glance{{min-width:800px}}.glance th,.glance td{{word-break:normal;overflow-wrap:normal}}"
           ".glance td:first-child{overflow-wrap:anywhere}.glance .badge{white-space:normal;display:inline-block}.fine{color:#666;font-size:.9em}.card{flex:1;min-width:105px}</style></head><body>"]
    out.append(brand_header(branding))
    out.append(f"<h1>Website Health &amp; Security Snapshot</h1><p class=muted>Prepared for <b>{e(label)}</b> &middot; {e(date)}"
               + (f" &middot; by {e(branding['company'])}" if branding.get("company") else "") + "</p>")
    if single and views:
        v = views[ordered[0]]
        out.append(f"<div class='rating {v['rcls']}'><b>{e(v['rating'])}</b>{e(v['rwhy'])}</div>")
    out.append("<div class=cards>" + (f"<div class=card><b>{total}</b>sites</div>" if not single else "")
               + f"<div class=card><b>{checked}</b>pages reviewed</div><div class=card><b>{pct}</b>confirmed loading</div>"
               f"<div class=card><b>{len(down_rows)}</b>broken pages</div><div class=card><b>{len(server_rows)}</b>server errors</div>"
               f"<div class=card><b>{analyzed} of {eligible}</b>pages security-checked</div></div>")
    out.append("<h2>Summary</h2><p>" + " ".join(summary) + "</p>")
    if single and views and (views[ordered[0]]["mozilla"] or {}).get("grade"):
        out.append(f"<p class=muted><b>Independent grade:</b> {mozilla_text(views[ordered[0]]['mozilla'])}</p>")

    out.append("<h2>What is down</h2>")
    out.append(_render_page_table(consolidate_pages(down_rows), total, show_sources=True) if down_rows else "<p>No page was confirmed broken.</p>")
    if server_rows:
        out.append("<h2>Server errors</h2><p class=muted>These pages failed more than once during the review, so they are more likely a real fault than a brief interruption.</p>"
                   + _render_page_table(consolidate_pages(server_rows), total))
    if review_rows:
        out.append("<h2>Could not be confirmed</h2><p class=muted>These pages refused, challenged or timed out on the automated check. "
                   "That does not show whether visitors can reach them.</p>" + _render_page_table(consolidate_pages(review_rows), total))

    out.append("<h2>Recommendations</h2>")
    out.append(_render_recommendations(recs, total) if recs else "<p>No high or medium priority actions came out of the pages we could check.</p>")

    if smaller:
        names = sorted(smaller.values())
        shown = "; ".join(e(n) for n in names[:6]) + (f"; and {len(names) - 6} more" if len(names) > 6 else "")
        out.append(f"<p><b>Smaller improvements:</b> {count_word(len(names), 'lower-priority item')} also found: {shown}. Details are in the technical report.</p>")

    if not single:
        show_mozilla = any(v["mozilla"] for v in views.values())
        out.append("<h2>Sites at a glance</h2><div class=table-wrap><table class=glance><tr><th>Site</th><th>Security rating</th><th>Pages loading</th>"
                   "<th>Broken</th><th>Server errors</th><th>Not confirmed</th><th>Security-checked</th><th>Certificate expires</th>"
                   + ("<th>Mozilla grade</th>" if show_mozilla else "") + "</tr>")
        for name in ordered:
            v = views[name]
            out.append(f"<tr><td>{e(name)}</td><td><span class='badge {RATING_CLASS[v['rating']]}'>{e(v['rating'])}</span></td>"
                       f"<td>{len(v['up'])} of {len(v['checked'])}</td><td>{len(v['broken'])}</td><td>{len(v['server_errors'])}</td><td>{len(v['unconfirmed'])}</td>"
                       f"<td>{v['coverage']['analyzed']} of {v['coverage']['eligible']}</td><td>{e(v['tls_expiry'] or 'n/a')}</td>"
                       + (f"<td>{e((v['mozilla'] or {}).get('grade') or 'n/a')}</td>" if show_mozilla else "") + "</tr>")
        out.append("</table></div>")

    limits = []
    unreached = [name for name in ordered if not views[name]["checked"]]
    home_only = [name for name in ordered if info.get("max_depth") and len(views[name]["checked"]) == 1]
    if unreached:
        limits.append(f"No pages were checked on {', '.join(e(n) for n in unreached[:5])}{' and others' if len(unreached) > 5 else ''}.")
    if home_only:
        limits.append(f"No links could be read on {count_word(len(home_only), 'site')}, so only the starting page was reviewed.")
    skipped = [r for v in views.values() for r in v["skipped"]]
    out.append("<div class=fine>" + _render_how_we_checked(results, info))
    if limits:
        out.append("<p>" + " ".join(limits) + "</p>")
    out.append(_render_skipped(skipped) + "</div>" + _render_next_steps(branding))
    out.append(f"<footer>This snapshot reflects publicly visible information on {e(date)}. It is a point-in-time, non-intrusive review and "
               "not a guarantee of security. Full page-level detail is in the technical report."
               + (f"<br>{brand_footer(branding)}" if brand_footer(branding) else "") + "</footer></body></html>")
    return "".join(out)


def control_short(ids: tuple, cookies_only: bool, coverage: dict) -> tuple:
    """Compact form of control_status for the by-site table: (text, badge class)."""
    analyzed = coverage["analyzed"]
    if not analyzed:
        return "Not assessed", "info"
    affected = sum(1 for r in coverage["pages"] if any(f["id"] in ids for f in r["_security"]))
    if affected:
        return f"Finding: {affected} of {analyzed} pages", "med"
    if cookies_only and not any((r.get("_security_meta") or {}).get("cookies", 0) > 0 for r in coverage["pages"]):
        return "No cookies seen", "info"
    if analyzed < coverage["eligible"]:
        return f"No finding: {analyzed} of {coverage['eligible']} checked", "info"
    return f"No finding: {analyzed} pages", "good"


def build_checks_reference_html(branding: dict = None) -> str:
    """A standalone handout explaining the checks, usable before any scan is run."""
    branding = branding or {}
    footer = brand_footer(branding)
    return (f"<!doctype html><html lang=en><head><meta charset=utf-8><title>How our website check works</title><style>{report_css(branding)}</style></head><body>"
            + brand_header(branding)
            + "<h1>How our website check works</h1>"
            "<p>A quick, non-intrusive health check of what your website shows every visitor, in the way you would check a shop's door, "
            "signs and locks from the pavement.</p>"
            "<h2>What it is, and what it is not</h2><ul>"
            "<li>It reads only what the website already shows every visitor: page headers, page content, the public security certificate, two standard files (robots.txt and security.txt), and whether the site's http:// address leads to https://.</li>"
            "<li>It does not log in, submit forms, guess addresses or try to break anything. Every request is a simple read.</li>"
            "<li>It is not a penetration test. It does not display pages or run their scripts, and cannot see anything behind a login, so a clean result is not proof of security.</li></ul>"
            "<h2>The checks</h2><p class=muted>Ratings: <b>High</b> fix soon; <b>Medium</b> a real weakness worth planning for; <b>Low</b> good-practice hardening; <b>Info</b> for awareness.</p>"
            + _checks_table()
            + (f"<footer>{footer}</footer>" if footer else "") + "</body></html>")


# ---------------------------------------------------------------------------
# Helpers - checking sites
# ---------------------------------------------------------------------------

def normalize_url(url: str) -> str:
    """Normalize a user-entered URL without silently accepting unsafe schemes."""
    url = str(url or "").strip()
    if not url:
        return ""
    if not re.match(r"^[a-zA-Z][a-zA-Z0-9+.-]*://", url):
        url = "https://" + url
    parsed = urlparse(url)
    if parsed.scheme.lower() not in ("http", "https"):
        raise PolicyBlocked("Blocked: only http:// and https:// URLs are allowed")
    if not parsed.netloc or parsed.username or parsed.password:
        raise PolicyBlocked("Blocked: malformed URL or embedded credentials")
    try:
        _ = parsed.port
    except ValueError:
        raise PolicyBlocked("Blocked: malformed URL port")
    return url


def detect_url_column(df: pd.DataFrame) -> str:
    candidates = ["url", "urls", "website", "websites", "link", "links", "address", "site"]
    for col in df.columns:
        if str(col).strip().lower() in candidates:
            return col
    return df.columns[0]


def check_url(url: str, timeout: float, request_budget=None) -> dict:
    original = url
    result = {
        "URL": original,
        "Status": "Down",
        "Status Code": None,
        "Response Time (ms)": None,
        "Error": "",
        "Crawler Key Diagnostic": "Not evaluated yet",
        "Checked At": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
        "Checked Via": "HTTP",
        "Down Confirmation": "Not applicable",
        "Security Analysis": "Not analyzed: request did not complete",
    }

    if not str(url or "").strip():
        result["Error"] = "Empty URL"
        result["Status"] = "Skipped"
        return result

    try:
        url = normalize_url(url)
        result["Crawler Key Diagnostic"] = (
            f"Configured for HTTPS host: {urlparse(url).hostname or 'unknown'}"
            if url_gets_key(url)
            else "Not configured for this URL (key absent, opt-in off, non-HTTPS, or host not approved)"
        )
        WAIT.total = 0.0
        start = time.perf_counter()
        # Many sites block requests without a browser-like User-Agent (bot/DDoS
        # protection such as Cloudflare), so non-key requests send one to avoid
        # false "down" reads. Key-scoped requests use the identifying User-Agent.
        if request_budget is None:
            resp = http_get(url, timeout)
        else:
            resp = http_get(url, timeout, request_budget=request_budget)
        # Time spent waiting on the rate cap or reading robots.txt is not the site's response time.
        elapsed_ms = max((time.perf_counter() - start - getattr(WAIT, "total", 0.0)) * 1000, 0.0)

        result["Status Code"] = resp.status_code
        hop_diagnostics = getattr(resp, "_crawler_key_diagnostics", [])
        if hop_diagnostics:
            result["Crawler Key Diagnostic"] = " | ".join(hop_diagnostics)
        result["Response Time (ms)"] = round(elapsed_ms, 1)
        code = resp.status_code
        challenged = (200 <= code < 300 or code in (403, 429, 503)) and response_is_challenge(resp)
        if challenged:
            result["Status"] = "Challenged"
            result["Error"] = (f"HTTP {code}: bot-protection challenge returned instead of the page; "
                               "availability and security are unconfirmed")
        elif 200 <= code < 400:
            result["Status"] = "Up"
        elif code in (401, 403):
            result["Status"] = "Restricted"
            result["Error"] = f"HTTP {code}: authentication or access restriction; availability is inconclusive"
        elif code in (405, 429):
            # A persistent 405 proves only that this request was rejected by method/policy;
            # it does not prove the page is missing. Treat it as inconclusive rather than
            # allowing the generic retry confirmer to label it Down after three repeats.
            result["Status"] = "Blocked"
            if code == 405:
                result["Error"] = ("HTTP 405: request method rejected; page availability is inconclusive. "
                                   "The server or an intermediary may be rejecting automated requests.")
            else:
                result["Error"] = "HTTP 429: rate limited; availability is inconclusive"
        elif code >= 500:
            result["Status"] = "Degraded"
            result["Error"] = f"HTTP {code}: server error"
        else:
            result["Status"] = "Down"
            result["Error"] = f"HTTP {code}"
        # Passive security checks, only on the site(s) being scanned (never on external links).
        final_host = key_host_of(resp.url or url)
        security_enabled = (
            request_budget.security_enabled if request_budget is not None
            and request_budget.security_enabled is not None else SECURITY_CONFIG["enabled"]
        )
        security_hosts = (
            request_budget.security_hosts if request_budget is not None
            and request_budget.security_hosts is not None else SECURITY_CONFIG["hosts"]
        )
        if not security_enabled:
            result["Security Analysis"] = "Off"
        elif final_host not in security_hosts:
            result["Security Analysis"] = f"Not analyzed: final host {final_host or 'unknown'} is not a scan target"
        elif challenged:
            result["_security"] = [make_finding("challenge-page")]
            result["_security_meta"] = {"https": (resp.url or "").lower().startswith("https://"),
                                        "html": True, "cookies": 0, "challenge": True}
            result["Security Issues"] = 0
            result["Security Analysis"] = "Not analyzed: bot-protection challenge"
        elif resp.status_code >= 400:
            result["Security Analysis"] = f"Not analyzed: HTTP {resp.status_code}"
        else:
            try:
                findings, meta = _analyze(resp)
                result["_security"] = findings
                result["_security_meta"] = meta
                result["Security Issues"] = sum(1 for f in findings if f["severity"] != "Info")
                result["Security Analysis"] = "Analyzed"
            except Exception as exc:
                # An analysis problem must never turn a healthy page into an error, but it
                # must be visible: reports count these pages as not analyzed.
                result["_security"] = None
                result["Security Analysis"] = f"Not analyzed: analysis error ({type(exc).__name__})"
                logging.getLogger(__name__).exception("Security analysis failed for %s", url)
    except PolicyBlocked as e:
        # Not requested at all (robots.txt, excluded RFQ/contact path, ...), so neither up nor down.
        result["Status"] = "Skipped"
        result["Error"] = str(e)
        result["Checked Via"] = "Not requested"
    except requests.exceptions.Timeout:
        result["Status"] = "Unknown"
        result["Error"] = f"Timed out after {timeout}s; one timeout is not conclusive proof of downtime"
    except requests.exceptions.SSLError:
        result["Status"] = "Degraded"
        result["Error"] = "TLS/SSL error"
    except requests.exceptions.ConnectionError as e:
        result["Status"] = "Unknown"
        result["Error"] = f"Connection failed: {str(e)[:100]}"
    except requests.exceptions.RequestException as e:
        result["Status"] = "Unknown"
        result["Error"] = str(e)[:120]

    return result


def get_chrome_options(stealth: bool = False, user_agent: str = "") -> "ChromeOptions":
    options = ChromeOptions()
    options.add_argument("--headless=new")
    options.add_argument("--no-sandbox")
    options.add_argument("--disable-dev-shm-usage")
    options.add_argument("--disable-gpu")
    options.add_argument("--window-size=1280,800")
    options.add_argument(f"user-agent={user_agent or HEADERS['User-Agent']}")
    # Lets the browser check read the real HTTP status and response headers of the page.
    options.set_capability("goog:loggingPrefs", {"performance": "ALL"})
    if stealth:
        # Hide the more obvious signs that this is an automated browser, and
        # drop Chrome's automation banner/flags that some bot-detection scripts
        # check for directly.
        options.add_argument("--disable-blink-features=AutomationControlled")
        options.add_experimental_option("excludeSwitches", ["enable-automation"])
        options.add_experimental_option("useAutomationExtension", False)
    import os
    for path in ("/usr/bin/chromium", "/usr/bin/chromium-browser"):
        if os.path.exists(path):
            options.binary_location = path
            break
    return options


def url_in_agreed_scope(url: str) -> bool:
    """Hosts the scan's crawl rules apply to: the ones entered for this scan, or given the key."""
    return url_gets_key(url) or key_host_of(url) in set(KEY_CONFIG.get("policy_hosts", []))


def enforce_browser_policy(url: str, request_budget=None) -> str:
    """Apply the crawl rules before a browser opens a URL, because a browser does not pass through
    KeyedSession. Returns the User-Agent to use, or raises PolicyBlocked.
    The first page load is covered. Assets the page then loads, and redirects the browser follows,
    are outside this check, and the reports say so."""
    if request_budget is not None:
        request_budget.consume(1.0)
    if not url_in_agreed_scope(url):
        return HEADERS["User-Agent"]
    session = KeyedSession(request_budget)
    session._enforce_policy(types.SimpleNamespace(method="GET", url=url))
    parsed = urlparse(url)
    rules = ROBOTS_CACHE.get(f"{parsed.scheme}://{parsed.netloc.lower()}")
    crawl_delay = min(rules.crawl_delay, 60.0) if rules else 0.0
    THROTTLE.wait(key_host_of(url), max(1.0 / max(KEY_CONFIG["rps"], 0.01), crawl_delay))
    return KEY_CONFIG["user_agent"]


class BrowserResponse:
    """The page as Chrome received it, shaped like the parts of a requests response that _analyze
    reads. Headers are the real ones. The body is the rendered page, so scripts have already run."""

    def __init__(self, status: int, url: str, headers: dict, cookies: list, html: str):
        self.status_code = status
        self.url = url
        self.headers = requests.structures.CaseInsensitiveDict(headers)
        self.text = html
        self.content = html.encode("utf-8", "replace")
        self.raw = types.SimpleNamespace(headers=types.SimpleNamespace(getlist=lambda name: list(cookies)))


def read_document_response(driver, html: str):
    """Find the top-level page in Chrome's network log. Returns a BrowserResponse, or None when the
    log is unavailable, in which case callers must treat the HTTP status as unknown."""
    try:
        entries = driver.get_log("performance")
    except Exception:
        return None
    top_frame, response, request_id = None, None, None
    extra = {}
    for entry in entries:
        try:
            message = json.loads(entry["message"])["message"]
        except (KeyError, TypeError, ValueError):
            continue
        method, params = message.get("method"), message.get("params") or {}
        if method == "Network.requestWillBeSent" and params.get("type") == "Document" and top_frame is None:
            top_frame = params.get("frameId")
        elif (method == "Network.responseReceived" and params.get("type") == "Document"
              and params.get("frameId") == top_frame):
            response, request_id = params.get("response") or {}, params.get("requestId")
        elif method == "Network.responseReceivedExtraInfo":
            extra[params.get("requestId")] = params.get("headers") or {}
    if not response or not response.get("status"):
        return None
    # Extra info holds the raw headers, including Set-Cookie, which responseReceived can omit.
    headers = {**(response.get("headers") or {}), **extra.get(request_id, {})}
    cookie_text = next((v for k, v in headers.items() if k.lower() == "set-cookie"), "")
    headers.setdefault("Content-Type", response.get("mimeType") or "")
    return BrowserResponse(int(response["status"]), response.get("url") or "", headers,
                           [c for c in str(cookie_text).split("\n") if c.strip()], html)


def apply_security_analysis(result: dict, resp, via: str) -> None:
    """Run the passive checks on a response when its final host is a scan target."""
    final_host = key_host_of(resp.url or result.get("URL") or "")
    if not SECURITY_CONFIG["enabled"] or final_host not in SECURITY_CONFIG["hosts"]:
        return
    try:
        findings, meta = _analyze(resp)
        result["_security"] = findings
        result["_security_meta"] = meta
        result["Security Issues"] = sum(1 for f in findings if f["severity"] != "Info")
        result["Security Analysis"] = via
    except Exception as exc:
        result["_security"] = None
        result["Security Analysis"] = f"Not analyzed: analysis error ({type(exc).__name__})"
        logging.getLogger(__name__).exception("Security analysis failed for %s", result.get("URL"))


BROWSER_BLOCK_MARKERS = ("just a moment", "checking your browser", "attention required", "access denied",
                         "403 forbidden", "human verification")
BROWSER_NOT_FOUND_TITLES = ("404", "page not found", "not found")


def check_url_browser(url: str, timeout: float, request_budget=None) -> dict:
    """Confirm a site's status using a real headless browser (catches JS
    challenges / bot-protection that block plain HTTP requests)."""
    original = url
    result = {
        "URL": original,
        "Status": "Unknown",
        "Status Code": None,
        "Response Time (ms)": None,
        "Error": "",
        "Checked At": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
        "Checked Via": "Browser",
    }

    if not str(url or "").strip():
        result["Status"] = "Skipped"
        result["Error"] = "Empty URL"
        return result

    driver = None
    try:
        url = _validate_public_url(url, request_budget=request_budget)
        user_agent = enforce_browser_policy(url, request_budget)
        result["_browser_used"] = True
        start = time.perf_counter()
        driver = webdriver.Chrome(options=get_chrome_options(user_agent=user_agent))
        driver.set_page_load_timeout(timeout)
        driver.get(url)
        elapsed_ms = (time.perf_counter() - start) * 1000

        title = (driver.title or "").lower()
        body_text = ""
        try:
            body_text = driver.find_element("tag name", "body").text[:500].lower()
        except Exception:
            pass
        try:
            page_source = driver.page_source or ""
        except Exception:
            page_source = ""

        dead_markers = ["site can't be reached", "this site can't be reached", "dns_probe_finished_nxdomain"]
        # A browser cannot report the HTTP status, so a page that merely rendered is not proof it
        # worked. The body mentioning "404" is not proof either, but the page title is a fair signal.
        if any(marker in title for marker in dead_markers) or any(marker in body_text for marker in dead_markers):
            result["Status"] = "Unknown"
            result["Error"] = "Browser displayed a possible network error; HTTP status was not available"
        else:
            document = read_document_response(driver, page_source)
            code = document.status_code if document is not None else None
            result["Status Code"] = code
            marker = ("bot-protection script in page" if looks_like_challenge(page_source, title) else
                      next((f"'{m}' in page title" for m in BROWSER_BLOCK_MARKERS if m in title), "") or
                      next((f"'{m}' in page text" for m in BROWSER_BLOCK_MARKERS if m in body_text), ""))
            if marker and (code is None or code != 200 or marker.startswith("bot-protection")
                           or "title" in marker):
                result["Status"] = "Challenged"
                result["Error"] = (f"Browser received a block or bot-protection page ({marker}"
                                   + (f", HTTP {code}" if code else "") + "); availability is unconfirmed")
            elif code is not None and code >= 400:
                if code in (401, 403):
                    result["Status"] = "Restricted"
                elif code in (405, 429):
                    result["Status"] = "Blocked"
                elif code >= 500:
                    result["Status"] = "Degraded"
                else:
                    result["Status"] = "Down"
                result["Error"] = f"Browser received HTTP {code}"
            elif code is None and any(m in title for m in BROWSER_NOT_FOUND_TITLES):
                result["Status"] = "Unknown"
                result["Error"] = "Browser showed a not-found page title; HTTP status was not available"
            else:
                result["Status"] = "Up"
                result["Response Time (ms)"] = round(elapsed_ms, 1)
                if document is not None:
                    apply_security_analysis(result, document, "Analyzed in browser")
                else:
                    result["Security Analysis"] = "Not analyzed: browser response headers unavailable"
    except PolicyBlocked as e:
        result["Status"] = "Skipped"
        result["Error"] = str(e)[:180]
    except TimeoutException:
        result["Status"] = "Unknown"
        result["Error"] = f"Browser page load timed out after {timeout}s"
    except WebDriverException as e:
        result["Status"] = "Unknown"
        result["Error"] = f"Browser error: {str(e)[:120]}"
    finally:
        if driver is not None:
            try:
                driver.quit()
            except Exception:
                pass

    return result


def check_url_advanced(url: str, timeout: float, challenge_wait: float = 8.0, request_budget=None) -> dict:
    """A slower, more thorough retry for a site that failed both the fast HTTP
    check and the standard browser check. Uses stealth browser options to hide
    common automation fingerprints, and waits several extra seconds after page
    load to give a JS-based challenge (e.g. a 'checking your browser' page)
    time to resolve before judging the result.

    This can only get past bot detection based on *fingerprinting* (detecting
    the browser looks automated). It cannot get past a site that blocks the
    request's network/IP outright — no browser-side trick fixes that; a
    consistent failure here despite this technique is a strong sign that's
    what's happening, and the only real fix is checking from a different
    network."""
    original = url
    result = {
        "URL": original,
        "Status": "Unknown",
        "Status Code": None,
        "Response Time (ms)": None,
        "Error": "",
        "Checked At": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
        "Checked Via": "Advanced Retry",
    }

    if not str(url or "").strip():
        result["Status"] = "Skipped"
        result["Error"] = "Empty URL"
        return result

    driver = None
    try:
        url = _validate_public_url(url, request_budget=request_budget)
        if url_in_agreed_scope(url):
            raise PolicyBlocked("Skipped: stealth retry is not used on sites under agreed crawl rules")
        result["_stealth_used"] = True
        result["_browser_used"] = True
        start = time.perf_counter()
        driver = webdriver.Chrome(options=get_chrome_options(stealth=True))
        driver.set_page_load_timeout(timeout)
        try:
            driver.execute_cdp_cmd(
                "Page.addScriptToEvaluateOnNewDocument",
                {"source": "Object.defineProperty(navigator, 'webdriver', {get: () => undefined})"},
            )
        except Exception:
            pass  # not fatal if CDP isn't available; stealth options above still apply

        driver.get(url)
        time.sleep(challenge_wait)  # let a JS challenge / interstitial finish resolving
        elapsed_ms = (time.perf_counter() - start) * 1000

        title = (driver.title or "").lower()
        body_text = ""
        try:
            body_text = driver.find_element("tag name", "body").text[:800].lower()
        except Exception:
            pass

        dead_markers = ["site can't be reached", "this site can't be reached", "dns_probe_finished_nxdomain"]
        challenge_markers = ["just a moment", "checking your browser", "attention required", "access denied"]

        if any(marker in title for marker in dead_markers) or any(marker in body_text for marker in dead_markers):
            result["Status"] = "Unknown"
            result["Error"] = "Browser displayed a possible network error; HTTP status was not available"
        elif any(marker in title for marker in challenge_markers) or any(marker in body_text for marker in challenge_markers):
            result["Status"] = "Blocked"
            result["Error"] = "Still blocked by a bot-protection challenge; availability is inconclusive"
        else:
            result["Status"] = "Up"
            result["Response Time (ms)"] = round(elapsed_ms, 1)
    except PolicyBlocked as e:
        result["Status"] = "Skipped"
        result["Error"] = str(e)[:180]
    except TimeoutException:
        result["Status"] = "Unknown"
        result["Error"] = f"Browser page load timed out after {timeout}s (even with stealth options)"
    except WebDriverException as e:
        result["Status"] = "Unknown"
        result["Error"] = f"Browser error: {str(e)[:120]}"
    finally:
        if driver is not None:
            try:
                driver.quit()
            except Exception:
                pass

    return result


def site_of_url(url: str) -> str:
    try:
        return key_host_of(normalize_url(url))
    except Exception:
        return ""


def run_checks(urls: list, timeout: float, max_workers: int, progress_cb=None, request_budget=None,
               one_site_at_a_time: bool = False, site_pause: float = 0.0) -> list:
    """The per-host rate cap does not limit the combined rate across hosts, and sites on shared
    infrastructure can see that combined rate from one IP. one_site_at_a_time finishes each site
    before starting the next, so the combined rate stays close to the per-host cap."""
    results = []
    def checked_with_retry(u):
        item = check_url(u, timeout, request_budget=request_budget)
        if item.get("Status") in ("Unknown", "Degraded"):
            # One bounded retry helps distinguish transient transport/server failures.
            time.sleep(0.4 + random.random() * 0.2)
            retry = check_url(u, timeout, request_budget=request_budget)
            retry["Attempts"] = 2
            if retry.get("Status") == "Up":
                retry["Error"] = "Recovered on retry"
            return retry
        item["Attempts"] = 1
        return item

    workers = max(1, min(int(max_workers), 50))
    if one_site_at_a_time:
        by_site = {}
        for u in urls:
            by_site.setdefault(site_of_url(u), []).append(u)
        batches = list(by_site.values())
        workers = min(workers, MAX_WORKERS_ONE_SITE)
    else:
        batches = [urls]

    done = 0
    for index, batch in enumerate(batches):
        if index and site_pause > 0:
            remaining = request_budget.remaining_seconds() if request_budget is not None else site_pause
            time.sleep(min(float(site_pause), remaining))
        with ThreadPoolExecutor(max_workers=workers) as executor:
            futures = {executor.submit(checked_with_retry, u): u for u in batch}
            for future in as_completed(futures):
                try:
                    results.append(future.result())
                except Exception as exc:
                    results.append({"URL": futures[future], "Status": "Unknown", "Status Code": None,
                                    "Response Time (ms)": None, "Error": f"Unexpected checker error ({type(exc).__name__})",
                                    "Checked At": datetime.now().strftime("%Y-%m-%d %H:%M:%S"), "Checked Via": "HTTP", "Attempts": 1})
                done += 1
                if progress_cb:
                    progress_cb(done, len(urls))
    order = {u: i for i, u in enumerate(urls)}
    results.sort(key=lambda r: order.get(r["URL"], 0))
    return results


def style_status(val):
    if val == "Up":
        return "background-color: #d4edda; color: #155724; font-weight: 600;"
    elif val == "Down":
        return "background-color: #f8d7da; color: #721c24; font-weight: 600;"
    elif val == "Skipped":
        return "background-color: #e2e3e5; color: #383d41; font-weight: 600;"
    elif val in ("Unknown", "Blocked", "Restricted", "Challenged", "Degraded"):
        return "background-color: #fff3cd; color: #664d03; font-weight: 600;"
    return ""


def style_severity(val):
    colors = {"High": "#f8d7da", "Medium": "#ffe5d0", "Low": "#fff3cd", "Info": "#e2e3e5"}
    return f"background-color: {colors.get(val, '')}; font-weight: 600; color: #222;"


# ---------------------------------------------------------------------------
# Helpers - crawling a site
# ---------------------------------------------------------------------------

def root_domain(netloc: str) -> str:
    netloc = netloc.lower()
    if netloc.startswith("www."):
        netloc = netloc[4:]
    return netloc


def is_probably_html_link(url: str) -> bool:
    path = urlparse(url).path.lower()
    return not path.endswith(NON_HTML_EXTENSIONS)


def browser_read_links_page(url: str, timeout: float, request_budget=None) -> tuple:
    """Open a page in the browser for link discovery only. Returns (html, final URL, status), or
    raises PolicyBlocked, or returns None when the browser itself received a refusal."""
    driver = None
    url = _validate_public_url(url, request_budget=request_budget)
    user_agent = enforce_browser_policy(url, request_budget)
    try:
        driver = webdriver.Chrome(options=get_chrome_options(user_agent=user_agent))
        driver.set_page_load_timeout(max(timeout, 15))
        driver.get(url)
        html = driver.page_source or ""
        document = read_document_response(driver, html)
        code = document.status_code if document is not None else None
        if (code is not None and code >= 400) or looks_like_challenge(html, driver.title or ""):
            return None
        return html, driver.current_url or url, code
    finally:
        if driver is not None:
            try:
                driver.quit()
            except Exception:
                pass


def crawl_site(start_url: str, max_pages: int, max_depth: int, timeout: float,
                include_external: bool = True, max_external: int = 75,
                use_browser: bool = False, progress_cb=None, request_budget=None,
                browser_fallback: bool = False) -> list:
    """Breadth-first discovery crawl.

    With browser_fallback, a page that is refused, challenged or has no links over plain HTTP
    is opened once in the browser to read its links, so depth still works on protected sites.

    Depth 0 is the supplied URL. The crawler fetches pages at depths less than
    max_depth, discovers links at the next depth, and returns every discovered
    URL up to max_pages so the shared checker can check those URLs too.
    Crawl failures are attached to the affected page instead of being silently
    discarded. External URLs can be reported but are never recursively crawled.
    """
    def canonical(u: str) -> str:
        u = u.split("#", 1)[0]
        parsed = urlparse(u)
        if parsed.path == "/" and parsed.query == "":
            return urlunparse((parsed.scheme.lower(), parsed.netloc.lower(), "", "", "", ""))
        return u

    def host_key(u: str) -> tuple:
        parsed = urlparse(u)
        host = (parsed.hostname or "").lower()
        if host.startswith("www."):
            host = host[4:]
        port = parsed.port
        if (parsed.scheme.lower() == "https" and port == 443) or (parsed.scheme.lower() == "http" and port == 80):
            port = None
        return host, port

    start_url = canonical(_validate_public_url(normalize_url(start_url), request_budget=request_budget))
    base_host = host_key(start_url)
    if request_budget is not None and use_browser:
        raise ValueError("Browser crawling cannot be used with strict request limits")

    # Keep discovered URLs separate from the fetch queue. This is important:
    # every accepted link is returned for checking even if the fetch/page cap
    # prevents the crawler from opening that link to discover still more links.
    discovered = {
        start_url: {"url": start_url, "type": "Internal", "sources": set(),
                    "depth": 0, "crawl_error": "", "links_found": 0}
    }
    queue = deque([(start_url, 0)])
    queued_urls = {start_url}
    visited_pages = set()
    driver = None
    browser_init_error = None

    if use_browser and SELENIUM_AVAILABLE:
        try:
            driver = webdriver.Chrome(options=get_chrome_options())
            driver.set_page_load_timeout(timeout)
        except Exception as e:
            driver = None
            browser_init_error = f"Browser startup failed; falling back to HTTP: {type(e).__name__}: {str(e)[:160]}"

    try:
        while queue and len(visited_pages) < max_pages:
            if request_budget is not None and request_budget.remaining_seconds() <= 0:
                discovered[queue[0][0]]["crawl_error"] = "Crawl stopped: time limit reached before this page could be fetched"
                break
            url, depth = queue.popleft()
            if url in visited_pages:
                continue
            visited_pages.add(url)
            if progress_cb:
                progress_cb(len(visited_pages), max_pages)
            # Links at max_depth are checked by run_checks but not opened to
            # discover depth+1 links. This is the intended depth definition.
            if depth >= max_depth or not is_probably_html_link(url):
                continue

            try:
                if driver is not None:
                    driver.get(url)
                    html = driver.page_source
                    page_base_url = driver.current_url or url
                else:
                    resp = http_get(url, timeout, request_budget=request_budget)
                    discovered[url]["crawl_status"] = resp.status_code
                    content_type = (resp.headers.get("Content-Type", "") or "").lower()
                    clearly_non_html = any(kind in content_type for kind in (
                        "application/pdf", "image/", "audio/", "video/", "application/zip",
                        "application/octet-stream", "application/msword",
                        "application/vnd.openxmlformats-officedocument",
                    ))
                    if clearly_non_html:
                        discovered[url]["crawl_error"] = f"Not parsed as HTML (Content-Type: {content_type or 'missing'})"
                        continue
                    html = resp.text
                    page_base_url = getattr(resp, "url", None) or url

                soup = BeautifulSoup(html, "html.parser")
                anchors = soup.find_all("a", href=True)
                if driver is None and (resp.status_code >= 400 or not anchors or response_is_challenge(resp)):
                    plain_reason = f"HTTP {resp.status_code}" + ("" if anchors else ", no links")
                    opened = None
                    browser_note = "browser verification is off"
                    if browser_fallback and SELENIUM_AVAILABLE:
                        browser_note = "the browser was refused too"
                        try:
                            opened = browser_read_links_page(url, timeout, request_budget)
                        except PolicyBlocked:
                            raise
                        except Exception as exc:
                            browser_note = f"browser failed ({type(exc).__name__})"
                    if opened is not None:
                        soup = BeautifulSoup(opened[0], "html.parser")
                        page_base_url = opened[1]
                        anchors = soup.find_all("a", href=True)
                        discovered[url]["crawl_via"] = "Browser"
                    elif resp.status_code >= 400 or not anchors:
                        discovered[url]["crawl_error"] = f"Links could not be read: {plain_reason}; {browser_note}"
                discovered[url]["links_found"] = len(anchors)
                for a in anchors:
                    href = a.get("href", "").strip()
                    if not href or href.startswith(("mailto:", "tel:", "javascript:", "#")):
                        continue
                    full_url = canonical(urljoin(page_base_url, href))
                    try:
                        parsed = urlparse(full_url)
                        if parsed.scheme not in ("http", "https"):
                            continue
                        _validate_public_url(full_url, request_budget=request_budget)
                    except (PolicyBlocked, requests.exceptions.RequestException, ValueError):
                        continue

                    is_internal = host_key(full_url) == base_host
                    child_depth = depth + 1
                    if is_internal:
                        if full_url not in discovered:
                            # max_pages caps URLs discovered, not just pages opened.
                            if len(discovered) >= max_pages:
                                continue
                            discovered[full_url] = {
                                "url": full_url, "type": "Internal", "sources": {url},
                                "depth": child_depth, "crawl_error": "", "links_found": 0,
                            }
                        else:
                            discovered[full_url]["sources"].add(url)
                            discovered[full_url]["depth"] = min(discovered[full_url]["depth"], child_depth)
                        if child_depth < max_depth and full_url not in visited_pages and full_url not in queued_urls:
                            queue.append((full_url, child_depth))
                            queued_urls.add(full_url)
                    elif include_external:
                        if full_url in discovered:
                            discovered[full_url]["sources"].add(url)
                        elif sum(1 for item in discovered.values() if item["type"] == "External") < max_external and len(discovered) < max_pages:
                            discovered[full_url] = {
                                "url": full_url, "type": "External", "sources": {url},
                                "depth": child_depth, "crawl_error": "External links are checked but not crawled",
                                "links_found": 0,
                            }
            except ScanLimitReached as e:
                discovered[url]["crawl_error"] = str(e)
                break
            except PolicyBlocked as e:
                discovered[url]["crawl_error"] = f"Crawl blocked by site policy: {str(e)[:180]}"
            except requests.exceptions.RequestException as e:
                discovered[url]["crawl_error"] = f"HTTP fetch failed: {type(e).__name__}: {str(e)[:180]}"
            except Exception as e:
                # Surface the error in the report/UI; do not silently pretend
                # this page had no links.
                discovered[url]["crawl_error"] = f"Page could not be parsed: {type(e).__name__}: {str(e)[:180]}"
    finally:
        if driver is not None:
            try:
                driver.quit()
            except Exception:
                pass

    return list(discovered.values()), browser_init_error


# ---------------------------------------------------------------------------
# Helpers - email alerts
# ---------------------------------------------------------------------------

def smtp_configured() -> bool:
    try:
        s = st.secrets["smtp"]
        return all(k in s for k in ("server", "port", "username", "password", "from_address"))
    except Exception:
        return False


def send_alert_email(recipient: str, newly_down: list, still_down: list) -> tuple:
    if not smtp_configured():
        return False, (
            "SMTP is not configured in secrets.toml — see README for setup. "
            "No email was sent."
        )

    cfg = st.secrets["smtp"]
    subject = f"⚠️ Website Down Alert — {len(newly_down)} new site(s) down"

    lines = ["The following site(s) just went DOWN:\n"]
    for r in newly_down:
        lines.append(f"  - {r['URL']}  (Error: {r['Error'] or r['Status Code']})")

    if still_down:
        lines.append("\nStill down from a previous check:")
        for r in still_down:
            lines.append(f"  - {r['URL']}  (Error: {r['Error'] or r['Status Code']})")

    lines.append(f"\nChecked at: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    body = "\n".join(lines)

    msg = MIMEText(body)
    msg["Subject"] = subject
    msg["From"] = cfg["from_address"]
    msg["To"] = recipient

    try:
        with smtplib.SMTP(cfg["server"], int(cfg["port"]), timeout=15) as server:
            server.starttls()
            server.login(cfg["username"], cfg["password"])
            server.sendmail(cfg["from_address"], [recipient], msg.as_string())
        return True, f"Alert email sent to {recipient}."
    except Exception as e:
        return False, f"Failed to send email: {e}"


# ---------------------------------------------------------------------------
# Saved sites (entire-site crawls) and download file names
# ---------------------------------------------------------------------------
# Every site you crawl is remembered in a small JSON file next to the app, so it
# can be picked from a dropdown next time. The file holds only the address, when
# it was last crawled, and the limits used. It never holds the crawler key.

try:
    _APP_DIR = os.path.dirname(os.path.abspath(__file__))
except NameError:
    _APP_DIR = os.getcwd()
SITES_FILE = os.environ.get("UPTIME_SITES_FILE") or os.path.join(_APP_DIR, "crawled_sites.json")
NEW_SITE_OPTION = "— enter a new site —"


def site_key(url: str) -> str:
    """Identity of a crawled site: host (www ignored), non-default port and path, lowercased."""
    full = normalize_url(url)
    parsed = urlparse(full)
    try:
        port = parsed.port
    except ValueError:
        port = None
    port_part = f":{port}" if port and port != 443 else ""
    return f"{key_host_of(full)}{port_part}{(parsed.path or '').rstrip('/').lower()}"


def _clamp_int(value, low: int, high: int, default: int) -> int:
    try:
        return max(low, min(high, int(value)))
    except (TypeError, ValueError):
        return default


def load_sites() -> list:
    """Saved sites, most recently crawled first. A missing or damaged file just means an empty list."""
    try:
        with open(SITES_FILE, encoding="utf-8") as f:
            data = json.load(f)
    except (OSError, ValueError):
        return []
    sites = []
    for d in data if isinstance(data, list) else []:
        if not isinstance(d, dict) or not isinstance(d.get("url"), str) or not d["url"].strip():
            continue
        sites.append({
            "url": d["url"].strip(),
            "last_crawled": str(d.get("last_crawled", ""))[:19],
            "times_crawled": _clamp_int(d.get("times_crawled"), 1, 1_000_000, 1),
            "max_pages": _clamp_int(d.get("max_pages"), 1, 300, 30),
            "max_depth": _clamp_int(d.get("max_depth"), 1, 5, 2),
            "include_external": bool(d.get("include_external", True)),
            "max_external": _clamp_int(d.get("max_external"), 10, 300, 75),
        })
    # Newest first. Entries are saved oldest-to-newest, so a later position wins any tie.
    sites = [x for _, x in sorted(enumerate(sites), key=lambda p: (p[1]["last_crawled"], p[0]), reverse=True)]
    unique, seen = [], set()
    for site in sites:
        if site_key(site["url"]) not in seen:
            seen.add(site_key(site["url"]))
            unique.append(site)
    return unique


def save_sites(sites: list) -> bool:
    """Write atomically, so an interrupted save can never leave a half-written list."""
    tmp = SITES_FILE + ".tmp"
    try:
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(sites, f, indent=2)
        os.replace(tmp, SITES_FILE)
        return True
    except OSError:
        try:
            os.remove(tmp)
        except OSError:
            pass
        return False


def record_crawled_site(url: str, settings: dict) -> bool:
    """Add the site, or update it if it is already listed."""
    url = normalize_url(url).rstrip("/")
    if not urlparse(url).hostname:
        return False
    sites = load_sites()
    entry = next((x for x in sites if site_key(x["url"]) == site_key(url)), None)
    now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    if entry:
        entry.update(url=url, last_crawled=now, times_crawled=entry["times_crawled"] + 1)
        sites.remove(entry)
        sites.append(entry)  # keep the file in oldest-to-newest order
    else:
        entry = {"url": url, "last_crawled": now, "times_crawled": 1}
        sites.append(entry)
    entry.update({
        "max_pages": _clamp_int(settings.get("max_pages"), 1, 300, 30),
        "max_depth": _clamp_int(settings.get("max_depth"), 1, 5, 2),
        "include_external": bool(settings.get("include_external", True)),
        "max_external": _clamp_int(settings.get("max_external"), 10, 300, 75),
    })
    return save_sites(sites)


def remove_site(url: str) -> bool:
    return save_sites([x for x in load_sites() if site_key(x["url"]) != site_key(url)])


def apply_saved_site():
    """Dropdown callback: fill the crawl form with the saved address and limits."""
    pick = st.session_state.get("saved_site_pick")
    if not pick or pick == NEW_SITE_OPTION:
        return
    site = next((x for x in load_sites() if x["url"] == pick), None)
    if site:
        st.session_state["crawl_url"] = site["url"]
        st.session_state["crawl_max_pages"] = site["max_pages"]
        st.session_state["crawl_max_depth"] = site["max_depth"]
        st.session_state["crawl_include_external"] = site["include_external"]
        st.session_state["crawl_max_external"] = site["max_external"]


def save_site_from_form():
    """Crawl-button callback: runs before the page redraws, so the dropdown shows the site straight away."""
    url = (st.session_state.get("crawl_url") or "").strip()
    if url:
        st.session_state["site_list_save_failed"] = not record_crawled_site(url, {
            "max_pages": st.session_state.get("crawl_max_pages"),
            "max_depth": st.session_state.get("crawl_max_depth"),
            "include_external": st.session_state.get("crawl_include_external", True),
            "max_external": st.session_state.get("crawl_max_external"),
        })


def remove_selected_site():
    pick = st.session_state.get("saved_site_pick")
    if pick and pick != NEW_SITE_OPTION:
        remove_site(pick)
    st.session_state["saved_site_pick"] = NEW_SITE_OPTION


def file_slug(site: str) -> str:
    """Safe file-name form of a site: 'https://www.Example.com:8443/x' -> 'example.com-8443'."""
    text = re.sub(r"^https?://", "", (site or "").strip().lower()).split("/")[0]
    if text.startswith("www."):
        text = text[4:]
    return (re.sub(r"[^a-z0-9.-]+", "-", text).strip("-.") or "site")[:60]


def scan_file_name(kind: str, scan_meta: dict, ext: str, stamp: str) -> str:
    """e.g. scan_report_broadlineelectricals.com_20261018_142530.html"""
    return f"{kind}_{file_slug((scan_meta or {}).get('site') or (scan_meta or {}).get('target', ''))}_{stamp}.{ext}"


# ---------------------------------------------------------------------------
# Automatic saving of the reports
# ---------------------------------------------------------------------------
# When a scan you started finishes, the reports are written to a folder, so nothing
# is lost if you move on without clicking download. Files use exactly the same names
# as the download buttons (the time in the name is the scan's own finish time).

REPORTS_DIR = os.environ.get("UPTIME_REPORTS_DIR") or os.path.join(_APP_DIR, "reports")


def results_dataframe(results: list) -> pd.DataFrame:
    """The results as shown and exported. Internal working columns (leading underscore) never appear."""
    df = pd.DataFrame(results)
    df = df.drop(columns=[c for c in df.columns if str(c).startswith("_")])
    if "Security Issues" in df.columns:
        df["Security Issues"] = df["Security Issues"].astype("Int64")
    return df


def scan_stamp(scan_info: dict) -> str:
    """The scan's finish time as 20261018_142530."""
    try:
        return datetime.strptime((scan_info or {}).get("finished", ""), "%Y-%m-%d %H:%M:%S").strftime("%Y%m%d_%H%M%S")
    except ValueError:
        return datetime.now().strftime("%Y%m%d_%H%M%S")


def _unique_path(directory: str, name: str) -> str:
    """Never overwrite an existing report: add _2, _3, ... if the name is taken."""
    base, ext = os.path.splitext(name)
    path, n = os.path.join(directory, name), 2
    while os.path.exists(path):
        path = os.path.join(directory, f"{base}_{n}{ext}")
        n += 1
    return path


def save_scan_reports(results: list, scan_info: dict, host_security: dict, branding: dict = None) -> dict:
    """Write the reports for a finished scan to REPORTS_DIR. Returns what was saved and any problem.
    One report failing never loses the others."""
    saved = {"dir": REPORTS_DIR, "files": [], "error": "", "finished": (scan_info or {}).get("finished", "")}
    stamp = scan_stamp(scan_info)
    security = bool((scan_info or {}).get("security_enabled"))
    jobs = []
    if security:
        jobs.append(("client_snapshot", "html", lambda: build_client_report_html(results, scan_info, host_security, branding)))
    jobs.append(("scan_report", "html", lambda: build_report_html(results, scan_info, host_security, branding)))
    if security:
        jobs.append(("security_findings", "csv", lambda: findings_csv(results, host_security)))
    jobs.append(("uptime_results", "csv", lambda: results_dataframe(results).to_csv(index=False)))
    try:
        os.makedirs(REPORTS_DIR, exist_ok=True)
    except OSError as e:
        saved["error"] = f"couldn't create the folder ({type(e).__name__})"
        return saved
    for kind, ext, make in jobs:
        tmp = None
        try:
            content = make()
            path = _unique_path(REPORTS_DIR, scan_file_name(kind, scan_info, ext, stamp))
            tmp = path + ".tmp"
            with open(tmp, "w", encoding="utf-8", newline="") as f:  # written as-is; no newline translation
                f.write(content)
            os.replace(tmp, path)  # complete file or nothing
            saved["files"].append(os.path.basename(path))
        except Exception as e:
            saved["error"] = f"couldn't save {kind} ({type(e).__name__})"
            if tmp:
                try:
                    os.remove(tmp)
                except OSError:
                    pass
    return saved


# ---------------------------------------------------------------------------
# Shared check pipeline (used by both CSV upload and site crawl)
# ---------------------------------------------------------------------------

def confirm_down_internal_links(results, timeout: float, request_budget=None, retry_attempts: int = 2,
                                sleep_seconds: float = 0.45, check_func=None, sleep_func=None,
                                include_csv_urls: bool = False) -> list:
    """Recheck internal crawl URLs reported Down before treating them as broken.

    The initial request plus two retries are used by default. A transient Up
    response clears the Down result. A non-Down response makes the result
    inconclusive (or Restricted/Blocked/Skipped as appropriate). A link is
    only left Down when all attempts return Down with the same HTTP status
    code, which reduces false positives caused by intermittent failures.

    check_func and sleep_func are injectable to make this logic unit-testable.
    """
    check_func = check_func or check_url
    sleep_func = sleep_func or time.sleep
    # CSV mode confirms every URL in the uploaded list and any pages discovered
    # from those roots. Site-crawl mode remains limited to internal links.
    candidates = [r for r in results
                  if r.get("Status") == "Down" and
                  (include_csv_urls or r.get("Link Type") == "Internal")]
    for row in candidates:
        original_code = row.get("Status Code")
        observed_codes = [original_code]
        total_attempts = int(row.get("Attempts", 1) or 1)
        inconclusive_result = None
        recovered_result = None

        for retry_number in range(1, retry_attempts + 1):
            if request_budget is not None and request_budget.remaining_seconds() <= 0:
                inconclusive_result = {
                    "Status": "Unknown", "Error": "Confirmation retries stopped: scan time budget exhausted",
                    "Status Code": None, "Checked Via": "HTTP retry confirmation",
                }
                break
            sleep_func(sleep_seconds)
            try:
                retry = check_func(row["URL"], timeout, request_budget=request_budget)
            except Exception as exc:
                retry = {"Status": "Unknown", "Status Code": None,
                         "Error": f"Retry failed ({type(exc).__name__})", "Checked Via": "HTTP retry confirmation"}
            total_attempts += int(retry.get("Attempts", 1) or 1)
            observed_codes.append(retry.get("Status Code"))

            if retry.get("Status") == "Up":
                recovered_result = retry
                break
            if retry.get("Status") != "Down":
                inconclusive_result = retry
                break

        if recovered_result is not None:
            # Keep crawl metadata while replacing the availability result.
            for key, value in recovered_result.items():
                if key not in ("Link Type", "Found On", "Crawl Depth", "Links Found On Page", "Crawl Error"):
                    row[key] = value
            row["Status"] = "Up"
            row["Error"] = "Recovered during internal-link confirmation retry"
            row["Checked Via"] = "HTTP + retry confirmation"
            row["Down Confirmation"] = "Recovered"
        elif inconclusive_result is not None:
            row["Status"] = inconclusive_result.get("Status", "Unknown")
            row["Status Code"] = inconclusive_result.get("Status Code")
            row["Error"] = inconclusive_result.get("Error") or "Down status could not be confirmed"
            row["Checked Via"] = "HTTP + retry confirmation (inconclusive)"
            row["Down Confirmation"] = "Inconclusive"
        elif len(observed_codes) == retry_attempts + 1 and all(code == observed_codes[0] for code in observed_codes):
            row["Status"] = "Down"
            row["Error"] = f"Confirmed down: HTTP {observed_codes[0]} on {len(observed_codes)} attempts"
            row["Checked Via"] = "HTTP retry confirmation"
            row["Down Confirmation"] = f"Confirmed ({len(observed_codes)} matching responses)"
        else:
            row["Status"] = "Unknown"
            row["Error"] = f"Inconsistent responses during confirmation; HTTP status codes: {observed_codes}"
            row["Checked Via"] = "HTTP retry confirmation (inconsistent)"
            row["Down Confirmation"] = "Inconclusive"
        row["Attempts"] = total_attempts
    return results


DEFINITE_DOWN_CODES = (404, 410)
REFUSED_ON_RECHECK = ("Blocked", "Restricted", "Challenged")


def recheck_server_errors(results: list, timeout: float, browser_confirm: bool = False, request_budget=None,
                          delay: float = None, sleep_func=None) -> int:
    """Check every 5xx page once more after a real gap, using the route that reached it before.
    Retries seconds apart cannot separate a restart from a fault. A page stays a server error only
    if it fails again. Returns the number of pages rechecked."""
    rows = [r for r in results if r.get("Status") == "Degraded" and isinstance(r.get("Status Code"), int)
            and r["Status Code"] >= 500]
    if not rows:
        return 0
    delay = SERVER_RECHECK_SECONDS if delay is None else delay
    sleep_func = sleep_func or time.sleep
    seen = []
    for r in rows:
        try:
            seen.append(datetime.strptime(r.get("Checked At", ""), "%Y-%m-%d %H:%M:%S"))
        except (TypeError, ValueError):
            pass
    elapsed = (datetime.now() - max(seen)).total_seconds() if seen else 0.0
    wait = max(0.0, delay - elapsed)

    def not_rechecked(row, reason):
        row["Status"] = "Unknown"
        row["Error"] = f"Server error HTTP {row['Status Code']}; delayed recheck did not run ({reason})"
        row["Server Error Check"] = "Not rechecked"

    if request_budget is not None and request_budget.remaining_seconds() <= wait:
        for r in rows:
            not_rechecked(r, "scan time limit reached")
        return 0
    if wait:
        sleep_func(wait)

    for r in rows:
        first_code = r["Status Code"]
        try:
            if r.get("_browser_used"):
                new = check_url_browser(r["URL"], max(timeout, 15), request_budget=request_budget)
            else:
                new = check_url(r["URL"], timeout, request_budget=request_budget)
                if new.get("Status") in REFUSED_ON_RECHECK and browser_confirm:
                    opened = check_url_browser(r["URL"], max(timeout, 15), request_budget=request_budget)
                    new = opened if opened.get("Status") != "Skipped" else new
        except Exception as exc:
            new = {"Status": "Unknown", "Status Code": None, "Error": f"Recheck failed ({type(exc).__name__})"}
        status = new.get("Status")
        if new.get("_browser_used"):
            r["_browser_used"] = True
        if status == "Skipped":
            not_rechecked(r, new.get("Error", "stopped"))
        elif status == "Up":
            for key in ("Status", "Status Code", "Response Time (ms)", "Checked At", "Security Analysis",
                        "_security", "_security_meta", "Security Issues"):
                if key in new:
                    r[key] = new[key]
            r["Error"] = f"Recovered: first check got HTTP {first_code}, delayed recheck succeeded"
            r["Server Error Check"] = f"Recovered (first HTTP {first_code})"
            r["_server_error_recovered"] = first_code
        elif status == "Degraded" and (new.get("Status Code") or 0) >= 500:
            r["Status Code"] = new["Status Code"]
            r["Error"] = f"HTTP {first_code}, then HTTP {new['Status Code']} on delayed recheck"
            r["Server Error Check"] = "Failed again on delayed recheck"
        else:
            r["Status"] = status or "Unknown"
            r["Status Code"] = new.get("Status Code") or first_code
            r["Error"] = f"First check got HTTP {first_code}; delayed recheck: {new.get('Error') or status}"
            r["Server Error Check"] = "Inconclusive on delayed recheck"
    return len(rows)


def perform_full_check(urls, timeout, max_workers, browser_confirm, alert_enabled, alert_email, link_metadata=None, scan_info=None,
                       branding=None, save_reports=None, request_budget=None):
    started = datetime.now()
    progress_bar = st.progress(0, text="Checking websites...")

    def update_progress(done, total):
        progress_bar.progress(done / total, text=f"Checked {done}/{total} sites...")

    results = run_checks(urls, timeout=timeout, max_workers=max_workers, progress_cb=update_progress,
                         request_budget=request_budget,
                         one_site_at_a_time=bool((scan_info or {}).get("one_site_at_a_time")),
                         site_pause=float((scan_info or {}).get("site_pause") or 0))
    progress_bar.empty()

    # Attach crawl context (link type + which page(s) it was found on), if this
    # check came from a site crawl rather than a plain CSV upload.
    link_metadata = link_metadata or {}
    for r in results:
        r["Site"] = key_host_of(normalize_url(r["URL"])) if str(r.get("URL") or "").strip() else ""
        meta = link_metadata.get(r["URL"])
        if meta:
            r["Link Type"] = meta["type"]
            r["Found On"] = "; ".join(sorted(meta["sources"])) if meta["sources"] else "(starting page)"
            r["Crawl Depth"] = meta.get("depth", 0)
            r["Links Found On Page"] = meta.get("links_found", 0)
            r["Crawl Error"] = meta.get("crawl_error", "")
            r["Crawl Status"] = meta.get("crawl_status")
            r["Crawl Via"] = meta.get("crawl_via", "")
            if meta.get("crawl_via") == "Browser":
                r["_browser_used"] = True
        else:
            r["Link Type"] = "—"
            r["Found On"] = "—"
            r["Crawl Depth"] = "—"
            r["Links Found On Page"] = "—"
            r["Crawl Error"] = ""

    # Site-level security checks: one TLS handshake and one security.txt request per site.
    host_security = {}
    security_enabled = (
        (scan_info or {}).get("security_enabled")
        if (scan_info or {}).get("security_enabled") is not None
        else SECURITY_CONFIG["enabled"]
    )
    security_targets = (scan_info or {}).get("security_targets", SECURITY_CONFIG["hostnames"])
    if security_enabled and security_targets:
        sec_progress = st.progress(0, text="Checking TLS certificate and security.txt...")
        host_security = run_host_checks(list(security_targets), request_budget=request_budget)
        sec_progress.empty()
        if (scan_info or {}).get("mozilla_grades"):
            if save_reports is None:
                # A timed re-check keeps the grades from the scan you started.
                for host, checks in (st.session_state.get("host_security") or {}).items():
                    if host in host_security and "mozilla" in checks:
                        host_security[host]["mozilla"] = checks["mozilla"]
            else:
                mozilla_progress = st.progress(0, text="Getting Mozilla Observatory grades...")
                attach_mozilla_grades(host_security)
                mozilla_progress.empty()

    # Browser verification is applied to inconclusive/rejected HTTP results as well
    # as Down results, so an accessible page is not mislabeled because plain HTTP
    # requests were blocked. This verifies pages only; it does not click links or submit forms.
    # A 404 or 410 is a definite answer from the site. Browsers cannot report status codes, and a
    # styled error page renders fine, so those results are never sent to the browser to overturn.
    browser_indices = [i for i, r in enumerate(results)
                       if r["Status"] in ("Blocked", "Restricted", "Challenged")
                       or (r["Status"] == "Down" and r.get("Status Code") not in DEFINITE_DOWN_CODES)]
    if browser_confirm and browser_indices:
        browser_progress = st.progress(0, text="Verifying blocked/restricted/down pages in a browser...")
        for done, idx in enumerate(browser_indices, start=1):
            original_result = results[idx]
            browser_result = check_url_browser(original_result["URL"], timeout=max(timeout, 15),
                                               request_budget=request_budget)
            if browser_result.get("_browser_used"):
                original_result["_browser_used"] = True
            if browser_result["Status"] == "Up":
                first_code = original_result.get("Status Code")
                original_result["Status"] = "Up"
                original_result["Error"] = (f"Plain request got HTTP {first_code}; page loaded in the browser"
                                            if first_code else "Plain request failed; page loaded in the browser")
                original_result["Checked Via"] = "HTTP + Browser (page loaded)"
                original_result["Status Code"] = browser_result.get("Status Code") or first_code
                original_result["Response Time (ms)"] = browser_result.get("Response Time (ms)")
                for key in ("_security", "_security_meta", "Security Issues", "Security Analysis"):
                    if key in browser_result:
                        original_result[key] = browser_result[key]
            elif browser_result["Status"] == "Skipped":
                # The rules stopped the browser check, so the HTTP result stands.
                original_result["Checked Via"] = f"HTTP (browser not used: {browser_result.get('Error', '')})"
            elif browser_result["Status"] in ("Unknown", "Blocked", "Restricted", "Challenged", "Degraded"):
                original_result["Status"] = browser_result["Status"]
                original_result["Status Code"] = browser_result.get("Status Code") or original_result.get("Status Code")
                original_result["Checked At"] = browser_result.get("Checked At") or original_result.get("Checked At")
                original_result["Error"] = (browser_result.get("Error") or
                    "Browser could not confirm page availability; result is inconclusive")
                original_result["Checked Via"] = "HTTP + Browser (inconclusive)"
            else:
                original_result["Status"] = "Down"
                original_result["Checked Via"] = "HTTP + Browser (still down)"
                original_result["Status Code"] = browser_result.get("Status Code") or original_result.get("Status Code")
                if browser_result.get("Status Code") in DEFINITE_DOWN_CODES:
                    # The browser saw the real status, so a plain retry that is refused must not replace it.
                    original_result["Error"] = browser_result.get("Error", "")
                    original_result["Down Confirmation"] = f"Confirmed by browser (HTTP {browser_result['Status Code']})"
            browser_progress.progress(
                done / len(browser_indices),
                text=f"Browser-verified {done}/{len(browser_indices)} blocked/restricted/down page(s)...",
            )
        browser_progress.empty()

    # Automatically confirm Down results before reporting or alerting. For a
    # site crawl, only internal links are rechecked. For CSV mode, all URLs
    # supplied or discovered from the uploaded CSV are eligible for confirmation.
    is_csv_run = (scan_info or {}).get("mode") == "csv"
    if link_metadata or is_csv_run:
        pending = [r for r in results if r.get("Status") == "Down" and
                   not str(r.get("Down Confirmation", "")).startswith("Confirmed by browser") and
                   (is_csv_run or r.get("Link Type") == "Internal")]
        if pending:
            label = "CSV URL/page" if is_csv_run else "internal link"
            confirm_progress = st.progress(0, text=f"Confirming {len(pending)} down {label}(s)...")
            # Sequential retries avoid creating a burst of requests.
            for done, row in enumerate(pending, start=1):
                confirm_down_internal_links([row], timeout, request_budget=request_budget,
                                            retry_attempts=2, sleep_seconds=0.45,
                                            include_csv_urls=is_csv_run)
                confirm_progress.progress(done / len(pending),
                                          text=f"Confirmed {done}/{len(pending)} {label}(s)...")
            confirm_progress.empty()

    server_error_count = sum(1 for r in results if r.get("Status") == "Degraded")
    if server_error_count:
        recheck_note = st.progress(0, text=f"Rechecking {server_error_count} server error page(s) after a short delay...")
        recheck_server_errors(results, timeout, browser_confirm=browser_confirm, request_budget=request_budget)
        recheck_note.empty()

    current_down_urls = {r["URL"] for r in results if r["Status"] == "Down"}
    newly_down_urls = current_down_urls - st.session_state.previously_down
    still_down_urls = current_down_urls & st.session_state.previously_down

    if alert_enabled and alert_email and newly_down_urls:
        newly_down = [r for r in results if r["URL"] in newly_down_urls]
        still_down = [r for r in results if r["URL"] in still_down_urls]
        success, msg = send_alert_email(alert_email, newly_down, still_down)
        if success:
            st.toast(msg, icon="📧")
        else:
            st.warning(msg)

    st.session_state.previously_down = current_down_urls
    st.session_state.results = results

    # Everything the report needs to describe this scan (the key itself is never recorded).
    info = dict(scan_info or {})
    info.update({
        "started": started.strftime("%Y-%m-%d %H:%M:%S"),
        "finished": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
        "key_hosts": list(KEY_CONFIG["hosts"]) if (KEY_CONFIG["key"] and KEY_CONFIG["hosts"]) else [],
        "policy_hosts": list(KEY_CONFIG.get("policy_hosts", [])),
        "user_agent": KEY_CONFIG["user_agent"],
        "rps": KEY_CONFIG["rps"],
        "blocked_paths": list(KEY_CONFIG["blocked_paths"]),
        "browser_confirm": browser_confirm,
        "server_recheck_seconds": SERVER_RECHECK_SECONDS,
        "security_enabled": bool(security_enabled),
        "engine_version": "11a",
        "max_response_bytes": MAX_RESPONSE_BYTES,
        "max_redirects": MAX_REDIRECTS,
        "target_policy": "Public Internet only by default; private targets require UPTIME_ALLOW_PRIVATE_TARGETS=true",
    })
    if request_budget is not None:
        info["request_limit"] = request_budget.max_requests
        info["requests_made"] = request_budget.requests_made
    st.session_state.scan_info = info
    st.session_state.host_security = host_security

    # save_reports: True/False for a scan the user started; None for the timed re-check, which
    # must not write a new set of files every cycle and leaves the message about the last save alone.
    if save_reports is True:
        st.session_state.saved_reports = save_scan_reports(results, info, host_security, branding)
    elif save_reports is False:
        st.session_state.saved_reports = None


# ---------------------------------------------------------------------------
# UI
# ---------------------------------------------------------------------------


def find_zap_baseline_command():
    configured = os.environ.get("ZAP_BASELINE_COMMAND", "").strip()
    if configured:
        command = shutil.which(configured) or (configured if os.path.isfile(configured) else None)
        return command if command and not command.lower().endswith((".bat", ".cmd")) else None
    return shutil.which("zap-baseline.py") or shutil.which("zap-baseline")


def run_zap_baseline(target: str, max_minutes: int, command: str, allowed_hosts=None) -> dict:
    target = _validate_public_url(normalize_url(target), allowed_hosts=allowed_hosts)
    with tempfile.TemporaryDirectory(prefix="uptime-zap-") as temp_dir:
        report_path = os.path.join(temp_dir, "zap-report.json")
        output_path = os.path.join(temp_dir, "zap-output.log")
        executable = [sys.executable, command] if command.lower().endswith(".py") else [command]
        args = executable + [
            "-t", target, "-m", str(int(max_minutes)),
            "-T", str(int(max_minutes)), "-J", report_path,
        ]
        try:
            with open(output_path, "wb") as output:
                completed = subprocess.run(
                    args, stdout=output, stderr=subprocess.STDOUT,
                    timeout=max(30, int(max_minutes) * 60 + 5), check=False,
                )
        except subprocess.TimeoutExpired:
            return {"status": "Timed out", "exit_code": None,
                    "output": "ZAP exceeded the configured hard time limit.", "report": None}
        except OSError as exc:
            raise RuntimeError(f"Could not start ZAP Baseline: {exc}") from exc

        with open(output_path, "rb") as output:
            output.seek(0, os.SEEK_END)
            size = output.tell()
            output.seek(max(0, size - 100_000))
            log = output.read().decode("utf-8", errors="replace")

        report = None
        report_error = None
        if os.path.isfile(report_path):
            if os.path.getsize(report_path) > 10_000_000:
                report_error = "ZAP's JSON report exceeded the 10 MB display limit."
            else:
                try:
                    with open(report_path, encoding="utf-8") as report_file:
                        report = json.load(report_file)
                except (OSError, json.JSONDecodeError) as exc:
                    report_error = f"Could not read ZAP's JSON report: {exc}"
        else:
            report_error = "ZAP did not produce a JSON report."

        return {
            "status": "Completed",
            "exit_code": completed.returncode,
            "output": log or "(ZAP produced no console output.)",
            "report": report,
            "report_error": report_error,
        }


st.title("🌐 Website Uptime Checker v11a")
st.caption("Choose a quick health check, a bounded internal crawl, or a passive ZAP Baseline assessment. CSV checks remain available.")

with st.sidebar:
    st.caption(f"Signed in as **{_client_username}**")
    st.caption("Assigned websites: " + ", ".join(sorted(CLIENT_ALLOWED_HOSTS)))
    if st.button("Log out"):
        st.session_state.clear()
        st.rerun()
    st.header("Settings")
    timeout = st.slider("Timeout per site (seconds)", 1, 30, 8)
    max_workers = st.slider("Parallel checks", 1, 50, 15)

    st.markdown("---")
    st.subheader("Crawler Key (X-ASAP-Key)")
    KEY_CONFIG["key"] = ""
    send_key_for_csv = False
    st.caption("Shared crawler keys are disabled for client accounts and are never sent to client websites.")

    st.markdown("---")
    st.subheader("Security Checks")
    st.caption("Safety defaults: public Internet targets only; private/loopback IPs and unsafe redirects are blocked. Configure network egress restrictions as an additional SSRF defense.")
    SECURITY_CONFIG["enabled"] = st.checkbox(
        "Run passive security checks",
        value=True,
        help="Reads the headers and content of pages the scan fetches anyway, plus one TLS "
             "handshake, one security.txt request and one http:// redirect check per site. Nothing is probed, submitted or "
             "exploited. Applies to the site you crawl (or the sites in your CSV), never to "
             "external links found along the way.",
    )

    mozilla_grades = st.checkbox(
        "Add Mozilla Observatory grades",
        value=False,
        help="Adds Mozilla's public security grade for each site you start a scan on. Mozilla's service scans the site itself, "
             "outside your crawl rules, and its scan history is public. Check that the site owner is comfortable with this first. "
             "Your crawler key is never sent to Mozilla.",
    )

    st.markdown("---")
    st.subheader("Report branding")
    _brand_defaults = load_branding_defaults()
    _saved_choice = load_brand_choice()
    _brand_keys = list(BRAND_CHOICES)
    brand_choice = st.radio(
        "Show on reports", _brand_keys, index=_brand_keys.index(_saved_choice),
        format_func=lambda key: BRAND_CHOICES[key],
        help="FusionWorks AI adds its logo and name throughout. Custom name replaces both everywhere. "
             "Reports never show contact details. Your choice is remembered.",
    )
    if brand_choice != _saved_choice and not save_brand_choice(brand_choice):
        st.warning("Your choice applies to this session, but it could not be saved for later sessions.")
    _custom_name, _logo_uri = "", ""
    if brand_choice == "custom":
        _saved_name = load_brand_name(_brand_defaults["company"])
        _custom_name = st.text_input("Name for reports", value=_saved_name, max_chars=80,
                                     help="Replaces FusionWorks AI everywhere. Leave blank for reports with no branding.")
        if _custom_name.strip() != _saved_name.strip() and not save_brand_name(_custom_name):
            st.warning("The name applies to this session, but it could not be saved for later sessions.")
        if "logo_uploader_version" not in st.session_state:
            st.session_state.logo_uploader_version = 0
        _logo_file = st.file_uploader("Logo (optional)", type=list(LOGO_TYPES),
                                      key=f"logo_upload_{st.session_state.logo_uploader_version}",
                                      help="PNG, JPG, WebP or SVG, up to 1 MB. A new upload replaces the saved one.")
        if _logo_file is not None:
            _logo_bytes = _logo_file.getvalue()
            _logo_ext = os.path.splitext(_logo_file.name)[1]
            _logo_uri = logo_data_uri(_logo_bytes, _logo_ext)
            if not _logo_uri:
                st.warning("That file could not be used as a logo. Use a real PNG, JPG, WebP or SVG up to 1 MB.")
            elif st.session_state.get("logo_saved_id") != _logo_file.file_id:
                if save_logo(_logo_bytes, _logo_ext):
                    st.session_state.logo_saved_id = _logo_file.file_id
                else:
                    st.warning("The logo is in use for this session, but it could not be saved for later sessions.")

    def _remove_custom_logo():
        remove_saved_logo()
        st.session_state.logo_uploader_version += 1
        st.session_state.logo_saved_id = None

    _brand_cta = st.text_area("Closing message (next steps)", value=_brand_defaults["cta"] or DEFAULT_CTA, height=130,
                              help="Shown at the end of the client snapshot. Edit it freely. Defaults can be set under [report] in secrets.")
    branding = resolve_branding(brand_choice, _custom_name, _brand_cta, _logo_uri,
                                load_saved_logo() if brand_choice == "custom" else "")
    if branding["logo_data"]:
        st.image(branding["logo_data"], width=160)
        if brand_choice == "custom":
            st.button("Remove logo", on_click=_remove_custom_logo)
    elif brand_choice == "custom" and not branding["company"]:
        st.info("No name or logo: reports will carry no branding.")
    st.download_button(
        "📘 Download the 'what we check' handout",
        data=build_checks_reference_html(branding),
        file_name="how_our_website_check_works.html",
        mime="text/html",
        help="A standalone explanation of every check, with your branding, that you can send before running a review.",
    )

    st.markdown("---")
    st.subheader("Saved reports")
    auto_save_reports = st.checkbox(
        "Save reports automatically after each scan",
        value=True,
        help="Writes the client snapshot (a combined report when a CSV covers several sites), technical report, findings CSV and results CSV to the folder below "
             "as soon as a scan you started finishes, so nothing is lost if you move on. The timed auto "
             "re-check does not save.",
    )
    st.caption(f"Folder: `{REPORTS_DIR}`")

    st.markdown("---")
    st.subheader("Browser Verification")
    browser_confirm = False
    st.caption("Browser-based checks are disabled in client accounts; only in-scope, server-side HTTP requests are used.")

    st.markdown("---")
    st.subheader("Email Alerts")
    alert_email = st.text_input("Alert recipient email", placeholder="you@example.com")
    alert_enabled = st.checkbox("Email me when a site is down", value=bool(alert_email))
    if alert_enabled and not smtp_configured():
        st.warning(
            "SMTP isn't set up yet in secrets — emails won't send until it is. "
            "See README for setup steps.",
            icon="⚠️",
        )

    st.markdown("---")
    auto_refresh = st.checkbox("Auto re-check on a timer")
    refresh_interval = None
    if auto_refresh:
        refresh_interval = st.number_input("Re-check every (seconds)", min_value=30, max_value=3600, value=120)
        st.caption("Keep this browser tab open for auto re-checks (and alerts) to keep firing.")

if "results" not in st.session_state:
    st.session_state.results = None
if "previously_down" not in st.session_state:
    st.session_state.previously_down = set()
if "last_urls" not in st.session_state:
    st.session_state.last_urls = None
if "last_link_metadata" not in st.session_state:
    st.session_state.last_link_metadata = None
if "zap_result" not in st.session_state:
    st.session_state.zap_result = None
if "key_hosts" not in st.session_state:
    st.session_state.key_hosts = []  # hosts trusted with the X-ASAP-Key for the current run
KEY_CONFIG["hosts"] = st.session_state.key_hosts
for _k, _v in (("scan_hostnames", []), ("scan_info", None), ("last_scan_info", None), ("host_security", {})):
    if _k not in st.session_state:
        st.session_state[_k] = _v


def set_scan_targets(hostnames):
    """The sites passive security checks apply to: what the user entered, never external links."""
    names = sorted({h for h in hostnames if h})
    st.session_state.scan_hostnames = names
    SECURITY_CONFIG["hostnames"] = names
    SECURITY_CONFIG["hosts"] = {key_host_of(f"https://{h}/") for h in names}


set_scan_targets(st.session_state.scan_hostnames)

input_mode = st.radio(
    "Choose a scan input",
    ["Upload a CSV of URLs", "Scan a website"],
    horizontal=True,
)

urls_to_check = None
link_metadata_for_run = None
scan_info_for_run = None
trigger_check = False
request_budget_for_run = None
zap_only_run = False

if input_mode == "Upload a CSV of URLs":
    st.caption("CSV should have a column named `url` (or similar). If not found, the first column is used.")
    uploaded_file = st.file_uploader("Upload CSV file", type=["csv"])
    csv_crawl_depth = st.selectbox(
        "Link depth for CSV URLs",
        options=[0, 1],
        index=1,
        format_func=lambda depth: {
            0: "0 — CSV URLs only",
            1: "1 — CSV URLs + links on those pages (recommended)",
        }[depth],
        help="Depth 1 checks each CSV URL and links found directly on that page. It does not discover links from those linked pages.",
    )
    csv_max_pages = st.number_input(
        "Maximum pages discovered per CSV URL",
        min_value=1, max_value=300, value=30, step=5,
        help="Caps the crawl starting from each CSV URL. Duplicate pages across roots are checked only once.",
    )
    csv_client_name = st.text_input(
        "Client name for the combined report (optional)",
        help="Shown on the report when the CSV covers more than one site, and used in the file names.",
    )
    csv_one_site = st.checkbox(
        "Check one site at a time (recommended for several sites)",
        value=True,
        help="Finishes each site before starting the next, using at most 2 parallel checks. Sites on shared "
             "infrastructure then see close to the per-site request rate, instead of that rate times the number of sites. Slower.",
    )
    csv_site_pause = st.number_input("Pause between sites (seconds)", min_value=0, max_value=120, value=5, disabled=not csv_one_site)
    csv_request_limit = st.number_input(
        "Total HTTP request limit (crawl + checks)",
        min_value=1, max_value=5000, value=1000, step=50,
    )
    csv_time_limit = st.number_input(
        "Total time limit in minutes (crawl + checks)",
        min_value=1, max_value=60, value=10,
    )

    if uploaded_file is not None:
        try:
            df_input = pd.read_csv(uploaded_file)
        except Exception as e:
            st.error(f"Could not read CSV: {e}")
            st.stop()

        if df_input.empty:
            st.warning("The uploaded CSV is empty.")
            st.stop()

        url_col = detect_url_column(df_input)
        urls = df_input[url_col].dropna().astype(str).tolist()
        urls = [u for u in urls if u.strip()]

        st.success(f"Loaded {len(urls)} website(s) from column **'{url_col}'**.")
        with st.expander("Preview loaded URLs"):
            st.write(urls)

        if st.button("🔍 Check Websites", type="primary"):
            # Normalize and deduplicate the CSV roots before crawling/checking.
            csv_roots = []
            seen_roots = set()
            invalid_roots = []
            for raw_url in urls:
                try:
                    normalized = normalize_url(raw_url)
                    _validate_public_url(normalized, allowed_hosts=CLIENT_ALLOWED_HOSTS)
                    canonical = normalized.split("#", 1)[0]
                    parsed_canonical = urlparse(canonical)
                    # Treat only the bare host and host-root slash as equivalent;
                    # preserve trailing slashes on page paths.
                    if parsed_canonical.path == "/" and not parsed_canonical.query:
                        canonical = urlunparse((parsed_canonical.scheme, parsed_canonical.netloc, "", "", "", ""))
                    if canonical not in seen_roots:
                        seen_roots.add(canonical)
                        csv_roots.append(normalized)
                except (PolicyBlocked, requests.exceptions.RequestException, ValueError) as exc:
                    invalid_roots.append((raw_url, str(exc)))

            if invalid_roots:
                st.warning(f"Skipped {len(invalid_roots)} invalid or disallowed CSV URL(s).")
                with st.expander("Skipped CSV URLs"):
                    for bad_url, reason in invalid_roots[:50]:
                        st.write(f"{bad_url} — {reason}")

            # Trust only the hosts the user listed, and only if they opted in.
            st.session_state.key_hosts = (
                sorted({key_host_of(normalize_url(u)) for u in csv_roots} - {""}) if send_key_for_csv else []
            )
            KEY_CONFIG["hosts"] = st.session_state.key_hosts
            # Apply robots.txt, crawl-delay/rate limiting, and excluded-path rules
            # to every explicitly supplied CSV host, whether or not key sending was
            # opted into. The key itself remains limited to KEY_CONFIG["hosts"].
            KEY_CONFIG["policy_hosts"] = sorted({key_host_of(normalize_url(u)) for u in csv_roots} - {""})
            set_scan_targets([scan_target_of(u) for u in csv_roots])
            _csv_sites = sorted({scan_target_of(u) for u in csv_roots} - {""})
            _security_hosts = sorted({key_host_of(normalize_url(u)) for u in csv_roots} - {""})
            request_budget_for_run = RequestBudget(
                int(csv_request_limit), int(csv_time_limit) * 60,
                allowed_hosts=CLIENT_ALLOWED_HOSTS,
                security_hosts=_security_hosts,
                security_enabled=SECURITY_CONFIG["enabled"],
            )

            discovered = {}
            if int(csv_crawl_depth) == 0:
                for root in csv_roots:
                    page_url = root.split("#", 1)[0]
                    parsed_page = urlparse(page_url)
                    if parsed_page.path == "/" and not parsed_page.query:
                        page_url = urlunparse((parsed_page.scheme, parsed_page.netloc, "", "", "", ""))
                    discovered.setdefault(page_url, {"url": page_url, "type": "Internal", "sources": set(), "depth": 0})
            else:
                crawl_progress = st.progress(0, text="Crawling CSV websites...")
                crawl_errors = []
                for root_index, root in enumerate(csv_roots, start=1):
                    if request_budget_for_run.remaining_seconds() <= 0 or request_budget_for_run.requests_made >= request_budget_for_run.max_requests:
                        break
                    try:
                        pages, _browser_error = crawl_site(
                            root,
                            max_pages=int(csv_max_pages),
                            max_depth=int(csv_crawl_depth),
                            timeout=float(timeout),
                            include_external=False,
                            max_external=0,
                            request_budget=request_budget_for_run,
                            browser_fallback=browser_confirm,
                        )
                        # Report crawl yield per CSV root so blocked or non-HTML pages are visible.
                        root_pages = len(pages)
                        root_errors = [
                            f"{page['url']}: {page['crawl_error']}"
                            for page in pages if page.get("crawl_error")
                            and page.get("crawl_error") != "External links are checked but not crawled"
                        ]
                        if root_pages <= 1:
                            crawl_errors.append(
                                f"{root}: discovered only the root URL. The page may have no crawlable same-host links, "
                                "or the fetch may have been blocked; see page-level crawl diagnostics below."
                            )
                        crawl_errors.extend(root_errors[:10])
                        for page in pages:
                            page_url = page["url"]
                            if page_url not in discovered:
                                discovered[page_url] = {
                                    "url": page_url,
                                    "type": page.get("type", "Internal"),
                                    "sources": set(page.get("sources", set())),
                                    "depth": page.get("depth", 0),
                                    "crawl_status": page.get("crawl_status"),
                                    "crawl_via": page.get("crawl_via", ""),
                                    "crawl_error": page.get("crawl_error", ""),
                                }
                            else:
                                discovered[page_url]["sources"].update(page.get("sources", set()))
                                discovered[page_url]["depth"] = min(discovered[page_url].get("depth", 0), page.get("depth", 0))
                    except (PolicyBlocked, requests.exceptions.RequestException, ValueError) as exc:
                        crawl_errors.append(f"{root}: {exc}")
                    crawl_progress.progress(
                        root_index / max(1, len(csv_roots)),
                        text=f"Crawling CSV websites... {root_index}/{len(csv_roots)} roots processed",
                    )
                crawl_progress.empty()
                if crawl_errors:
                    st.warning(f"Crawl produced limited results or could not fully process {len(crawl_errors)} CSV URL(s).")
                    with st.expander("Crawl messages"):
                        for message in crawl_errors[:50]:
                            st.write(message)

            urls_to_check = list(discovered.keys())
            link_metadata_for_run = {
                page_url: {"type": page["type"], "sources": sorted(page["sources"]), "depth": page.get("depth", 0),
                           "crawl_status": page.get("crawl_status"), "crawl_via": page.get("crawl_via", ""),
                           "crawl_error": page.get("crawl_error", "")}
                for page_url, page in discovered.items()
            }
            trigger_check = bool(urls_to_check)
            scan_info_for_run = {
                "mode": "csv",
                "target": f"CSV list ({len(csv_roots)} root URLs; {len(urls_to_check)} unique pages)",
                "site": _csv_sites[0] if len(_csv_sites) == 1 else (csv_client_name.strip() or f"csv-{len(_csv_sites)}-sites"),
                "sites": _csv_sites,
                "client_name": csv_client_name.strip(),
                "one_site_at_a_time": bool(csv_one_site),
                "mozilla_grades": bool(mozilla_grades),
                "security_enabled": SECURITY_CONFIG["enabled"],
                "security_targets": list(st.session_state.scan_hostnames),
                "site_pause": int(csv_site_pause) if csv_one_site else 0,
                "max_depth": int(csv_crawl_depth),
                "max_pages": int(csv_max_pages),
                "request_limit": int(csv_request_limit),
                "time_limit_minutes": int(csv_time_limit),
            }
            if trigger_check:
                depth_counts = {}
                for meta in discovered.values():
                    d = int(meta.get("depth", 0))
                    depth_counts[d] = depth_counts.get(d, 0) + 1
                depth_summary = ", ".join(
                    f"depth {d}: {depth_counts[d]}" for d in sorted(depth_counts)
                )
                st.success(
                    f"Queued {len(urls_to_check)} unique page(s) from {len(csv_roots)} valid CSV URL(s). "
                    f"Discovery by depth — {depth_summary or 'no pages discovered'}. "
                    f"Depth {int(csv_crawl_depth)} was selected. Depth 0 is the CSV URL; depth 1 is links on CSV pages; "
                    "depth 2 is links on first-level pages. The request and time limits apply to crawling and checks combined."
                )
                if request_budget_for_run.requests_made >= request_budget_for_run.max_requests:
                    st.warning("The HTTP request limit was reached during discovery; remaining checks may be marked skipped.")
                elif request_budget_for_run.remaining_seconds() <= 0:
                    st.warning("The time limit was reached during discovery; remaining checks may be marked skipped.")
            else:
                st.error("No valid URLs were available to check. Please review the CSV and skipped URL messages.")

else:
    scan_mode = st.radio(
        "Choose a website scan",
        ["Quick health check", "Internal link crawl", "Passive security assessment (ZAP Baseline)"],
        horizontal=True,
    )
    for _k, _v in (("crawl_url", ""), ("crawl_max_pages", 30), ("crawl_max_depth", 2),
                   ("crawl_include_external", False), ("crawl_max_external", 75)):
        st.session_state.setdefault(_k, _v)

    if scan_mode == "Internal link crawl":
        saved_sites = [
            site for site in load_sites()
            if key_host_of(normalize_url(site["url"])) in CLIENT_ALLOWED_HOSTS
        ]
        saved_by_url = {x["url"]: x for x in saved_sites}
        if saved_sites:
            if st.session_state.get("saved_site_pick") not in [NEW_SITE_OPTION] + list(saved_by_url):
                st.session_state["saved_site_pick"] = NEW_SITE_OPTION
            st.selectbox(
                "Previously crawled sites",
                [NEW_SITE_OPTION] + list(saved_by_url),
                key="saved_site_pick",
                on_change=apply_saved_site,
                format_func=lambda u: u if u == NEW_SITE_OPTION else
                f"{u}  (last crawled {saved_by_url[u]['last_crawled'][:16] or 'unknown'}, {saved_by_url[u]['times_crawled']}x)",
                help=f"Previously scanned sites. Picking one fills in the address and limits. "
                     f"The list is saved in {os.path.basename(SITES_FILE)} next to the app.",
            )
            if st.session_state.get("saved_site_pick") != NEW_SITE_OPTION:
                st.button("Remove this site from the list", on_click=remove_selected_site)
        else:
            st.caption("Sites you crawl are remembered here, so you can pick them again next time.")
        if st.session_state.get("site_list_save_failed"):
            st.warning(f"Couldn't save the site list to {SITES_FILE}. Check that the folder is writable.", icon="⚠️")

    crawl_url = st.text_input("Website URL", placeholder="https://example.com", key="crawl_url")
    max_pages = 25
    max_depth = 1
    include_external = False
    max_external = 0
    time_limit_minutes = 2
    request_limit = 100

    if scan_mode == "Quick health check":
        st.caption("Checks the home page and up to one level of internal links, with basic passive security checks.")
        max_pages = st.number_input("Max pages (home page plus links)", min_value=1, max_value=100, value=25)
        time_limit_minutes = st.number_input("Time limit (minutes)", min_value=1, max_value=10, value=2)
        request_limit = st.number_input("HTTP request limit", min_value=1, max_value=1000, value=100)
    elif scan_mode == "Internal link crawl":
        st.caption("Follows same-site links only by default. Page, depth, elapsed-time and HTTP-request caps apply to both discovery and checks.")
        col_a, col_b = st.columns(2)
        with col_a:
            max_pages = st.number_input("Max pages to discover", min_value=1, max_value=300, key="crawl_max_pages")
            time_limit_minutes = st.number_input("Time limit (minutes)", min_value=1, max_value=60, value=10)
        with col_b:
            max_depth = st.number_input("Max link depth", min_value=1, max_value=5, key="crawl_max_depth")
            request_limit = st.number_input("HTTP request limit", min_value=1, max_value=5000, value=500, step=25)
        include_external = st.checkbox(
            "Also check external links found on the site (only with permission)",
            key="crawl_include_external",
            help="External links are checked but never crawled further. Their requests also count against the request limit.",
        )
        if include_external:
            max_external = st.number_input(
                "Max external links to include", min_value=1, max_value=300, key="crawl_max_external",
            )
    else:
        st.caption("Runs the local OWASP ZAP Baseline script (passive checks; no active scan). Only assess systems you are authorized to test.")
        zap_command = find_zap_baseline_command()
        if not zap_command:
            st.warning("ZAP Baseline was not found. Install it locally or set ZAP_BASELINE_COMMAND to its executable path.")
        time_limit_minutes = st.number_input("Maximum scan time (minutes)", min_value=1, max_value=30, value=5)
        authorized = st.checkbox("I am authorized to assess this website", key="zap_authorized")

        if st.button("Run passive ZAP Baseline", type="primary", disabled=not bool(zap_command)):
            zap_only_run = True
            try:
                if not authorized:
                    st.error("Confirm authorization before starting the assessment.")
                elif not crawl_url.strip():
                    st.error("Enter a website URL to assess.")
                else:
                    with st.spinner("Running ZAP Baseline..."):
                        st.session_state.zap_result = run_zap_baseline(
                            crawl_url, int(time_limit_minutes), zap_command,
                            allowed_hosts=CLIENT_ALLOWED_HOSTS,
                        )
            except (PolicyBlocked, RuntimeError) as exc:
                st.error(str(exc))

        zap_result = st.session_state.get("zap_result")
        if zap_result:
            st.markdown("### ZAP Baseline results")
            st.write(f"Status: **{zap_result['status']}**; exit code: `{zap_result['exit_code']}`")
            if zap_result.get("report_error"):
                st.warning(zap_result["report_error"])
            if zap_result.get("report") is not None:
                st.json(zap_result["report"])
                st.download_button(
                    "Download ZAP JSON report",
                    data=json.dumps(zap_result["report"], indent=2),
                    file_name="zap-baseline-report.json",
                    mime="application/json",
                )
            with st.expander("ZAP console output"):
                st.code(zap_result["output"])

    if scan_mode != "Passive security assessment (ZAP Baseline)" and st.button(
        "Run quick health check" if scan_mode == "Quick health check" else "Crawl and check internal pages",
        type="primary",
        on_click=save_site_from_form if scan_mode == "Internal link crawl" else None,
    ):
        try:
            normalized_target = _validate_public_url(
                normalize_url(crawl_url), allowed_hosts=CLIENT_ALLOWED_HOSTS,
            )
        except (PolicyBlocked, requests.exceptions.RequestException) as exc:
            st.error(str(exc))
        else:
            entered_host = key_host_of(normalized_target)
            st.session_state.key_hosts = [entered_host] if entered_host else []
            KEY_CONFIG["hosts"] = st.session_state.key_hosts
            KEY_CONFIG["policy_hosts"] = [entered_host] if entered_host else []
            set_scan_targets([scan_target_of(normalized_target)])
            if scan_mode == "Quick health check":
                SECURITY_CONFIG["enabled"] = True
            request_budget_for_run = RequestBudget(
                int(request_limit), int(time_limit_minutes) * 60,
                allowed_hosts=CLIENT_ALLOWED_HOSTS,
                security_hosts=[entered_host],
                security_enabled=SECURITY_CONFIG["enabled"],
            )
            scan_info_for_run = {
                "mode": "quick" if scan_mode == "Quick health check" else "crawl",
                "mozilla_grades": bool(mozilla_grades),
                "target": normalized_target,
                "site": scan_target_of(normalized_target),
                "max_pages": int(max_pages),
                "max_depth": int(max_depth),
                "include_external": include_external,
                "time_limit_minutes": int(time_limit_minutes),
                "request_limit": int(request_limit),
                "security_enabled": SECURITY_CONFIG["enabled"],
                "security_targets": list(st.session_state.scan_hostnames),
            }
            crawl_progress = st.progress(0, text="Discovering pages...")

            def crawl_progress_cb(found, target):
                crawl_progress.progress(min(found / target, 1.0), text=f"Discovered {found}/{target} page(s)...")

            crawl_results, _ = crawl_site(
                normalized_target, max_pages=int(max_pages), max_depth=int(max_depth), timeout=timeout,
                include_external=include_external, max_external=int(max_external),
                progress_cb=crawl_progress_cb, request_budget=request_budget_for_run,
                browser_fallback=browser_confirm,
            )
            crawl_progress.empty()
            internal_pages = [page for page in crawl_results if page["type"] == "Internal"]
            internal_n = len(internal_pages)
            external_n = sum(1 for page in crawl_results if page["type"] == "External")
            depth_counts = {}
            for page in internal_pages:
                d = int(page.get("depth", 0))
                depth_counts[d] = depth_counts.get(d, 0) + 1
            depth_summary = ", ".join(f"depth {d}: {n}" for d, n in sorted(depth_counts.items()))
            st.success(
                f"Discovered {internal_n} internal page(s)"
                + (f" and {external_n} external link(s)" if include_external else "")
                + (f" ({depth_summary})" if depth_summary else "")
                + ". Checking status and passive security now..."
            )
            crawl_errors = [
                f"{page['url']}: {page['crawl_error']}"
                for page in crawl_results if page.get("crawl_error")
                and page.get("crawl_error") != "External links are checked but not crawled"
            ]
            roots_with_no_links = [
                page for page in internal_pages
                if page.get("depth", 0) == 0 and not page.get("links_found") and not page.get("crawl_error")
            ]
            if internal_n <= 1 or crawl_errors:
                st.warning(
                    "The crawler found few or no internal pages, or encountered crawl errors. "
                    "Review the diagnostics below; the starting URL alone does not prove the site has no other pages."
                )
            if crawl_errors or roots_with_no_links:
                with st.expander("Website crawl diagnostics", expanded=True):
                    for page in internal_pages:
                        st.write(
                            f"Depth {page.get('depth', 0)} — {page['url']} — "
                            f"links found: {page.get('links_found', 0)}"
                            + (f" — {page['crawl_error']}" if page.get('crawl_error') else "")
                        )
                    if not crawl_errors and roots_with_no_links:
                        st.write("No anchor links were extracted from the starting page. The site may render navigation with JavaScript, or the fetched response may differ from the browser page.")
            if request_budget_for_run.requests_made >= request_budget_for_run.max_requests:
                st.warning("The HTTP request limit was reached during discovery; remaining checks will be marked skipped.")
            elif request_budget_for_run.remaining_seconds() <= 0:
                st.warning("The time limit was reached during discovery; remaining checks will be marked skipped.")
            urls_to_check = [page["url"] for page in crawl_results]
            link_metadata_for_run = {
                page["url"]: {
                    "type": page["type"],
                    "sources": page["sources"],
                    "depth": page.get("depth", 0),
                    "links_found": page.get("links_found", 0),
                    "crawl_error": page.get("crawl_error", ""),
                    "crawl_status": page.get("crawl_status"),
                    "crawl_via": page.get("crawl_via", ""),
                }
                for page in crawl_results
            }
            trigger_check = True

if trigger_check and urls_to_check:
    st.session_state.last_urls = urls_to_check
    st.session_state.last_link_metadata = link_metadata_for_run
    st.session_state.last_scan_info = scan_info_for_run

if trigger_check or (
    not zap_only_run and auto_refresh
    and st.session_state.results is not None and st.session_state.last_urls
):
    urls_for_this_run = urls_to_check if trigger_check else st.session_state.last_urls
    metadata_for_this_run = link_metadata_for_run if trigger_check else st.session_state.last_link_metadata
    if trigger_check:
        check_budget = request_budget_for_run
    else:
        previous_scan = st.session_state.last_scan_info or {}
        check_budget = (
            RequestBudget(
                previous_scan["request_limit"],
                previous_scan["time_limit_minutes"] * 60,
                allowed_hosts=CLIENT_ALLOWED_HOSTS,
                security_hosts=previous_scan.get("security_targets", []),
                security_enabled=previous_scan.get("security_enabled"),
            )
            if previous_scan.get("request_limit") and previous_scan.get("time_limit_minutes")
            else None
        )
    perform_full_check(
        urls_for_this_run, timeout=timeout, max_workers=max_workers,
        browser_confirm=browser_confirm,
        alert_enabled=alert_enabled, alert_email=alert_email,
        link_metadata=metadata_for_this_run,
        scan_info=scan_info_for_run if trigger_check else st.session_state.last_scan_info,
        branding=branding,
        save_reports=auto_save_reports if trigger_check else None,
        request_budget=check_budget,
    )

if st.session_state.results:
    results = st.session_state.results
    df = results_dataframe(results)
    scan_meta = st.session_state.scan_info or {}
    host_security = st.session_state.host_security or {}

    total = len(df)
    up_count = (df["Status"] == "Up").sum()
    down_count = (df["Status"] == "Down").sum()

    _saved = st.session_state.get("saved_reports")
    if _saved:
        if _saved["files"]:
            st.success(
                f"{len(_saved['files'])} report files were saved automatically (scan finished {_saved['finished']}) in `{_saved['dir']}`",
                icon="💾",
            )
            with st.expander("Saved files"):
                st.markdown("\n".join(f"- `{name}`" for name in _saved["files"]))
        if _saved["error"]:
            st.warning(f"Not everything could be saved: {_saved['error']}. The download buttons below still work.", icon="⚠️")

    st.markdown("### Summary")
    server_error_rows = df[df["Status"] == "Degraded"]
    m1, m2, m3, m3b, m4 = st.columns(5)
    m1.metric("Total Pages/Sites", total)
    m2.metric("Up", int(up_count))
    m3.metric("Broken", int(down_count))
    m3b.metric("Server Errors", len(server_error_rows))
    avg_rt = df.loc[df["Status"] == "Up", "Response Time (ms)"].mean()
    m4.metric("Avg Response Time", f"{avg_rt:.0f} ms" if pd.notna(avg_rt) else "N/A")

    if scan_meta.get("security_enabled"):
        _cov = coverage_stats(results)
        if _cov["eligible"] and _cov["analyzed"] < _cov["eligible"]:
            st.warning(
                f"Security checks analyzed {_cov['analyzed']} of {_cov['eligible']} requested page(s). "
                "The Security Analysis column gives the reason for each page.",
                icon="⚠️",
            )

    status_counts = df["Status"].value_counts().to_dict()
    inconclusive_count = sum(int(status_counts.get(k, 0)) for k in UNCONFIRMED_STATUSES)
    if not server_error_rows.empty:
        st.warning(f"{len(server_error_rows)} page(s) failed repeatedly with server errors. Check logs and load balancer target health.", icon="⚠️")
        st.dataframe(server_error_rows[[c for c in ("URL", "Site", "Status Code", "Error", "Server Error Check") if c in df.columns]],
                     use_container_width=True, hide_index=True)
    if inconclusive_count:
        st.warning(
            f"Not confirmed healthy or broken: {inconclusive_count} restricted, blocked, challenged, or unknown. "
            "Review these separately from confirmed broken links.",
            icon="⚠️",
        )
        review_rows = df[df["Status"].isin(UNCONFIRMED_STATUSES)]
        if not review_rows.empty:
            st.dataframe(review_rows, use_container_width=True, hide_index=True)

    skipped_count = int((df["Status"] == "Skipped").sum())
    if skipped_count:
        st.info(
            f"{skipped_count} URL(s) were not requested, because robots.txt disallows them or they "
            "match an excluded RFQ/contact path. They show as 'Skipped' in the results below.",
            icon="ℹ️",
        )

    if down_count > 0:
        st.error(f"⚠️ {down_count} page(s)/site(s) are currently down!")
        down_cols = ["URL", "Status", "Status Code", "Error", "Checked Via", "Checked At"]
        if "Link Type" in df.columns and (df["Link Type"] != "—").any():
            down_cols = ["URL", "Link Type", "Found On", "Status", "Status Code", "Error", "Checked At"]
        st.dataframe(
            df[df["Status"] == "Down"][down_cols],
            use_container_width=True,
            hide_index=True,
        )

        if SELENIUM_AVAILABLE:
            st.caption("Browser retries are disabled for client accounts to keep checks within assigned hostnames.")

    if scan_meta.get("security_enabled"):
        st.markdown("### Security Checks (passive)")
        groups = group_findings(results, host_security)
        issues = [g for g in groups if g["severity"] != "Info"]
        analyzed = coverage_stats(results)["analyzed"]
        s1, s2, s3, s4 = st.columns(4)
        s1.metric("High", sum(1 for g in issues if g["severity"] == "High"))
        s2.metric("Medium", sum(1 for g in issues if g["severity"] == "Medium"))
        s3.metric("Low", sum(1 for g in issues if g["severity"] == "Low"))
        s4.metric("Pages analyzed", analyzed)
        st.caption("Counts are of distinct finding types, not of affected pages.")
        if any(g["id"] == "challenge-page" for g in groups):
            st.warning(
                "Some responses were bot-protection challenge pages, so they could not be analyzed. "
                "Check that the crawler key is accepted for this site.", icon="⚠️",
            )
        shown = [g for g in groups if g["id"] != "tls-ok"]
        if shown:
            sec_df = pd.DataFrame([{
                "Severity": g["severity"],
                "Finding": g["title"],
                "Affects": f"{len(g['items'])} {'site' if g['scope'] == 'Site' else 'page'}(s)",
                "Example": str(g["items"][0][0]),
                "Recommendation": g["fix"],
            } for g in shown])
            st.dataframe(sec_df.style.map(style_severity, subset=["Severity"]), use_container_width=True, hide_index=True)
            with st.expander("Affected pages for a finding"):
                chosen = st.selectbox("Finding", [g["title"] for g in shown])
                g = next(x for x in shown if x["title"] == chosen)
                st.dataframe(
                    pd.DataFrame([{"Affected": w, "Detail": d} for w, d in g["items"]]),
                    use_container_width=True, hide_index=True,
                )
        elif analyzed:
            st.success("No findings from the passive checks.")
        if host_security:
            with st.expander("Site-level checks (TLS certificate, security.txt)"):
                st.dataframe(pd.DataFrame([{
                    "Site": host,
                    "TLS": (f"Verification failed: {hs['tls']['error']}" if hs["tls"]["error_kind"] == "verify"
                            else f"Valid until {hs['tls']['not_after']} ({hs['tls']['days_left']} days), {hs['tls']['version']}"
                            if hs["tls"]["days_left"] is not None else hs["tls"]["error"] or "not checked"),
                    "security.txt": hs["security_txt"] + (f" ({hs['security_txt_note']})" if hs["security_txt_note"] else ""),
                    "HTTP redirect": (hs.get("redirect") or {}).get("detail", "Not checked"),
                    **({"Mozilla grade": hs["mozilla"].get("grade") or hs["mozilla"].get("error", "")} if hs.get("mozilla") else {}),
                } for host, hs in sorted(host_security.items())]), use_container_width=True, hide_index=True)
        st.caption(
            "Passive checks only: response headers and page content already fetched, no probing. "
            "A clean result is not proof of security and this is not a penetration test."
        )

    st.markdown("### Full Results")
    st.dataframe(
        df.style.map(style_status, subset=["Status"]),
        use_container_width=True,
        hide_index=True,
    )

    _stamp = scan_stamp(scan_meta)  # same time as the automatically saved files, so the names match
    if scan_meta.get("security_enabled"):
        st.download_button(
            "📄 Client snapshot (HTML, printable to PDF)",
            data=build_client_report_html(results, scan_meta, host_security, branding),
            file_name=scan_file_name("client_snapshot", scan_meta, "html", _stamp),
            mime="text/html",
            help="Clean summary to present: what is down, what we recommend, and why. Multi-site scans are consolidated into one report.",
        )
    st.download_button(
        "🛠️ Technical report (HTML, printable to PDF)",
        data=build_report_html(results, scan_meta, host_security, branding),
        file_name=scan_file_name("scan_report", scan_meta, "html", _stamp),
        mime="text/html",
        help="Full detail for IT: every affected page, the fix, and exactly how each check works.",
    )
    if scan_meta.get("security_enabled"):
        st.download_button(
            "⬇️ Download security findings (CSV)",
            data=findings_csv(results, host_security),
            file_name=scan_file_name("security_findings", scan_meta, "csv", _stamp),
            mime="text/csv",
        )

    csv_buffer = io.StringIO()
    df.to_csv(csv_buffer, index=False)
    st.download_button(
        "⬇️ Download Results as CSV",
        data=csv_buffer.getvalue(),
        file_name=scan_file_name("uptime_results", scan_meta, "csv", _stamp),
        mime="text/csv",
    )

    st.caption(f"Last checked: {df['Checked At'].iloc[0] if len(df) else '—'}")

    if auto_refresh and refresh_interval:
        st.caption(f"Auto-refreshing every {refresh_interval} seconds...")
        time.sleep(refresh_interval)
        st.rerun()
else:
    st.info("Choose an input method above, then run a check to get started.")
    st.markdown("**Example CSV format:**")
    st.code("url\nhttps://www.google.com\nhttps://www.github.com\nhttps://example.com", language="text")
