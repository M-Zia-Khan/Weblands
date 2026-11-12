import csv
import io
import logging
import threading
from datetime import datetime, timezone
from urllib.parse import urlparse

from django.core.exceptions import ValidationError

import checker_engine as engine
from .models import AllowedHost


logger = logging.getLogger(__name__)
SCAN_LOCK = threading.Lock()
MAX_CSV_BYTES = 1_000_000
MAX_CSV_ROOTS = 5
MAX_PAGES_PER_ROOT = 25
MAX_REQUESTS_PER_SCAN = 150
MAX_SCAN_SECONDS = 120


def _csv_urls(uploaded_file):
    raw = uploaded_file.read(MAX_CSV_BYTES + 1)
    if len(raw) > MAX_CSV_BYTES:
        raise ValidationError("The CSV must be 1 MB or smaller.")
    try:
        text = raw.decode("utf-8-sig")
    except UnicodeDecodeError as exc:
        raise ValidationError("The CSV must use UTF-8 encoding.") from exc
    try:
        rows = list(csv.reader(io.StringIO(text)))
    except csv.Error as exc:
        raise ValidationError("The uploaded file is not a valid CSV.") from exc
    if not rows or not rows[0]:
        raise ValidationError("The CSV is empty.")

    candidates = {"url", "urls", "website", "websites", "link", "links", "address", "site"}
    header = [cell.strip().lower() for cell in rows[0]]
    matching_columns = [index for index, value in enumerate(header) if value in candidates]
    column_index = matching_columns[0] if matching_columns else 0
    data_rows = rows[1:] if matching_columns else rows
    values = [row[column_index].strip() for row in data_rows if len(row) > column_index and row[column_index].strip()]
    if not values:
        raise ValidationError("No website URLs were found in the CSV.")
    if len(values) > MAX_CSV_ROOTS:
        raise ValidationError(f"A CSV may contain at most {MAX_CSV_ROOTS} website URLs.")
    return values


def _validate_roots(raw_urls, allowed_hosts):
    roots = []
    seen = set()
    errors = []
    for raw_url in raw_urls:
        try:
            normalized = engine.normalize_url(raw_url)
            parsed = urlparse(normalized)
            hostname = engine.normalize_client_host(parsed.hostname or "")
            if hostname not in allowed_hosts:
                errors.append(f"{raw_url}: hostname is not assigned to this account")
                continue
            engine._validate_public_url(
                normalized,
                allowed_hosts=allowed_hosts,
                allowed_ports={80, 443},
                allow_private_targets=False,
            )
            canonical = normalized.split("#", 1)[0]
            if canonical not in seen:
                seen.add(canonical)
                roots.append(canonical)
        except (engine.PolicyBlocked, engine.requests.exceptions.RequestException, ValueError) as exc:
            errors.append(f"{raw_url}: {exc}")
    if errors:
        raise ValidationError(errors[:10])
    if not roots:
        raise ValidationError("No valid website URLs were provided.")
    return roots


def run_scan(user, raw_urls):
    allowed_hosts = frozenset(
        AllowedHost.objects.filter(user=user).values_list("hostname", flat=True)
    )
    if not allowed_hosts:
        raise ValidationError("No websites are assigned to your account. Contact your administrator.")

    roots = _validate_roots(raw_urls, allowed_hosts)
    with SCAN_LOCK:
        old_key_config = {
            key: value.copy() if isinstance(value, (list, dict)) else value
            for key, value in engine.KEY_CONFIG.items()
        }
        old_security_config = {
            key: value.copy() if isinstance(value, (list, set, dict)) else value
            for key, value in engine.SECURITY_CONFIG.items()
        }
        try:
            started = datetime.now(timezone.utc).isoformat()
            security_targets = sorted({engine.scan_target_of(url) for url in roots})
            security_hosts = sorted({engine.key_host_of(url) for url in roots})
            engine.KEY_CONFIG.update(
                key="",
                hosts=[],
                policy_hosts=sorted(allowed_hosts),
                user_agent=engine.DEFAULT_USER_AGENT,
                rps=1.0,
                blocked_paths=["rfq", "/contact"],
            )
            engine.SECURITY_CONFIG.update(
                enabled=True,
                hosts=set(security_hosts),
                hostnames=security_targets,
            )
            budget = engine.RequestBudget(
                MAX_REQUESTS_PER_SCAN,
                MAX_SCAN_SECONDS,
                allowed_hosts=allowed_hosts,
                security_hosts=security_hosts,
                security_enabled=True,
                allowed_ports={80, 443},
                allow_private_targets=False,
            )

            discovered = {}
            for root in roots:
                pages, _browser_error = engine.crawl_site(
                    root,
                    max_pages=MAX_PAGES_PER_ROOT,
                    max_depth=1,
                    timeout=8,
                    include_external=False,
                    request_budget=budget,
                    browser_fallback=False,
                )
                for page in pages:
                    url = page["url"]
                    if url not in discovered:
                        discovered[url] = {
                            **page,
                            "sources": set(page.get("sources") or ()),
                        }
                    else:
                        discovered[url]["sources"].update(page.get("sources") or ())

            urls = list(discovered)
            results = engine.run_checks(
                urls,
                timeout=8,
                max_workers=3,
                request_budget=budget,
                one_site_at_a_time=True,
            )
            for result in results:
                page = discovered.get(result["URL"], {})
                result.update({
                    "Site": engine.key_host_of(result["URL"]),
                    "Link Type": page.get("type", "Internal"),
                    "Found On": "; ".join(sorted(page.get("sources") or ())) or "(starting page)",
                    "Crawl Depth": page.get("depth", 0),
                    "Links Found On Page": page.get("links_found", 0),
                    "Crawl Error": page.get("crawl_error", ""),
                })
            engine.confirm_down_internal_links(
                results,
                timeout=8,
                request_budget=budget,
                retry_attempts=2,
            )

            host_security = engine.run_host_checks(security_targets, request_budget=budget)
            finished = datetime.now(timezone.utc).isoformat()
            scan_info = {
                "mode": "crawl" if len(roots) == 1 else "csv",
                "target": roots[0] if len(roots) == 1 else f"{len(roots)} assigned websites",
                "site": security_targets[0] if len(security_targets) == 1 else f"{len(security_targets)} websites",
                "sites": security_targets,
                "started": started,
                "finished": finished,
                "security_enabled": True,
                "security_targets": security_targets,
                "max_pages": MAX_PAGES_PER_ROOT,
                "max_depth": 1,
                "request_limit": MAX_REQUESTS_PER_SCAN,
                "requests_made": budget.requests_made,
                "time_limit_minutes": MAX_SCAN_SECONDS // 60,
                "engine_version": "11a",
                "max_response_bytes": engine.MAX_RESPONSE_BYTES,
                "max_redirects": engine.MAX_REDIRECTS,
                "target_policy": "Assigned public hosts only; non-public addresses and out-of-scope redirects are blocked",
                "browser_confirm": False,
            }
            return {
                "roots": roots,
                "results": results,
                "host_security": host_security,
                "scan_info": scan_info,
            }
        except Exception:
            logger.exception("Website scan failed for user %s", user.pk)
            raise
        finally:
            engine.KEY_CONFIG.clear()
            engine.KEY_CONFIG.update(old_key_config)
            engine.SECURITY_CONFIG.clear()
            engine.SECURITY_CONFIG.update(old_security_config)
