# Client Website Uptime Checker

The client portal now runs on Django. It reuses the bounded HTTP crawler, response analysis, TLS checks, passive security checks, and client-report generator from the original checker. The Streamlit UI in `uptime_checker.py` is retained as a legacy reference; run the Django portal below.

## Local setup (PowerShell)

```powershell
python -m venv .venv
.\.venv\Scripts\Activate.ps1
python -m pip install -r requirements.txt
$env:DJANGO_DEBUG = "true"
$env:DJANGO_SECRET_KEY = python -c "import secrets; print(secrets.token_urlsafe(50))"
python manage.py migrate
python manage.py createsuperuser
python manage.py runserver
```

Open `http://127.0.0.1:8000/admin/`, sign in as the administrator, create each client as a Django user, and add that user's assigned hostnames under **Allowed hosts**. Clients sign in at `http://127.0.0.1:8000/login/`. The `www.` prefix is normalized; subdomains and other hostnames must be assigned explicitly.

## Client checks and scope

- Clients can check one assigned website or upload a CSV containing up to five assigned URLs.
- Each crawl is limited to 25 pages per root and one link level. Requests are capped by a shared request/time budget and use the existing robots.txt and rate-limit rules.
- URLs must resolve to public Internet addresses. The initial URL, discovered pages, redirects, TLS checks, and site-level checks are restricted to the client's assigned hostnames and standard HTTP/HTTPS ports. External links are not crawled.
- Checks are passive and non-destructive; this is not a penetration test. Browser automation and shared crawler-key forwarding are not enabled in the client portal.
- Scan history and report downloads are account-scoped and stored in the configured Django database.

## Production deployment

Set `DJANGO_SECRET_KEY` to a unique secret, `DJANGO_ALLOWED_HOSTS` to the portal's hostnames, and keep `DJANGO_DEBUG=false`. Use HTTPS, a production WSGI/ASGI server, a production database, backups, and network egress controls. If TLS terminates at a reverse proxy, set `DJANGO_TRUST_PROXY_SSL_HEADER=true` only when that trusted proxy removes client-supplied forwarding headers and sets `X-Forwarded-Proto` itself. Set `DJANGO_CSRF_TRUSTED_ORIGINS` when the portal needs explicit trusted origins. Protect login endpoints with rate limiting at the reverse proxy.

Scans currently run synchronously in the web request, with strict page, request, and time caps. This is appropriate for a small pilot; for a larger client rollout, move scan execution to a supervised background queue (for example Celery) before scaling web workers. Keep the existing host allowlist checks in the worker.

## Configuration

- `DJANGO_DATABASE`: optional Django database path; SQLite is the local default.
- `DJANGO_SECURE_SSL_REDIRECT`: defaults to enabled outside debug mode.
- `DJANGO_SECURE_HSTS_SECONDS`: defaults to one year outside debug mode. Review this before deployment, especially if subdomains are not all HTTPS-ready.
- `UPTIME_MAX_RESPONSE_BYTES`: optional response-body size cap for the shared checker engine.

Django's deployment check warns that HSTS is not extended to subdomains or preload-enabled. Those settings are intentionally left off until you verify every subdomain is HTTPS-only and are ready to request browser preload inclusion.
