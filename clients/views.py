import logging

from django.contrib import messages
from django.contrib.auth.decorators import login_required
from django.core.exceptions import ValidationError
from django.http import HttpResponse
from django.shortcuts import get_object_or_404, redirect, render
from django.utils import timezone

import checker_engine as engine
from .forms import ScanForm
from .models import AllowedHost, ScanRun
from .scan_service import _csv_urls, run_scan


logger = logging.getLogger(__name__)


@login_required
def dashboard(request):
    form = ScanForm()
    hosts = AllowedHost.objects.filter(user=request.user)
    scans = ScanRun.objects.filter(user=request.user)[:10]
    return render(
        request,
        "clients/dashboard.html",
        {"form": form, "hosts": hosts, "scans": scans},
    )


@login_required
def start_scan(request):
    if request.method != "POST":
        return redirect("dashboard")

    form = ScanForm(request.POST, request.FILES)
    if not form.is_valid():
        return render(
            request,
            "clients/dashboard.html",
            {
                "form": form,
                "hosts": AllowedHost.objects.filter(user=request.user),
                "scans": ScanRun.objects.filter(user=request.user)[:10],
            },
            status=400,
        )

    if form.cleaned_data["scan_type"] == "website":
        raw_urls = [form.cleaned_data["website_url"]]
    else:
        try:
            raw_urls = _csv_urls(form.cleaned_data["csv_file"])
        except ValidationError as exc:
            form.add_error("csv_file", exc)
            return render(
                request,
                "clients/dashboard.html",
                {
                    "form": form,
                    "hosts": AllowedHost.objects.filter(user=request.user),
                    "scans": ScanRun.objects.filter(user=request.user)[:10],
                },
                status=400,
            )

    scan = ScanRun.objects.create(
        user=request.user,
        target=raw_urls[0] if len(raw_urls) == 1 else f"{len(raw_urls)} uploaded websites",
    )
    try:
        outcome = run_scan(request.user, raw_urls)
    except ValidationError as exc:
        scan.delete()
        form.add_error(None, exc)
        return render(
            request,
            "clients/dashboard.html",
            {
                "form": form,
                "hosts": AllowedHost.objects.filter(user=request.user),
                "scans": ScanRun.objects.filter(user=request.user)[:10],
            },
            status=400,
        )
    except Exception as exc:
        scan.status = ScanRun.Status.FAILED
        scan.error_message = f"Scan failed ({type(exc).__name__}). Please try again or contact support."
        scan.finished_at = timezone.now()
        scan.save(update_fields=("status", "error_message", "finished_at"))
        logger.exception("Scan %s failed", scan.pk)
        messages.error(request, scan.error_message)
        return redirect("scan_detail", scan_id=scan.pk)

    scan.target = outcome["scan_info"]["target"]
    scan.results = outcome["results"]
    scan.host_security = outcome["host_security"]
    scan.scan_info = outcome["scan_info"]
    scan.status = ScanRun.Status.COMPLETE
    scan.finished_at = timezone.now()
    scan.save(
        update_fields=(
            "target",
            "results",
            "host_security",
            "scan_info",
            "status",
            "finished_at",
        )
    )
    messages.success(request, "Website check completed.")
    return redirect("scan_detail", scan_id=scan.pk)


@login_required
def scan_detail(request, scan_id):
    scan = get_object_or_404(ScanRun, pk=scan_id, user=request.user)
    results = [
        {
            **row,
            "status_code": row.get("Status Code"),
            "response_time": row.get("Response Time (ms)"),
            "security_analysis": row.get("Security Analysis"),
        }
        for row in scan.results
    ] if isinstance(scan.results, list) else []
    findings = engine.group_findings(scan.results, scan.host_security)
    summary = {
        "total": len(results),
        "up": sum(row.get("Status") == "Up" for row in results),
        "down": sum(row.get("Status") == "Down" for row in results),
        "other": sum(row.get("Status") not in {"Up", "Down"} for row in results),
    }
    return render(
        request,
        "clients/scan_detail.html",
        {"scan": scan, "results": results, "findings": findings, "summary": summary},
    )


@login_required
def download_report(request, scan_id):
    scan = get_object_or_404(
        ScanRun, pk=scan_id, user=request.user, status=ScanRun.Status.COMPLETE
    )
    html = engine.build_client_report_html(
        scan.results,
        scan.scan_info,
        scan.host_security,
        branding={},
    )
    response = HttpResponse(html, content_type="text/html; charset=utf-8")
    response["Content-Disposition"] = f'attachment; filename="client-report-{scan.pk}.html"'
    return response


@login_required
def download_results(request, scan_id):
    scan = get_object_or_404(
        ScanRun, pk=scan_id, user=request.user, status=ScanRun.Status.COMPLETE
    )
    frame = engine.results_dataframe(scan.results)
    response = HttpResponse(frame.to_csv(index=False), content_type="text/csv; charset=utf-8")
    response["Content-Disposition"] = f'attachment; filename="website-results-{scan.pk}.csv"'
    return response
