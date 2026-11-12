import socket
from unittest.mock import patch

from django.contrib.auth.models import User
from django.core.exceptions import ValidationError
from django.test import TestCase
from django.urls import reverse

import checker_engine as engine
from .models import AllowedHost, ScanRun
from .scan_service import _csv_urls, run_scan


def public_dns_answer(*args, **kwargs):
    return [(socket.AF_INET, socket.SOCK_STREAM, 6, "", ("93.184.216.34", 443))]


class ClientPortalTests(TestCase):
    def setUp(self):
        self.client_user = User.objects.create_user(username="client-a", password="correct-horse")
        self.other_user = User.objects.create_user(username="client-b", password="another-password")
        self.host = AllowedHost.objects.create(user=self.client_user, hostname="www.example.com")
        self.other_host = AllowedHost.objects.create(user=self.other_user, hostname="other.example")

    def test_dashboard_requires_login(self):
        response = self.client.get(reverse("dashboard"))
        self.assertRedirects(response, f"{reverse('login')}?next={reverse('dashboard')}")

    def test_login_dashboard_shows_only_assigned_hosts(self):
        self.assertTrue(self.client.login(username="client-a", password="correct-horse"))
        response = self.client.get(reverse("dashboard"))
        self.assertContains(response, "example.com")
        self.assertNotContains(response, "other.example")

    def test_scan_history_is_owner_scoped(self):
        other_scan = ScanRun.objects.create(user=self.other_user, target="other.example")
        self.client.force_login(self.client_user)
        response = self.client.get(reverse("scan_detail", args=[other_scan.pk]))
        self.assertEqual(response.status_code, 404)

    def test_out_of_scope_hostname_is_rejected_before_network_lookup(self):
        with self.assertRaises(ValidationError):
            run_scan(self.client_user, ["https://not-assigned.example"])

    def test_nonstandard_ports_are_rejected(self):
        with self.assertRaises(ValidationError):
            run_scan(self.client_user, ["https://example.com:8443"])

    @patch.dict("os.environ", {"UPTIME_ALLOW_PRIVATE_TARGETS": "true"})
    @patch(
        "clients.scan_service.engine.socket.getaddrinfo",
        return_value=[(socket.AF_INET, socket.SOCK_STREAM, 6, "", ("127.0.0.1", 443))],
    )
    def test_client_scans_never_allow_private_targets(self, _dns):
        with self.assertRaises(ValidationError):
            run_scan(self.client_user, ["https://example.com"])

    def test_csv_accepts_headered_and_headerless_inputs(self):
        class Upload:
            def __init__(self, value):
                self.value = value.encode("utf-8")

            def read(self, size):
                return self.value[:size]

        self.assertEqual(_csv_urls(Upload("url\nhttps://example.com\n")), ["https://example.com"])
        self.assertEqual(_csv_urls(Upload("https://example.com\n")), ["https://example.com"])

    @patch("clients.scan_service.engine.run_host_checks", return_value={})
    @patch("clients.scan_service.engine.run_checks")
    @patch("clients.scan_service.engine.crawl_site")
    @patch("clients.scan_service.engine.socket.getaddrinfo", side_effect=public_dns_answer)
    def test_scan_runs_through_existing_engine_and_saves_private_history(
        self, _dns, crawl, checks, _host_checks
    ):
        crawl.return_value = (
            [{
                "url": "https://example.com",
                "type": "Internal",
                "sources": set(),
                "depth": 0,
                "links_found": 0,
                "crawl_error": "",
            }],
            None,
        )
        checks.return_value = [{
            "URL": "https://example.com",
            "Status": "Up",
            "Status Code": 200,
            "Response Time (ms)": 20,
            "Error": "",
            "Checked At": "2026-11-11 12:00:00",
            "Security Analysis": "Analyzed",
        }]

        result = run_scan(self.client_user, ["https://example.com"])

        self.assertEqual(result["results"][0]["Status"], "Up")
        self.assertEqual(result["scan_info"]["security_enabled"], True)
        budget = checks.call_args.kwargs["request_budget"]
        self.assertEqual(budget.allowed_hosts, frozenset({"example.com"}))
        with self.assertRaises(engine.PolicyBlocked):
            engine._validate_public_url("https://outside.example", request_budget=budget)
        with self.assertRaises(engine.PolicyBlocked):
            engine._validate_public_url("https://example.com:8443", request_budget=budget)
        crawl.assert_called_once()

    def test_user_cannot_download_another_clients_results(self):
        other_scan = ScanRun.objects.create(
            user=self.other_user,
            target="other.example",
            status=ScanRun.Status.COMPLETE,
        )
        self.client.force_login(self.client_user)
        response = self.client.get(reverse("download_results", args=[other_scan.pk]))
        self.assertEqual(response.status_code, 404)

    def test_owner_can_download_html_report(self):
        scan = ScanRun.objects.create(
            user=self.client_user,
            target="example.com",
            status=ScanRun.Status.COMPLETE,
            scan_info={
                "mode": "quick",
                "target": "https://example.com",
                "site": "example.com",
                "sites": ["example.com"],
                "started": "2026-11-11T12:00:00+00:00",
                "finished": "2026-11-11T12:01:00+00:00",
                "security_enabled": True,
            },
        )
        self.client.force_login(self.client_user)
        response = self.client.get(reverse("download_report", args=[scan.pk]))
        self.assertEqual(response.status_code, 200)
        self.assertEqual(response["Content-Type"], "text/html; charset=utf-8")
        self.assertIn("attachment;", response["Content-Disposition"])
        self.assertContains(response, "<html", html=False)

    def test_owner_can_view_scan_results(self):
        scan = ScanRun.objects.create(
            user=self.client_user,
            target="example.com",
            status=ScanRun.Status.COMPLETE,
            results=[{
                "URL": "https://example.com",
                "Status": "Up",
                "Status Code": 200,
                "Response Time (ms)": 20,
                "Security Analysis": "Analyzed",
                "Error": "",
            }],
            scan_info={"security_enabled": True},
        )
        self.client.force_login(self.client_user)
        response = self.client.get(reverse("scan_detail", args=[scan.pk]))
        self.assertEqual(response.status_code, 200)
        self.assertContains(response, "https://example.com")
        self.assertContains(response, "Passive security findings")
