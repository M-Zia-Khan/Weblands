from django.conf import settings
from django.core.exceptions import ValidationError
from django.db import models

from checker_engine import normalize_client_host


class AllowedHost(models.Model):
    user = models.ForeignKey(
        settings.AUTH_USER_MODEL,
        on_delete=models.CASCADE,
        related_name="allowed_hosts",
    )
    hostname = models.CharField(max_length=253)

    class Meta:
        ordering = ["hostname"]
        constraints = [
            models.UniqueConstraint(fields=["user", "hostname"], name="unique_user_allowed_host")
        ]

    def clean(self):
        try:
            self.hostname = normalize_client_host(self.hostname)
        except ValueError as exc:
            raise ValidationError({"hostname": str(exc)}) from exc

    def save(self, *args, **kwargs):
        self.full_clean()
        return super().save(*args, **kwargs)

    def __str__(self):
        return f"{self.user}: {self.hostname}"


class ScanRun(models.Model):
    class Status(models.TextChoices):
        RUNNING = "running", "Running"
        COMPLETE = "complete", "Complete"
        FAILED = "failed", "Failed"

    user = models.ForeignKey(
        settings.AUTH_USER_MODEL,
        on_delete=models.CASCADE,
        related_name="scan_runs",
    )
    status = models.CharField(max_length=12, choices=Status.choices, default=Status.RUNNING)
    target = models.CharField(max_length=500)
    created_at = models.DateTimeField(auto_now_add=True)
    finished_at = models.DateTimeField(null=True, blank=True)
    results = models.JSONField(default=list, blank=True)
    host_security = models.JSONField(default=dict, blank=True)
    scan_info = models.JSONField(default=dict, blank=True)
    error_message = models.CharField(max_length=300, blank=True)

    class Meta:
        ordering = ["-created_at"]

    def __str__(self):
        return f"{self.target} ({self.get_status_display()})"
