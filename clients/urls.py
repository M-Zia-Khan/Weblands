from django.urls import path

from . import views


urlpatterns = [
    path("", views.dashboard, name="dashboard"),
    path("scan/", views.start_scan, name="start_scan"),
    path("scans/<int:scan_id>/", views.scan_detail, name="scan_detail"),
    path("scans/<int:scan_id>/report/", views.download_report, name="download_report"),
    path("scans/<int:scan_id>/results.csv", views.download_results, name="download_results"),
]
