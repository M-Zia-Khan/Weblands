from django.contrib import admin
from django.contrib.auth.admin import UserAdmin
from django.contrib.auth.models import User

from .models import AllowedHost, ScanRun


class AllowedHostInline(admin.TabularInline):
    model = AllowedHost
    extra = 1


class ClientUserAdmin(UserAdmin):
    inlines = [AllowedHostInline]


admin.site.unregister(User)
admin.site.register(User, ClientUserAdmin)


@admin.register(ScanRun)
class ScanRunAdmin(admin.ModelAdmin):
    list_display = ("target", "user", "status", "created_at", "finished_at")
    list_filter = ("status", "created_at")
    search_fields = ("target", "user__username")
    readonly_fields = ("created_at", "finished_at", "results", "host_security", "scan_info")
