from django.contrib import admin
from django.urls import include, path
from django.contrib.auth import views as auth_views

from clients.forms import ClientAuthenticationForm


urlpatterns = [
    path("admin/", admin.site.urls),
    path(
        "login/",
        auth_views.LoginView.as_view(
            template_name="clients/login.html",
            redirect_authenticated_user=True,
            authentication_form=ClientAuthenticationForm,
        ),
        name="login",
    ),
    path("logout/", auth_views.LogoutView.as_view(), name="logout"),
    path("", include("clients.urls")),
]
