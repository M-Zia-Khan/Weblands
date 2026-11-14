from django import forms
from django.contrib.auth.forms import AuthenticationForm, UserCreationForm
from django.contrib.auth.models import User


class ClientAuthenticationForm(AuthenticationForm):
    username = forms.CharField(
        label="Email address or username",
        widget=forms.TextInput(attrs={"autocomplete": "username"}),
    )

    def clean_username(self):
        username = self.cleaned_data["username"]
        return username.lower() if "@" in username else username


class ClientSignUpForm(UserCreationForm):
    username = forms.EmailField(
        label="Email address",
        max_length=150,
        widget=forms.EmailInput(attrs={"autocomplete": "email"}),
    )

    class Meta(UserCreationForm.Meta):
        model = User
        fields = ("username",)

    def clean_username(self):
        email = super().clean_username().strip().lower()
        if User.objects.filter(email__iexact=email).exists():
            raise forms.ValidationError("An account with this email address already exists.")
        return email

    def save(self, commit=True):
        user = super().save(commit=False)
        user.email = self.cleaned_data["username"]
        if commit:
            user.save()
        return user


class ScanForm(forms.Form):
    scan_type = forms.ChoiceField(
        choices=(("website", "Check a website"), ("csv", "Upload a CSV")),
        widget=forms.RadioSelect,
        initial="website",
    )
    website_url = forms.CharField(
        label="Website URL",
        max_length=2048,
        required=False,
        widget=forms.URLInput(attrs={"placeholder": "https://example.com"}),
    )
    csv_file = forms.FileField(
        label="CSV file",
        required=False,
        widget=forms.FileInput(attrs={"accept": ".csv,text/csv"}),
    )

    def clean(self):
        cleaned = super().clean()
        if cleaned.get("scan_type") == "website" and not cleaned.get("website_url", "").strip():
            self.add_error("website_url", "Enter a website URL.")
        if cleaned.get("scan_type") == "csv" and not cleaned.get("csv_file"):
            self.add_error("csv_file", "Choose a CSV file.")
        return cleaned

    def clean_csv_file(self):
        uploaded = self.cleaned_data.get("csv_file")
        if uploaded:
            if uploaded.size > 1_000_000:
                raise forms.ValidationError("The CSV must be 1 MB or smaller.")
            if not uploaded.name.lower().endswith(".csv"):
                raise forms.ValidationError("Upload a .csv file.")
        return uploaded
