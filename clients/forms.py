from django import forms


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
