import { applyTranslations, getLang, t } from "./i18n.js";

document.addEventListener("DOMContentLoaded", () => {
    const lang = getLang();
    const meta = document.querySelector('meta[name="description"]');
    if (meta) meta.setAttribute("content", t("privacyMetaDesc", lang));
    const titleEl = document.querySelector("title");
    if (titleEl) titleEl.textContent = t("privacyDocTitle", lang);
    applyTranslations(lang);
});
