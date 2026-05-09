"use strict";

var _i18n = require("./i18n.js");
document.addEventListener("DOMContentLoaded", function () {
  var lang = (0, _i18n.getLang)();
  var meta = document.querySelector('meta[name="description"]');
  if (meta) meta.setAttribute("content", (0, _i18n.t)("privacyMetaDesc", lang));
  var titleEl = document.querySelector("title");
  if (titleEl) titleEl.textContent = (0, _i18n.t)("privacyDocTitle", lang);
  (0, _i18n.applyTranslations)(lang);
});