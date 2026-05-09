export const translations = {
    en: {
        appTitle: "Inventory App With JS & TailwindCSS",
        addNewCategory: "Add New Category",
        addNewProduct: "Add New Product",
        title: "Title",
        description: "Description",
        quantity: "Quantity",
        location: "Location",
        category: "Category",
        cancel: "Cancel",
        addCategoryBtn: "Add Category",
        addProductBtn: "Add Product",
        productsList: "Products List",
        search: "Search...",
        selectLocation: "- select location -",
        selectCategory: "- select category -",
        sortNewest: "Newest",
        sortOldest: "Oldest",
        sortAZ: "A-Z",
        sortZA: "Z-A",
        cookieText: "We use localStorage to save your inventory on this device. No data is sent to any server.",
        cookieAccept: "Accept",
        cookieReject: "Reject",
        privacyLink: "Privacy Policy",
        langToggle: "中文",
        skipLink: "Skip to main content",
        categoriesList: "Categories",
        noCategories: "No categories yet — add one above.",
        privacyDocTitle: "Privacy Policy | Inventory App",
        privacyMetaDesc:
            "Privacy Policy for the Inventory App, describing how local browser storage is used.",
        privacyLastUpdated: "Last updated: 19 April 2026",
        privacyS1Title: "1. Overview",
        privacyS1Body:
            "This Inventory App is a client-side web application. We do not operate a backend server that stores your data, and we do not collect, share, or sell personal information to third parties.",
        privacyS2Title: "2. Data We Store",
        privacyS2PBefore:
            "All product and category information you create is stored exclusively in your browser via ",
        privacyS2PAfter: ". This data never leaves your device.",
        privacyS2Li1:
            "products — items you add (title, quantity, category, location, timestamp).",
        privacyS2Li2: "categories — categories you define (title, description).",
        privacyS2Li3: "cookieConsent — a single string recording your banner choice.",
        privacyS2Li4: "lang — your preferred language (en or zh).",
        privacyS3Title: "3. Third-Party Services",
        privacyS3BeforeCode:
            "The app loads Google Fonts (Outfit, Vazirmatn) from ",
        privacyS3AfterCode:
            ". Google may log the IP address used to fetch these fonts per its own privacy policy.",
        privacyS4Title: "4. Your Rights",
        privacyS4BeforeCode:
            "You can clear all stored data at any time by clearing your browser's site data for this origin, or by opening DevTools and running ",
        privacyS4AfterCode: ".",
        privacyS5Title: "5. Contact",
        privacyS5Body: "Questions? Open an issue on the project's GitHub repository.",
        privacyBackToApp: "← Back to App"
    },
    zh: {
        appTitle: "库存管理应用（JS + TailwindCSS）",
        addNewCategory: "添加新分类",
        addNewProduct: "添加新产品",
        title: "标题",
        description: "描述",
        quantity: "数量",
        location: "位置",
        category: "分类",
        cancel: "取消",
        addCategoryBtn: "添加分类",
        addProductBtn: "添加产品",
        productsList: "产品列表",
        search: "搜索...",
        selectLocation: "- 选择位置 -",
        selectCategory: "- 选择分类 -",
        sortNewest: "最新",
        sortOldest: "最旧",
        sortAZ: "A-Z",
        sortZA: "Z-A",
        cookieText: "我们使用浏览器 localStorage 在本设备保存您的库存数据，不会上传到任何服务器。",
        cookieAccept: "同意",
        cookieReject: "拒绝",
        privacyLink: "隐私政策",
        langToggle: "EN",
        skipLink: "跳转到主内容",
        categoriesList: "分类列表",
        noCategories: "暂无分类 — 请在上方添加。",
        privacyDocTitle: "隐私政策 | 库存管理应用",
        privacyMetaDesc: "库存管理应用的隐私政策，说明本应用如何使用浏览器本地存储。",
        privacyLastUpdated: "最后更新：2026年4月19日",
        privacyS1Title: "1. 概述",
        privacyS1Body:
            "本库存管理应用为纯前端网页应用。我们不运营用于存储您数据的后端服务器，也不会向第三方收集、共享或出售个人信息。",
        privacyS2Title: "2. 我们存储的数据",
        privacyS2PBefore: "您创建的所有产品与分类信息仅保存在浏览器的 ",
        privacyS2PAfter: " 中，这些数据不会离开您的设备。",
        privacyS2Li1:
            "products — 您添加的商品条目（标题、数量、分类、位置、时间戳）。",
        privacyS2Li2: "categories — 您自定义的分类（标题、描述）。",
        privacyS2Li3: "cookieConsent — 记录您对 Cookie 提示横幅所做选择的字符串。",
        privacyS2Li4: "lang — 您的首选界面语言（en 或 zh）。",
        privacyS3Title: "3. 第三方服务",
        privacyS3BeforeCode: "本应用会从 ",
        privacyS3AfterCode:
            " 加载 Google 字体（Outfit、Vazirmatn）。Google 可能会依据其自有隐私政策记录用于获取这些字体的 IP 地址。",
        privacyS4Title: "4. 您的权利",
        privacyS4BeforeCode:
            "您可以随时通过清除浏览器中本网站的站点数据来删除所有已存储内容，也可以打开开发者工具并执行 ",
        privacyS4AfterCode: "。",
        privacyS5Title: "5. 联系方式",
        privacyS5Body: "如有疑问，请在项目的 GitHub 仓库中提交 issue。",
        privacyBackToApp: "← 返回应用"
    }
};

const LANG_KEY = "lang";
const DEFAULT_LANG = "en";
const SUPPORTED = ["en", "zh"];

export function getLang() {
    const saved = typeof localStorage !== "undefined" ? localStorage.getItem(LANG_KEY) : null;
    return SUPPORTED.includes(saved) ? saved : DEFAULT_LANG;
}

export function setLang(lang) {
    if (!SUPPORTED.includes(lang)) return DEFAULT_LANG;
    if (typeof localStorage !== "undefined") localStorage.setItem(LANG_KEY, lang);
    return lang;
}

export function t(key, lang = getLang()) {
    const dict = translations[lang] || translations[DEFAULT_LANG];
    return dict[key] ?? key;
}

export function applyTranslations(lang = getLang()) {
    if (typeof document === "undefined") return;
    document.documentElement.setAttribute("lang", lang);
    document.querySelectorAll("[data-i18n]").forEach((el) => {
        const key = el.getAttribute("data-i18n");
        el.textContent = t(key, lang);
    });
    document.querySelectorAll("[data-i18n-placeholder]").forEach((el) => {
        const key = el.getAttribute("data-i18n-placeholder");
        el.setAttribute("placeholder", t(key, lang));
    });
    document.querySelectorAll("[data-i18n-aria]").forEach((el) => {
        const key = el.getAttribute("data-i18n-aria");
        el.setAttribute("aria-label", t(key, lang));
    });
}

export function toggleLang() {
    const next = getLang() === "en" ? "zh" : "en";
    setLang(next);
    applyTranslations(next);
    return next;
}
