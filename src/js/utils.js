export function validateTitle(title, min = 2) {
    if (typeof title !== "string") return false;
    return title.trim().length >= min;
}

/**
 * Escape user-controlled strings before they are concatenated into an
 * innerHTML template. Prevents stored-XSS via product / category titles.
 * Reference: OWASP XSS Prevention Cheat Sheet, Rule #1.
 */
export function escapeHtml(value) {
    if (value === null || value === undefined) return "";
    return String(value)
        .replace(/&/g, "&amp;")
        .replace(/</g, "&lt;")
        .replace(/>/g, "&gt;")
        .replace(/"/g, "&quot;")
        .replace(/'/g, "&#39;");
}

/**
 * Collision-resistant id: timestamp + 4 random hex chars.
 * Avoids duplicate ids when two clicks land in the same millisecond.
 */
let lastTimestamp = 0;
let sequence = 0;

export function uniqueId() {
  const now = Date.now();
  if (now !== lastTimestamp) {
    lastTimestamp = now;
    sequence = 0;
  }
  const seq = sequence.toString(16).padStart(4, "0");
  sequence++;
  return `${now}-${seq}`;
}

/**
 * Format a date for display using the active UI locale.
 * Falls back to en-US for unknown languages. Accepts a Date, an ISO
 * string, or any value `new Date(x)` can parse.
 */
export function formatDate(value, lang = "en") {
    const date = value instanceof Date ? value : new Date(value);
    if (Number.isNaN(date.getTime())) return "";
    const locale = lang === "zh" ? "zh-CN" : "en-US";
    return new Intl.DateTimeFormat(locale, {
        year: "numeric", month: "2-digit", day: "2-digit"
    }).format(date);
}

/**
 * Clamp a quantity to a non-negative integer. Stock counts cannot be
 * negative — this is the single source of truth for that invariant so
 * both the +/- buttons and the storage layer stay consistent.
 */
export function clampQuantity(value, min = 0) {
    const n = Number(value);
    if (!Number.isFinite(n)) return min;
    return Math.max(min, Math.floor(n));
}

export function filterByTitle(products, term) {
    if (!Array.isArray(products)) return [];
    const normalized = String(term || "").toLowerCase().trim();
    if (!normalized) return products.slice();
    return products.filter((p) =>
        typeof p?.title === "string" &&
        p.title.toLowerCase().trim().includes(normalized)
    );
}

export function sortProducts(products, sortType) {
    if (!Array.isArray(products)) return [];
    const arr = products.slice();
    switch (sortType) {
        case "newest":
            return arr.sort((a, b) => b.id - a.id);
        case "oldest":
            return arr.sort((a, b) => a.id - b.id);
        case "A-Z":
            return arr.sort((a, b) =>
                a.title.toLowerCase().localeCompare(b.title.toLowerCase())
            );
        case "Z-A":
            return arr.sort((a, b) =>
                a.title.toLowerCase().localeCompare(b.title.toLowerCase())
            ).reverse();
        default:
            return arr;
    }
}

export function createProduct({ title, quantity, location, category }, idProvider = () => Date.now()) {
    return {
        id: idProvider(),
        title: String(title).trim(),
        quantity: Number(quantity) || 0,
        location: location || "none",
        category: category || "none"
    };
}

export function findCategoryByTitle(categories, title) {
    if (!Array.isArray(categories)) return undefined;
    return categories.find((c) => c?.title === title);
}
