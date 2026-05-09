import {
    validateTitle,
    filterByTitle,
    sortProducts,
    createProduct,
    findCategoryByTitle,
    escapeHtml,
    uniqueId,
    formatDate,
    clampQuantity
} from "../src/js/utils.js";

describe("validateTitle", () => {
    test("returns true for strings with >= min chars after trim", () => {
        expect(validateTitle("ab")).toBe(true);
        expect(validateTitle("  hello  ")).toBe(true);
    });

    test("returns false for short or empty strings", () => {
        expect(validateTitle("a")).toBe(false);
        expect(validateTitle(" ")).toBe(false);
        expect(validateTitle("")).toBe(false);
    });

    test("returns false for non-string input", () => {
        expect(validateTitle(null)).toBe(false);
        expect(validateTitle(undefined)).toBe(false);
        expect(validateTitle(42)).toBe(false);
    });

    test("respects custom minimum length", () => {
        expect(validateTitle("abc", 5)).toBe(false);
        expect(validateTitle("abcdef", 5)).toBe(true);
    });
});

describe("filterByTitle", () => {
    const products = [
        { id: 1, title: "Apple" },
        { id: 2, title: "Banana" },
        { id: 3, title: "  apple pie " },
        { id: 4, title: "Cherry" }
    ];

    test("returns products matching search term (case-insensitive)", () => {
        const result = filterByTitle(products, "apple");
        expect(result).toHaveLength(2);
    });

    test("returns all products when term is empty", () => {
        expect(filterByTitle(products, "")).toHaveLength(4);
        expect(filterByTitle(products, "   ")).toHaveLength(4);
    });

    test("returns empty array for non-array input", () => {
        expect(filterByTitle(null, "x")).toEqual([]);
        expect(filterByTitle(undefined, "x")).toEqual([]);
    });

    test("skips items without a string title", () => {
        const dirty = [...products, { id: 5, title: null }, { id: 6 }];
        const result = filterByTitle(dirty, "apple");
        expect(result.every((p) => typeof p.title === "string")).toBe(true);
    });
});

describe("sortProducts", () => {
    const products = [
        { id: 3, title: "Banana" },
        { id: 1, title: "apple" },
        { id: 2, title: "Cherry" }
    ];

    test("sorts newest by descending id", () => {
        expect(sortProducts(products, "newest").map((p) => p.id)).toEqual([3, 2, 1]);
    });

    test("sorts oldest by ascending id", () => {
        expect(sortProducts(products, "oldest").map((p) => p.id)).toEqual([1, 2, 3]);
    });

    test("sorts A-Z case-insensitively", () => {
        expect(sortProducts(products, "A-Z").map((p) => p.title)).toEqual(["apple", "Banana", "Cherry"]);
    });

    test("sorts Z-A case-insensitively", () => {
        expect(sortProducts(products, "Z-A").map((p) => p.title)).toEqual(["Cherry", "Banana", "apple"]);
    });

    test("returns shallow copy for unknown sort type", () => {
        const out = sortProducts(products, "nope");
        expect(out).toEqual(products);
        expect(out).not.toBe(products);
    });

    test("returns empty array for non-array input", () => {
        expect(sortProducts(null, "newest")).toEqual([]);
    });
});

describe("createProduct", () => {
    test("creates product with trimmed title and defaults", () => {
        const p = createProduct({ title: "  Milk  " }, () => 42);
        expect(p).toEqual({
            id: 42,
            title: "Milk",
            quantity: 0,
            location: "none",
            category: "none"
        });
    });

    test("preserves numeric quantity", () => {
        const p = createProduct({ title: "a", quantity: 7 }, () => 1);
        expect(p.quantity).toBe(7);
    });

    test("coerces non-numeric quantity to 0", () => {
        expect(createProduct({ title: "a", quantity: "abc" }, () => 1).quantity).toBe(0);
    });

    test("uses provided location and category", () => {
        const p = createProduct({ title: "x", location: "BDG", category: "shoe" }, () => 1);
        expect(p.location).toBe("BDG");
        expect(p.category).toBe("shoe");
    });
});

describe("escapeHtml", () => {
    test("neutralises script-injection payloads", () => {
        const evil = `<img src=x onerror="alert(1)">`;
        const safe = escapeHtml(evil);
        expect(safe).not.toContain("<img");
        expect(safe).toContain("&lt;img");
        expect(safe).toContain("&quot;");
    });

    test("escapes ampersands first to avoid double-encoding", () => {
        expect(escapeHtml("Tom & Jerry")).toBe("Tom &amp; Jerry");
        expect(escapeHtml("a&lt;b")).toBe("a&amp;lt;b");
    });

    test("escapes single and double quotes", () => {
        expect(escapeHtml(`"hi"`)).toBe("&quot;hi&quot;");
        expect(escapeHtml(`it's`)).toBe("it&#39;s");
    });

    test("returns empty string for null / undefined", () => {
        expect(escapeHtml(null)).toBe("");
        expect(escapeHtml(undefined)).toBe("");
    });

    test("coerces non-strings", () => {
        expect(escapeHtml(42)).toBe("42");
        expect(escapeHtml(true)).toBe("true");
    });
});

describe("uniqueId", () => {
    test("returns a unique id even when called within the same millisecond", () => {
        const ids = new Set();
        for (let i = 0; i < 200; i++) ids.add(uniqueId());
        expect(ids.size).toBeGreaterThanOrEqual(200);
    });

    test("contains a millisecond timestamp prefix", () => {
        const id = uniqueId();
        expect(id).toMatch(/^\d+-[0-9a-f]{4}$/);
    });
});

describe("formatDate", () => {
    const fixed = new Date("2025-04-19T10:30:00Z");

    test("English locale uses MM/DD/YYYY-style numerics", () => {
        const out = formatDate(fixed, "en");
        expect(out).toMatch(/2025/);
        expect(out).toMatch(/04/);
    });

    test("Chinese locale produces a Chinese calendar string", () => {
        const out = formatDate(fixed, "zh");
        expect(out).toMatch(/2025/);
    });

    test("never produces Persian/Farsi numerals for either locale", () => {
        const en = formatDate(fixed, "en");
        const zh = formatDate(fixed, "zh");
        // Persian-Indic digits range U+06F0..U+06F9 — must be absent
        const persian = /[۰-۹]/;
        expect(persian.test(en)).toBe(false);
        expect(persian.test(zh)).toBe(false);
    });

    test("accepts ISO strings as well as Date objects", () => {
        expect(formatDate("2025-04-19T10:30:00Z", "en")).toMatch(/2025/);
    });

    test("returns empty string for invalid input", () => {
        expect(formatDate("not-a-date", "en")).toBe("");
    });
});

describe("clampQuantity", () => {
    test("never returns a negative number", () => {
        expect(clampQuantity(-5)).toBe(0);
        expect(clampQuantity("-99")).toBe(0);
    });

    test("returns 0 for non-numeric input", () => {
        expect(clampQuantity("abc")).toBe(0);
        expect(clampQuantity(NaN)).toBe(0);
        expect(clampQuantity(undefined)).toBe(0);
    });

    test("floors decimals", () => {
        expect(clampQuantity(3.9)).toBe(3);
    });

    test("preserves valid positive integers (string or number)", () => {
        expect(clampQuantity(7)).toBe(7);
        expect(clampQuantity("12")).toBe(12);
    });

    test("respects custom minimum", () => {
        expect(clampQuantity(0, 1)).toBe(1);
        expect(clampQuantity(5, 1)).toBe(5);
    });
});

describe("findCategoryByTitle", () => {
    const categories = [
        { title: "Food", description: "edible" },
        { title: "Tools", description: "hardware" }
    ];

    test("finds matching category", () => {
        expect(findCategoryByTitle(categories, "Food")).toEqual({ title: "Food", description: "edible" });
    });

    test("returns undefined when not found", () => {
        expect(findCategoryByTitle(categories, "Nope")).toBeUndefined();
    });

    test("handles invalid input", () => {
        expect(findCategoryByTitle(null, "x")).toBeUndefined();
    });
});
