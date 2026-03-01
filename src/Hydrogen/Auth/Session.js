// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                   // hydrogen // auth // ffi
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// ═══════════════════════════════════════════════════════════════════════════════
// BROWSER BOUNDARY: Storage APIs (localStorage, sessionStorage, window)
// These MUST remain as FFI - they access browser-only global state
// ═══════════════════════════════════════════════════════════════════════════════

// | BROWSER BOUNDARY: Read from localStorage/sessionStorage/memory
// | Returns PureScript Maybe (Just value | Nothing)
export const getStorageItem = (storageType) => (key) => () => {
  try {
    let value = null;
    if (storageType === "memory") {
      value = window.__hydrogenMemoryStorage?.[key] ?? null;
    } else {
      const storage = storageType === "localStorage" ? localStorage : sessionStorage;
      value = storage.getItem(key);
    }
    // Return PureScript Maybe encoding
    return value === null ? { tag: "Nothing" } : { tag: "Just", value0: value };
  } catch (e) {
    // Storage may be unavailable (private browsing, etc.)
    return { tag: "Nothing" };
  }
};

// | BROWSER BOUNDARY: Write to localStorage/sessionStorage/memory
export const setStorageItem = (storageType) => (key) => (value) => () => {
  try {
    if (storageType === "memory") {
      window.__hydrogenMemoryStorage = window.__hydrogenMemoryStorage || {};
      window.__hydrogenMemoryStorage[key] = value;
      return;
    }
    const storage = storageType === "localStorage" ? localStorage : sessionStorage;
    storage.setItem(key, value);
  } catch (e) {
    // Storage may be unavailable or quota exceeded
  }
};

// | BROWSER BOUNDARY: Remove from localStorage/sessionStorage/memory
export const removeStorageItem = (storageType) => (key) => () => {
  try {
    if (storageType === "memory") {
      if (window.__hydrogenMemoryStorage) {
        delete window.__hydrogenMemoryStorage[key];
      }
      return;
    }
    const storage = storageType === "localStorage" ? localStorage : sessionStorage;
    storage.removeItem(key);
  } catch (e) {
    // Storage may be unavailable
  }
};
