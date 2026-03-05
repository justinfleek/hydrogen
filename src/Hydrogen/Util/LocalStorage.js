// FFI for Hydrogen.Util.LocalStorage
// Direct browser localStorage operations

export const getItemRaw = key => () => {
  try {
    const value = localStorage.getItem(key);
    if (value === null) {
      return null; // PureScript Maybe handles null as Nothing via purescript-nullable
    }
    return value;
  } catch (e) {
    // localStorage might throw in private browsing or if blocked
    return null;
  }
};

export const setItemRaw = key => value => () => {
  try {
    localStorage.setItem(key, value);
  } catch (e) {
    // Silently fail - quota exceeded or storage blocked
    console.warn("localStorage.setItem failed:", e);
  }
};

export const removeItemRaw = key => () => {
  try {
    localStorage.removeItem(key);
  } catch (e) {
    // Silently fail
    console.warn("localStorage.removeItem failed:", e);
  }
};
