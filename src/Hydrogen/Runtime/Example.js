// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                 // hydrogen // runtime // example
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// FFI for Example module

// Convert a Foreign value to a string representation
// Handles objects, arrays, primitives, null/undefined
export const foreignToString = (value) => {
  if (value === null) {
    return "null";
  }
  if (value === undefined) {
    return "undefined";
  }
  if (typeof value === "string") {
    return value;
  }
  if (typeof value === "object") {
    try {
      // Pretty print with 2-space indentation
      return JSON.stringify(value, null, 2);
    } catch (e) {
      return "[Object]";
    }
  }
  return String(value);
};

// Floor a number to an integer
// Used for display purposes in animation demos
export const floorToInt = (n) => Math.floor(n) | 0;

// Safe array index access
// Takes Just and Nothing constructors from PureScript
export const arrayIndexImpl = (just) => (nothing) => (idx) => (arr) => {
  if (idx >= 0 && idx < arr.length) {
    return just(arr[idx]);
  }
  return nothing;
};

// Parse a number from a string with fallback default
export const parseNumberImpl = (str) => (defaultVal) => {
  const parsed = parseFloat(str);
  if (isNaN(parsed)) {
    return defaultVal;
  }
  return parsed;
};
