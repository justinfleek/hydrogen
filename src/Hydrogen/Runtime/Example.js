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
