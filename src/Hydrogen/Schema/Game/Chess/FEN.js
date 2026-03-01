// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                     // hydrogen // schema // game // chess // fen
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// | FFI for Chess.FEN module.
// |
// | Minimal string manipulation at the boundary. All logic lives in PureScript.

export const splitStringImpl = (delim) => (str) => {
  if (delim === "") {
    return str.split("");
  }
  return str.split(delim);
};

export const parseIntImpl = (str) => {
  const n = parseInt(str, 10);
  if (isNaN(n)) {
    return null;
  }
  return n;
};

export const dropFirstImpl = (arr) => arr.slice(1);

export const containsCharImpl = (char) => (str) => str.includes(char);
