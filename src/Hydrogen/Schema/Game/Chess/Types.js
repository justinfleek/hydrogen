// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                   // hydrogen // schema // game // chess // types
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// | FFI for Chess.Types module.
// |
// | Minimal string manipulation at the boundary. All logic lives in PureScript.

export const splitStringImpl = (delim) => (str) => {
  if (delim === "") {
    return str.split("");
  }
  return str.split(delim);
};
