// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                          // playground // scene // primitive
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//
// FFI for Primitive module.
// Only safe, total functions are exported.

// | Convert Int to Number.
// |
// | This is a safe coercion in JavaScript since both are represented
// | as IEEE 754 doubles. PureScript Ints are bounded [-2^31, 2^31-1]
// | which fit exactly in Number.
export const intToNumber = function(n) {
  return n;
};
