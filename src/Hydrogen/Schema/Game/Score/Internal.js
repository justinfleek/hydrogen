// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                              // hydrogen // schema // game // score // internal
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// Minimal FFI at serialization boundary.
// These are primitive operations that JavaScript provides natively.

export const unsafeIntToNumber = function(n) {
  return n;
};

export const unsafeNumberToInt = function(n) {
  return Math.trunc(n);
};

export const unsafeFoldBonuses = function(arr) {
  return function(acc) {
    let sum = acc;
    for (let i = 0; i < arr.length; i++) {
      sum = sum + arr[i].value;
    }
    return sum;
  };
};

export const unsafeAppendBonus = function(arr) {
  return function(bonus) {
    return arr.concat([bonus]);
  };
};
