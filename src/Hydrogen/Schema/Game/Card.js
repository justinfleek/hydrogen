// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                 // hydrogen // schema // game
//                                                                       // card
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// FFI implementations for Card.purs string operations and array fold.

// | String length.
export const stringLength = (s) => s.length;

// | Take first n characters.
export const stringTake = (n) => (s) => s.slice(0, n);

// | Drop first n characters.
export const stringDrop = (n) => (s) => s.slice(n);

// | Integer division (truncates toward zero).
export const intDiv = (a) => (b) => Math.trunc(a / b);

// | Left fold over an array.
export const foldlArray = (f) => (init) => (arr) => {
  let acc = init;
  for (let i = 0; i < arr.length; i++) {
    acc = f(acc)(arr[i]);
  }
  return acc;
};
