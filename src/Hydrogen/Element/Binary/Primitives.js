// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                          // hydrogen // element // binary // primitives
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//
// FFI for string/byte array conversion.
// Used for serializing/deserializing string fields in Element binary format.

"use strict";

// | Convert String to array of ASCII code points (0-127)
// | Characters outside ASCII range are replaced with '?' (63)
export const toCodePointArray = function(str) {
  const result = [];
  for (let i = 0; i < str.length; i++) {
    const code = str.charCodeAt(i);
    result.push(code <= 127 ? code : 63); // '?' for non-ASCII
  }
  return result;
};

// | Convert array of ASCII code points to String
export const bytesToString = function(bytes) {
  return String.fromCharCode.apply(null, bytes);
};
