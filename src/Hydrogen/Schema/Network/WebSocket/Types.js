// FFI for WebSocket Types module
"use strict";

export const stringLength = function(s) {
  return s.length;
};

export const mapArray = function(f) {
  return function(arr) {
    return arr.map(f);
  };
};
