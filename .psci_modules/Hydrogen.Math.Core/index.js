// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                        // hydrogen // math
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Core mathematical functions.
// |
// | This module provides pure mathematical operations via FFI to JavaScript's
// | Math object. These are the foundational operations that Color, Dimension,
// | and other Schema pillars depend on.
// |
// | ## Verification Notes
// |
// | The following operations may benefit from Lean4 formal verification:
// | - Color space conversions (affects accessibility compliance)
// | - Unit conversions (affects physical accuracy)
// | - Interpolation functions (affects animation correctness)
// |
// | The following are unlikely to need verification:
// | - CSS output formatting
// | - Blend modes (creative, not safety-critical)
import * as $foreign from "./foreign.js";

// | Convert radians to degrees
var radiansToDegrees = function (rad) {
    return (rad * 180.0) / $foreign.pi;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                           // angle conversion
// ═══════════════════════════════════════════════════════════════════════════════
// | Convert degrees to radians
var degreesToRadians = function (deg) {
    return (deg * $foreign.pi) / 180.0;
};
export {
    pi,
    e,
    tau,
    sqrt2,
    sqrt1_2,
    ln2,
    ln10,
    log2e,
    log10e,
    pow,
    sqrt,
    cbrt,
    hypot,
    hypot3,
    sin,
    cos,
    tan,
    asin,
    acos,
    atan,
    atan2,
    sinh,
    cosh,
    tanh,
    asinh,
    acosh,
    atanh,
    exp,
    expm1,
    log,
    log10,
    log2,
    log1p,
    floor,
    ceil,
    round,
    trunc,
    fround,
    abs,
    sign,
    min,
    max,
    minArray,
    maxArray,
    clamp,
    isNaN,
    isFinite,
    isInteger,
    infinity,
    negativeInfinity,
    lerp,
    inverseLerp,
    remap,
    smoothstep,
    smootherstep
} from "./foreign.js";
export {
    degreesToRadians,
    radiansToDegrees
};
