// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                       // hydrogen // schema // color // opacity
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Opacity - alpha transparency value.
// |
// | Measured as a percentage from 0 to 100:
// | - **0%**: Fully transparent (invisible)
// | - **50%**: Half transparent
// | - **100%**: Fully opaque (solid)
// |
// | Used in RGBA, HSLA, and other color spaces with alpha channels.
// | Also known as alpha or transparency.
import * as Data_Int from "../Data.Int/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Hydrogen_Schema_Bounded from "../Hydrogen.Schema.Bounded/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);
var compare = /* #__PURE__ */ Data_Ord.compare(Data_Ord.ordInt);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // opacity
// ═══════════════════════════════════════════════════════════════════════════════
// | Opacity value as percentage (0-100)
// |
// | Represents alpha transparency. 0% is fully transparent, 100% is fully opaque.
// | This matches the pattern of other percentage-based atoms like Saturation and
// | Lightness for consistency across the Schema.
var Opacity = function (x) {
    return x;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // accessors
// ═══════════════════════════════════════════════════════════════════════════════
// | Extract the raw Int value (0-100)
var unwrap = function (v) {
    return v;
};

// | Create an opacity value without clamping
// |
// | Use only when you know the value is valid (0-100).
// | Invalid values will break invariants.
var unsafeOpacity = Opacity;

// | Convert to unit interval (0.0-1.0)
// |
// | Useful for exporting to graphics APIs (CSS, WebGL, Canvas):
// | ```purescript
// | toUnitInterval (opacity 0)    -- 0.0
// | toUnitInterval (opacity 50)   -- 0.5
// | toUnitInterval (opacity 100)  -- 1.0
// | ```
var toUnitInterval = function (v) {
    return Data_Int.toNumber(v) / 100.0;
};

// | Convert to Number for calculations
var toNumber = function (v) {
    return Data_Int.toNumber(v);
};

// | Convert to 8-bit channel value (0-255)
// |
// | Useful for serializing to RGBA8 formats:
// | ```purescript
// | toChannel (opacity 0)    -- 0
// | toChannel (opacity 50)   -- 128
// | toChannel (opacity 100)  -- 255
// | ```
var toChannel = function (v) {
    return Data_Int.round((Data_Int.toNumber(v) * 255.0) / 100.0);
};
var showOpacity = {
    show: function (v) {
        return show(v) + "%";
    }
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // constructors
// ═══════════════════════════════════════════════════════════════════════════════
// | Create an opacity value, clamping to 0-100
// |
// | Values outside the valid range are clamped:
// | ```purescript
// | opacity 50   -- Opacity 50%
// | opacity 150  -- Opacity 100% (clamped)
// | opacity (-20) -- Opacity 0% (clamped)
// | ```
var opacity = function (n) {
    return Hydrogen_Schema_Bounded.clampInt(0)(100)(n);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // operations
// ═══════════════════════════════════════════════════════════════════════════════
// | Scale opacity by a factor (0.0 to 2.0 typical)
// |
// | Useful for fading effects:
// | ```purescript
// | scale 0.5 (opacity 80)  -- Opacity 40%
// | scale 2.0 (opacity 30)  -- Opacity 60%
// | ```
var scale = function (factor) {
    return function (v) {
        return opacity(Data_Int.round(Data_Int.toNumber(v) * factor));
    };
};

// | Multiply two opacity values
// |
// | Models layering of transparent surfaces. Result is always more transparent
// | than either input (unless one is fully opaque):
// | ```purescript
// | multiply (opacity 50) (opacity 50)  -- Opacity 25%
// | multiply (opacity 80) (opacity 90)  -- Opacity 72%
// | ```
var multiply = function (v) {
    return function (v1) {
        return opacity(Data_Int.round((Data_Int.toNumber(v) * Data_Int.toNumber(v1)) / 100.0));
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // predicates
// ═══════════════════════════════════════════════════════════════════════════════
// | Check if fully transparent (opacity = 0%)
// |
// | Useful for optimization - fully transparent layers don't need rendering:
// | ```purescript
// | isTransparent (opacity 0)  -- true
// | isTransparent (opacity 1)  -- false
// | ```
var isTransparent = function (v) {
    return v === 0;
};

// | Check if semi-transparent (0% < opacity < 100%)
// |
// | Detects cases requiring alpha blending:
// | ```purescript
// | isSemiTransparent (opacity 50)   -- true
// | isSemiTransparent (opacity 0)    -- false
// | isSemiTransparent (opacity 100)  -- false
// | ```
var isSemiTransparent = function (v) {
    return v > 0 && v < 100;
};

// | Check if fully opaque (opacity = 100%)
// |
// | Useful for optimization - fully opaque layers can occlude layers behind:
// | ```purescript
// | isOpaque (opacity 100)  -- true
// | isOpaque (opacity 99)   -- false
// | ```
var isOpaque = function (v) {
    return v === 100;
};

// | Invert opacity (100 - value)
// |
// | Converts transparency to opacity and vice versa:
// | ```purescript
// | invert (opacity 30)   -- Opacity 70%
// | invert (opacity 100)  -- Opacity 0%
// | ```
var invert = function (v) {
    return 100 - v | 0;
};

// | Increase opacity by percentage points
// |
// | Makes something more opaque:
// | ```purescript
// | increase 20 (opacity 30)  -- Opacity 50%
// | increase 50 (opacity 80)  -- Opacity 100% (clamped)
// | ```
var increase = function (amount) {
    return function (v) {
        return opacity(v + amount | 0);
    };
};

// | Create opacity from unit interval (0.0-1.0)
// |
// | Useful for converting from graphics APIs that use normalized floats.
// | ```purescript
// | fromUnitInterval 0.0  -- Opacity 0%
// | fromUnitInterval 0.5  -- Opacity 50%
// | fromUnitInterval 1.0  -- Opacity 100%
// | ```
var fromUnitInterval = function (n) {
    return opacity(Data_Int.round(Hydrogen_Schema_Bounded.clampNumber(0.0)(1.0)(n) * 100.0));
};

// | Create opacity from 8-bit channel value (0-255)
// |
// | Useful for converting RGBA8 formats where alpha is stored as a byte.
// | ```purescript
// | fromChannel 0    -- Opacity 0%
// | fromChannel 128  -- Opacity 50%
// | fromChannel 255  -- Opacity 100%
// | ```
var fromChannel = function (c) {
    var clamped = Hydrogen_Schema_Bounded.clampInt(0)(255)(c);
    return opacity(Data_Int.round((Data_Int.toNumber(clamped) * 100.0) / 255.0));
};
var eqOpacity = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordOpacity = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqOpacity;
    }
};

// | Decrease opacity by percentage points
// |
// | Makes something more transparent:
// | ```purescript
// | decrease 20 (opacity 50)  -- Opacity 30%
// | decrease 50 (opacity 30)  -- Opacity 0% (clamped)
// | ```
var decrease = function (amount) {
    return function (v) {
        return opacity(v - amount | 0);
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // metadata
// ═══════════════════════════════════════════════════════════════════════════════
// | Bounds documentation for this type
var bounds = /* #__PURE__ */ Hydrogen_Schema_Bounded.intBounds(0)(100)("opacity")("Alpha transparency as percentage");

// | Blend two opacity values with weight (0.0 = all first, 1.0 = all second)
// |
// | Linear interpolation between two alpha values:
// | ```purescript
// | blend 0.0 (opacity 20) (opacity 80)  -- Opacity 20%
// | blend 0.5 (opacity 20) (opacity 80)  -- Opacity 50%
// | blend 1.0 (opacity 20) (opacity 80)  -- Opacity 80%
// | ```
var blend = function (weight) {
    return function (v) {
        return function (v1) {
            var w = Hydrogen_Schema_Bounded.clampNumber(0.0)(1.0)(weight);
            var result = Data_Int.toNumber(v) * (1.0 - w) + Data_Int.toNumber(v1) * w;
            return opacity(Data_Int.round(result));
        };
    };
};
export {
    opacity,
    unsafeOpacity,
    unwrap,
    scale,
    increase,
    decrease,
    invert,
    multiply,
    blend,
    isTransparent,
    isOpaque,
    isSemiTransparent,
    bounds,
    toNumber,
    toUnitInterval,
    fromUnitInterval,
    toChannel,
    fromChannel,
    eqOpacity,
    ordOpacity,
    showOpacity
};
