// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                    // hydrogen // schema // color // saturation
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Saturation - color intensity/purity.
// |
// | Measured as a percentage from 0 to 100:
// | - **0%**: Grayscale (no color)
// | - **50%**: Muted, desaturated
// | - **100%**: Fully saturated, vivid
// |
// | In HSL color space, saturation describes how much gray is mixed in.
// | At 0% saturation, the hue is irrelevant - you get pure gray.
import * as Data_Int from "../Data.Int/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Hydrogen_Schema_Bounded from "../Hydrogen.Schema.Bounded/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);
var compare = /* #__PURE__ */ Data_Ord.compare(Data_Ord.ordInt);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // saturation
// ═══════════════════════════════════════════════════════════════════════════════
// | Saturation value as percentage (0-100)
// |
// | Represents color purity/intensity. 0% is grayscale, 100% is fully vivid.
var Saturation = function (x) {
    return x;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // accessors
// ═══════════════════════════════════════════════════════════════════════════════
// | Extract the raw Int value
var unwrap = function (v) {
    return v;
};

// | Create a saturation without clamping
// |
// | Use only when you know the value is valid.
var unsafeSaturation = Saturation;

// | Convert to unit interval (0.0-1.0)
var toUnitInterval = function (v) {
    return Data_Int.toNumber(v) / 100.0;
};

// | Convert to Number for calculations
var toNumber = function (v) {
    return Data_Int.toNumber(v);
};
var showSaturation = {
    show: function (v) {
        return show(v) + "%";
    }
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // constructors
// ═══════════════════════════════════════════════════════════════════════════════
// | Create a saturation, clamping to 0-100
var saturation = function (n) {
    return Hydrogen_Schema_Bounded.clampInt(0)(100)(n);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // operations
// ═══════════════════════════════════════════════════════════════════════════════
// | Scale saturation by a factor (0.0 to 2.0 typical)
var scale = function (factor) {
    return function (v) {
        return saturation(Data_Int.round(Data_Int.toNumber(v) * factor));
    };
};

// | Check if saturation is vivid (> 80%)
var isVivid = function (v) {
    return v > 80;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // predicates
// ═══════════════════════════════════════════════════════════════════════════════
// | Check if saturation is effectively grayscale (< 5%)
var isGrayscale = function (v) {
    return v < 5;
};

// | Increase saturation by percentage points
var increase = function (amount) {
    return function (v) {
        return saturation(v + amount | 0);
    };
};
var eqSaturation = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordSaturation = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqSaturation;
    }
};

// | Decrease saturation by percentage points
var decrease = function (amount) {
    return function (v) {
        return saturation(v - amount | 0);
    };
};

// | Bounds documentation for this type
var bounds = /* #__PURE__ */ Hydrogen_Schema_Bounded.intBounds(0)(100)("saturation")("Color intensity as percentage");
export {
    saturation,
    unsafeSaturation,
    unwrap,
    scale,
    increase,
    decrease,
    isGrayscale,
    isVivid,
    bounds,
    toNumber,
    toUnitInterval,
    eqSaturation,
    ordSaturation,
    showSaturation
};
