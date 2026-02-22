// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                     // hydrogen // schema // color // lightness
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Lightness - how light or dark a color is.
// |
// | Measured as a percentage from 0 to 100:
// | - **0%**: Black (no light)
// | - **50%**: Pure color (maximum saturation possible)
// | - **100%**: White (full light)
// |
// | In HSL, lightness determines the amount of white or black mixed in.
// | At 50% lightness, you get the most vivid version of the hue.
import * as Data_Int from "../Data.Int/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Hydrogen_Schema_Bounded from "../Hydrogen.Schema.Bounded/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);
var compare = /* #__PURE__ */ Data_Ord.compare(Data_Ord.ordInt);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // lightness
// ═══════════════════════════════════════════════════════════════════════════════
// | Lightness value as percentage (0-100)
// |
// | Represents how light or dark a color is. 0% is black, 100% is white.
// | 50% gives the most saturated version of the hue.
var Lightness = function (x) {
    return x;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // accessors
// ═══════════════════════════════════════════════════════════════════════════════
// | Extract the raw Int value
var unwrap = function (v) {
    return v;
};

// | Create a lightness without clamping
// |
// | Use only when you know the value is valid.
var unsafeLightness = Lightness;

// | Convert to unit interval (0.0-1.0)
var toUnitInterval = function (v) {
    return Data_Int.toNumber(v) / 100.0;
};

// | Convert to Number for calculations
var toNumber = function (v) {
    return Data_Int.toNumber(v);
};
var showLightness = {
    show: function (v) {
        return show(v) + "%";
    }
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // constructors
// ═══════════════════════════════════════════════════════════════════════════════
// | Create a lightness, clamping to 0-100
var lightness = function (n) {
    return Hydrogen_Schema_Bounded.clampInt(0)(100)(n);
};

// | Scale lightness by a factor
var scale = function (factor) {
    return function (v) {
        return lightness(Data_Int.round(Data_Int.toNumber(v) * factor));
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // operations
// ═══════════════════════════════════════════════════════════════════════════════
// | Increase lightness (add white)
var lighten = function (amount) {
    return function (v) {
        return lightness(v + amount | 0);
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // predicates
// ═══════════════════════════════════════════════════════════════════════════════
// | Check if lightness is in the light range (> 60%)
// |
// | Useful for determining if dark text should be used on this background.
var isLight = function (v) {
    return v > 60;
};

// | Check if lightness is in the dark range (< 40%)
// |
// | Useful for determining if light text should be used on this background.
var isDark = function (v) {
    return v < 40;
};
var eqLightness = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordLightness = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqLightness;
    }
};

// | Decrease lightness (add black)
var darken = function (amount) {
    return function (v) {
        return lightness(v - amount | 0);
    };
};

// | Bounds documentation for this type
var bounds = /* #__PURE__ */ Hydrogen_Schema_Bounded.intBounds(0)(100)("lightness")("Light/dark level as percentage");
export {
    lightness,
    unsafeLightness,
    unwrap,
    lighten,
    darken,
    scale,
    isLight,
    isDark,
    bounds,
    toNumber,
    toUnitInterval,
    eqLightness,
    ordLightness,
    showLightness
};
