// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                       // hydrogen // schema // color // kelvin
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Kelvin - color temperature of light sources.
// |
// | Measured in degrees Kelvin from 1000 to 40000:
// | - **1,800K**: Candlelight (warm orange)
// | - **2,700K**: Tungsten/incandescent bulbs (warm white)
// | - **3,000K**: Warm white LED
// | - **4,000K**: Neutral white
// | - **5,500K**: Daylight (reference white, "D55")
// | - **6,500K**: Cool white (standard daylight, "D65")
// | - **7,000K**: Overcast sky
// | - **10,000K+**: Blue sky, deep shade
// |
// | ## Physical Basis
// |
// | Color temperature describes the spectrum of light emitted by a blackbody
// | radiator at that temperature. Lower temperatures produce warmer (redder)
// | light, higher temperatures produce cooler (bluer) light.
// |
// | ## Use Cases
// |
// | - Light source definitions for glows, buttons, ambient lighting
// | - White balance for photo/video rendering in LATTICE
// | - Accurate color preview ("how will this look under tungsten vs daylight?")
// | - Color grading (film look = warmer temps, clinical = cooler temps)
import * as Data_Int from "../Data.Int/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Hydrogen_Math_Core from "../Hydrogen.Math.Core/index.js";
import * as Hydrogen_Schema_Bounded from "../Hydrogen.Schema.Bounded/index.js";
import * as Hydrogen_Schema_Color_RGB from "../Hydrogen.Schema.Color.RGB/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);
var compare = /* #__PURE__ */ Data_Ord.compare(Data_Ord.ordInt);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                      // kelvin
// ═══════════════════════════════════════════════════════════════════════════════
// | Color temperature in Kelvin (1000-40000)
// |
// | Represents the color of light emitted by a blackbody radiator at this
// | temperature. Used for lighting design, white balance, and color grading.
var Kelvin = function (x) {
    return x;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // accessors
// ═══════════════════════════════════════════════════════════════════════════════
// | Extract the raw Int value
var unwrap = function (v) {
    return v;
};

// | Create a kelvin value without clamping
// |
// | Use only when you know the value is valid (1000-40000).
var unsafeKelvin = Kelvin;

// | Convert to Number for calculations
var toNumber = function (v) {
    return Data_Int.toNumber(v);
};
var showKelvin = {
    show: function (v) {
        return show(v) + "K";
    }
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // conversion
// ═══════════════════════════════════════════════════════════════════════════════
// | Convert color temperature to approximate RGB value.
// |
// | This uses Tanner Helland's approximation algorithm, which is reasonably
// | accurate for typical lighting ranges (1000K - 40000K).
// |
// | Note: This is an approximation of blackbody radiation. For precise color
// | rendering, use CIE illuminants and chromatic adaptation transforms.
// |
// | ```purescript
// | kelvinToRgb (kelvin 2700)  -- Warm tungsten white
// | kelvinToRgb (kelvin 6500)  -- Cool daylight white
// | ```
var kelvinToRgb = function (v) {
    
    // Normalize to 0-100 scale (divide by 100)
var t = Data_Int.toNumber(v) / 100.0;
    
    // Calculate red
var r = (function () {
        var $40 = t <= 66.0;
        if ($40) {
            return 255.0;
        };
        return Hydrogen_Math_Core.clamp(0.0)(255.0)(329.698727446 * Hydrogen_Math_Core.pow(t - 60.0)(-0.1332047592));
    })();
    
    // Calculate green
var g = (function () {
        var $41 = t <= 66.0;
        if ($41) {
            return Hydrogen_Math_Core.clamp(0.0)(255.0)(99.4708025861 * Hydrogen_Math_Core.log(t) - 161.1195681661);
        };
        return Hydrogen_Math_Core.clamp(0.0)(255.0)(288.1221695283 * Hydrogen_Math_Core.pow(t - 60.0)(-7.55148492e-2));
    })();
    
    // Calculate blue
var b = (function () {
        var $42 = t >= 66.0;
        if ($42) {
            return 255.0;
        };
        var $43 = t <= 19.0;
        if ($43) {
            return 0.0;
        };
        return Hydrogen_Math_Core.clamp(0.0)(255.0)(138.5177312231 * Hydrogen_Math_Core.log(t - 10.0) - 305.0447927307);
    })();
    return Hydrogen_Schema_Color_RGB.rgb(Data_Int.round(r))(Data_Int.round(g))(Data_Int.round(b));
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // constructors
// ═══════════════════════════════════════════════════════════════════════════════
// | Create a kelvin value, clamping to 1000-40000
// |
// | Values below 1000K (infrared) or above 40000K (UV) are clamped to valid range.
var kelvin = function (n) {
    return Hydrogen_Schema_Bounded.clampInt(1000)(40000)(n);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // operations
// ═══════════════════════════════════════════════════════════════════════════════
// | Scale kelvin by a factor
// |
// | Useful for relative adjustments:
// | ```purescript
// | scale 1.2 (kelvin 5000)  -- Slightly cooler
// | scale 0.8 (kelvin 5000)  -- Slightly warmer
// | ```
var scale = function (factor) {
    return function (v) {
        return kelvin(Data_Int.round(Data_Int.toNumber(v) * factor));
    };
};

// | Shift kelvin by an amount
// |
// | ```purescript
// | shift 500 (kelvin 5000)   -- 5500K (cooler)
// | shift (-500) (kelvin 5000) -- 4500K (warmer)
// | ```
var shift = function (amount) {
    return function (v) {
        return kelvin(v + amount | 0);
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // predicates
// ═══════════════════════════════════════════════════════════════════════════════
// | Check if warm temperature (< 3500K)
// |
// | Warm temperatures: candlelight, tungsten, warm white LEDs
var isWarm = function (v) {
    return v < 3500;
};

// | Check if tungsten/incandescent range (2500K - 3000K)
var isTungsten = function (v) {
    return v >= 2500 && v <= 3000;
};

// | Check if neutral temperature (3500K - 5000K)
// |
// | Neutral temperatures: neutral white LEDs, early morning/late afternoon sun
var isNeutral = function (v) {
    return v >= 3500 && v <= 5000;
};

// | Check if daylight range (5000K - 6500K)
var isDaylight = function (v) {
    return v >= 5000 && v <= 6500;
};

// | Check if cool temperature (> 5000K)
// |
// | Cool temperatures: daylight, overcast sky, blue sky
var isCool = function (v) {
    return v > 5000;
};

// | Check if candlelight range (< 2000K)
var isCandlelight = function (v) {
    return v < 2000;
};
var eqKelvin = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordKelvin = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqKelvin;
    }
};

// | Bounds documentation for this type
var bounds = /* #__PURE__ */ Hydrogen_Schema_Bounded.intBounds(1000)(40000)("kelvin")("Color temperature in degrees Kelvin");
export {
    kelvin,
    unsafeKelvin,
    unwrap,
    scale,
    shift,
    bounds,
    toNumber,
    isWarm,
    isNeutral,
    isCool,
    isCandlelight,
    isTungsten,
    isDaylight,
    kelvinToRgb,
    eqKelvin,
    ordKelvin,
    showKelvin
};
