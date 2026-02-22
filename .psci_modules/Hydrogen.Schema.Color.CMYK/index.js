// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                        // hydrogen // schema // color // cmyk
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | CMYK color molecule - composition of Cyan, Magenta, Yellow, Key atoms.
// |
// | CMYK is the subtractive color model used in color printing:
// | - **Cyan**: Absorbs red light (0-100%)
// | - **Magenta**: Absorbs green light (0-100%)
// | - **Yellow**: Absorbs blue light (0-100%)
// | - **Key (Black)**: True black ink (0-100%)
// |
// | ## Subtractive Color Mixing
// |
// | Unlike RGB (additive - light-based), CMYK is subtractive (ink/pigment-based):
// | ```
// | Cyan + Magenta        = Blue
// | Magenta + Yellow      = Red
// | Yellow + Cyan         = Green
// | Cyan + Magenta + Yellow = Dark Brown (not true black - that's why K exists)
// | ```
// |
// | ## Print Applications
// |
// | CMYK is essential for:
// | - Print-on-demand products (t-shirts, mugs, posters)
// | - Professional printing (brochures, business cards)
// | - Color accuracy preview ("will this RGB color print correctly?")
// | - Gamut warnings ("this bright green can't be printed in CMYK")
import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Int from "../Data.Int/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Ordering from "../Data.Ordering/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Hydrogen_Math_Core from "../Hydrogen.Math.Core/index.js";
import * as Hydrogen_Schema_Color_Channel from "../Hydrogen.Schema.Color.Channel/index.js";
import * as Hydrogen_Schema_Color_Cyan from "../Hydrogen.Schema.Color.Cyan/index.js";
import * as Hydrogen_Schema_Color_Key from "../Hydrogen.Schema.Color.Key/index.js";
import * as Hydrogen_Schema_Color_Magenta from "../Hydrogen.Schema.Color.Magenta/index.js";
import * as Hydrogen_Schema_Color_RGB from "../Hydrogen.Schema.Color.RGB/index.js";
import * as Hydrogen_Schema_Color_Yellow from "../Hydrogen.Schema.Color.Yellow/index.js";
var eq = /* #__PURE__ */ Data_Eq.eq(Hydrogen_Schema_Color_Cyan.eqCyan);
var eq1 = /* #__PURE__ */ Data_Eq.eq(Hydrogen_Schema_Color_Key.eqKey);
var eq2 = /* #__PURE__ */ Data_Eq.eq(Hydrogen_Schema_Color_Magenta.eqMagenta);
var eq3 = /* #__PURE__ */ Data_Eq.eq(Hydrogen_Schema_Color_Yellow.eqYellow);
var compare = /* #__PURE__ */ Data_Ord.compare(Hydrogen_Schema_Color_Cyan.ordCyan);
var compare1 = /* #__PURE__ */ Data_Ord.compare(Hydrogen_Schema_Color_Key.ordKey);
var compare2 = /* #__PURE__ */ Data_Ord.compare(Hydrogen_Schema_Color_Magenta.ordMagenta);
var compare3 = /* #__PURE__ */ Data_Ord.compare(Hydrogen_Schema_Color_Yellow.ordYellow);
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                        // cmyk
// ═══════════════════════════════════════════════════════════════════════════════
// | CMYK color value — a molecule composed of four ink percentage atoms.
// |
// | This is a lawful composition: if Cyan, Magenta, Yellow, and Key are each
// | correct (0-100, clamped), then CMYK is correct by construction.
var CMYK = function (x) {
    return x;
};

// | Extract the yellow component.
var yellow = function (v) {
    return v.yellow;
};

// | Extract the magenta component.
var magenta = function (v) {
    return v.magenta;
};

// | Extract the key (black) component.
var key = function (v) {
    return v.key;
};
var eqCMYK = {
    eq: function (x) {
        return function (y) {
            return eq(x.cyan)(y.cyan) && eq1(x.key)(y.key) && eq2(x.magenta)(y.magenta) && eq3(x.yellow)(y.yellow);
        };
    }
};
var ordCMYK = {
    compare: function (x) {
        return function (y) {
            var v = compare(x.cyan)(y.cyan);
            if (v instanceof Data_Ordering.LT) {
                return Data_Ordering.LT.value;
            };
            if (v instanceof Data_Ordering.GT) {
                return Data_Ordering.GT.value;
            };
            var v1 = compare1(x.key)(y.key);
            if (v1 instanceof Data_Ordering.LT) {
                return Data_Ordering.LT.value;
            };
            if (v1 instanceof Data_Ordering.GT) {
                return Data_Ordering.GT.value;
            };
            var v2 = compare2(x.magenta)(y.magenta);
            if (v2 instanceof Data_Ordering.LT) {
                return Data_Ordering.LT.value;
            };
            if (v2 instanceof Data_Ordering.GT) {
                return Data_Ordering.GT.value;
            };
            return compare3(x.yellow)(y.yellow);
        };
    },
    Eq0: function () {
        return eqCMYK;
    }
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // accessors
// ═══════════════════════════════════════════════════════════════════════════════
// | Extract the cyan component.
var cyan = function (v) {
    return v.cyan;
};

// | Convert CMYK to RGB.
// |
// | This is an approximation - actual conversion depends on color profiles,
// | ink characteristics, and paper type. For accurate conversion, use ICC
// | color profiles.
// |
// | Algorithm:
// | 1. Normalize CMYK to 0.0-1.0
// | 2. R = 255 × (1-C) × (1-K)
// | 3. G = 255 × (1-M) × (1-K)
// | 4. B = 255 × (1-Y) × (1-K)
// |
// | ```purescript
// | cmykToRgb (cmyk 0 100 100 0)  -- CMYK Red → RGB(255, 0, 0)
// | ```
var cmykToRgb = function (v) {
    var yVal = Hydrogen_Schema_Color_Yellow.toUnitInterval(v.yellow);
    var mVal = Hydrogen_Schema_Color_Magenta.toUnitInterval(v.magenta);
    var kVal = Hydrogen_Schema_Color_Key.toUnitInterval(v.key);
    var g = 255.0 * (1.0 - mVal) * (1.0 - kVal);
    var cVal = Hydrogen_Schema_Color_Cyan.toUnitInterval(v.cyan);
    var r = 255.0 * (1.0 - cVal) * (1.0 - kVal);
    var b = 255.0 * (1.0 - yVal) * (1.0 - kVal);
    return Hydrogen_Schema_Color_RGB.rgb(Data_Int.round(r))(Data_Int.round(g))(Data_Int.round(b));
};

// | Convert to a record of raw Int values.
// |
// | Useful for interop with other systems or JSON serialization.
var cmykToRecord = function (v) {
    return {
        c: Hydrogen_Schema_Color_Cyan.unwrap(v.cyan),
        m: Hydrogen_Schema_Color_Magenta.unwrap(v.magenta),
        y: Hydrogen_Schema_Color_Yellow.unwrap(v.yellow),
        k: Hydrogen_Schema_Color_Key.unwrap(v.key)
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // css output
// ═══════════════════════════════════════════════════════════════════════════════
// | Convert to CSS device-cmyk() function string.
// |
// | Uses CSS Color Level 4 device-cmyk() syntax:
// | ```purescript
// | cmykToCss (cmyk 0 100 100 0)  -- "device-cmyk(0%, 100%, 100%, 0%)"
// | ```
var cmykToCss = function (v) {
    return "device-cmyk(" + (show(Hydrogen_Schema_Color_Cyan.unwrap(v.cyan)) + ("%" + (", " + (show(Hydrogen_Schema_Color_Magenta.unwrap(v.magenta)) + ("%" + (", " + (show(Hydrogen_Schema_Color_Yellow.unwrap(v.yellow)) + ("%" + (", " + (show(Hydrogen_Schema_Color_Key.unwrap(v.key)) + "%)"))))))))));
};
var showCMYK = {
    show: cmykToCss
};

// | Create from already-validated atoms.
// |
// | Use when you already have valid Cyan, Magenta, Yellow, Key values.
var cmykFromComponents = function (c) {
    return function (m) {
        return function (y) {
            return function (k) {
                return {
                    cyan: c,
                    magenta: m,
                    yellow: y,
                    key: k
                };
            };
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // constructors
// ═══════════════════════════════════════════════════════════════════════════════
// | Create a CMYK color from raw percentage values.
// |
// | All values are ink percentages (0-100):
// | ```purescript
// | cmyk 0 100 100 0    -- Red (no cyan, full magenta+yellow)
// | cmyk 100 0 0 0      -- Cyan
// | cmyk 0 0 0 100      -- Pure black
// | cmyk 50 40 40 100   -- Rich black (black + some color)
// | ```
var cmyk = function (c) {
    return function (m) {
        return function (y) {
            return function (k) {
                return {
                    cyan: Hydrogen_Schema_Color_Cyan.cyan(c),
                    magenta: Hydrogen_Schema_Color_Magenta.magenta(m),
                    yellow: Hydrogen_Schema_Color_Yellow.yellow(y),
                    key: Hydrogen_Schema_Color_Key.key(k)
                };
            };
        };
    };
};

// | Create from a record of raw values.
var cmykFromRecord = function (v) {
    return cmyk(v.c)(v.m)(v.y)(v.k);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // conversion
// ═══════════════════════════════════════════════════════════════════════════════
// | Convert RGB to CMYK.
// |
// | This is an approximation - actual conversion depends on color profiles,
// | ink characteristics, and paper type. For print-accurate conversion,
// | use ICC color profiles.
// |
// | Algorithm:
// | 1. Normalize RGB to 0.0-1.0
// | 2. Calculate K = 1 - max(R, G, B)
// | 3. If K = 1 (black), C=M=Y=0
// | 4. Otherwise: C = (1-R-K)/(1-K), M = (1-G-K)/(1-K), Y = (1-B-K)/(1-K)
// |
// | ```purescript
// | rgbToCmyk (RGB.rgb 255 0 0)  -- Red → CMYK(0, 100, 100, 0)
// | rgbToCmyk (RGB.rgb 0 0 0)    -- Black → CMYK(0, 0, 0, 100)
// | ```
var rgbToCmyk = function (rgb) {
    var r = Data_Int.toNumber(Hydrogen_Schema_Color_Channel.unwrap(Hydrogen_Schema_Color_RGB.red(rgb))) / 255.0;
    var g = Data_Int.toNumber(Hydrogen_Schema_Color_Channel.unwrap(Hydrogen_Schema_Color_RGB.green(rgb))) / 255.0;
    var b = Data_Int.toNumber(Hydrogen_Schema_Color_Channel.unwrap(Hydrogen_Schema_Color_RGB.blue(rgb))) / 255.0;
    var k = 1.0 - Hydrogen_Math_Core.max(Hydrogen_Math_Core.max(r)(g))(b);
    
    // If completely black, CMY are all 0
var result = (function () {
        var $53 = k >= 1.0;
        if ($53) {
            return {
                c: 0.0,
                m: 0.0,
                y: 0.0,
                k: 1.0
            };
        };
        return {
            c: (1.0 - r - k) / (1.0 - k),
            m: (1.0 - g - k) / (1.0 - k),
            y: (1.0 - b - k) / (1.0 - k),
            k: k
        };
    })();
    return cmyk(Data_Int.round(result.c * 100.0))(Data_Int.round(result.m * 100.0))(Data_Int.round(result.y * 100.0))(Data_Int.round(result.k * 100.0));
};
export {
    cmyk,
    cmykFromRecord,
    cmykFromComponents,
    cyan,
    magenta,
    yellow,
    key,
    cmykToRecord,
    cmykToCss,
    rgbToCmyk,
    cmykToRgb,
    eqCMYK,
    ordCMYK,
    showCMYK
};
