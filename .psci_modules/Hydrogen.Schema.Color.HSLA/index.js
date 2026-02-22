// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                        // hydrogen // schema // color // hsla
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | HSLA color molecule - HSL with alpha transparency.
// |
// | HSLA extends HSL with an opacity channel, allowing for transparent colors
// | in the cylindrical color space.
// |
// | - **Hue**: Position on the color wheel (0-359°)
// | - **Saturation**: Color intensity/purity (0-100%)
// | - **Lightness**: Light/dark level (0-100%)
// | - **Alpha**: Opacity (0-100%): 0% = transparent, 100% = opaque
// |
// | Like HSL, this space is intuitive for color manipulation while supporting
// | transparency for UI effects, overlays, and compositing.
import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Ordering from "../Data.Ordering/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Hydrogen_Schema_Color_HSL from "../Hydrogen.Schema.Color.HSL/index.js";
import * as Hydrogen_Schema_Color_Hue from "../Hydrogen.Schema.Color.Hue/index.js";
import * as Hydrogen_Schema_Color_Lightness from "../Hydrogen.Schema.Color.Lightness/index.js";
import * as Hydrogen_Schema_Color_Opacity from "../Hydrogen.Schema.Color.Opacity/index.js";
import * as Hydrogen_Schema_Color_Saturation from "../Hydrogen.Schema.Color.Saturation/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);
var show1 = /* #__PURE__ */ Data_Show.show(Data_Show.showNumber);
var eq = /* #__PURE__ */ Data_Eq.eq(Hydrogen_Schema_Color_Opacity.eqOpacity);
var eq1 = /* #__PURE__ */ Data_Eq.eq(Hydrogen_Schema_Color_Hue.eqHue);
var eq2 = /* #__PURE__ */ Data_Eq.eq(Hydrogen_Schema_Color_Lightness.eqLightness);
var eq3 = /* #__PURE__ */ Data_Eq.eq(Hydrogen_Schema_Color_Saturation.eqSaturation);
var compare = /* #__PURE__ */ Data_Ord.compare(Hydrogen_Schema_Color_Opacity.ordOpacity);
var compare1 = /* #__PURE__ */ Data_Ord.compare(Hydrogen_Schema_Color_Hue.ordHue);
var compare2 = /* #__PURE__ */ Data_Ord.compare(Hydrogen_Schema_Color_Lightness.ordLightness);
var compare3 = /* #__PURE__ */ Data_Ord.compare(Hydrogen_Schema_Color_Saturation.ordSaturation);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                        // hsla
// ═══════════════════════════════════════════════════════════════════════════════
// | HSLA color value — HSL with an alpha channel.
// |
// | Alpha is an Opacity (0-100%): 0% = fully transparent, 100% = fully opaque.
// | This matches the pattern of other percentage-based atoms in the Schema.
var HSLA = function (x) {
    return x;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // conversion
// ═══════════════════════════════════════════════════════════════════════════════
// | Convert HSL to HSLA with full opacity (100%).
var toHSLA = function (hsl) {
    return {
        hue: Hydrogen_Schema_Color_HSL.hue(hsl),
        saturation: Hydrogen_Schema_Color_HSL.saturation(hsl),
        lightness: Hydrogen_Schema_Color_HSL.lightness(hsl),
        alpha: Hydrogen_Schema_Color_Opacity.opacity(100)
    };
};

// | Extract the saturation component.
var saturation = function (v) {
    return v.saturation;
};

// | Increase saturation by percentage points.
// |
// | Preserves alpha.
// |
// | ```purescript
// | saturate 20 (hsla 0 50 50 50)  -- S: 50 → 70, alpha unchanged
// | ```
var saturate = function (amount) {
    return function (v) {
        return {
            hue: v.hue,
            saturation: Hydrogen_Schema_Color_Saturation.increase(amount)(v.saturation),
            lightness: v.lightness,
            alpha: v.alpha
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // operations
// ═══════════════════════════════════════════════════════════════════════════════
// | Rotate hue by degrees (wraps around the color wheel).
// |
// | Preserves alpha.
// |
// | ```purescript
// | rotate 120 (hsla 0 100 50 50)   -- Red → Green (half transparent)
// | rotate (-60) (hsla 60 100 50 100) -- Yellow → Red (opaque)
// | ```
var rotate = function (degrees) {
    return function (v) {
        return {
            hue: Hydrogen_Schema_Color_Hue.rotate(degrees)(v.hue),
            saturation: v.saturation,
            lightness: v.lightness,
            alpha: v.alpha
        };
    };
};

// | Extract the lightness component.
var lightness = function (v) {
    return v.lightness;
};

// | Increase lightness by percentage points.
// |
// | Preserves alpha.
// |
// | ```purescript
// | lighten 20 (hsla 0 100 50 50)  -- L: 50 → 70, alpha unchanged
// | ```
var lighten = function (amount) {
    return function (v) {
        return {
            hue: v.hue,
            saturation: v.saturation,
            lightness: Hydrogen_Schema_Color_Lightness.lighten(amount)(v.lightness),
            alpha: v.alpha
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // accessors
// ═══════════════════════════════════════════════════════════════════════════════
// | Extract the hue component.
var hue = function (v) {
    return v.hue;
};

// | Convert HSLA to a record of raw Int values.
// |
// | All values are percentages (0-100) except hue (0-359).
var hslaToRecord = function (v) {
    return {
        h: Hydrogen_Schema_Color_Hue.unwrap(v.hue),
        s: Hydrogen_Schema_Color_Saturation.unwrap(v.saturation),
        l: Hydrogen_Schema_Color_Lightness.unwrap(v.lightness),
        a: Hydrogen_Schema_Color_Opacity.unwrap(v.alpha)
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // css output
// ═══════════════════════════════════════════════════════════════════════════════
// | Convert to CSS hsla() function string.
// |
// | CSS expects alpha as 0.0-1.0, so we use Opacity.toUnitInterval.
// |
// | ```purescript
// | hslaToCss (hsla 210 80 50 100)  -- "hsla(210, 80%, 50%, 1.0)"
// | hslaToCss (hsla 0 100 50 50)    -- "hsla(0, 100%, 50%, 0.5)"
// | ```
var hslaToCss = function (v) {
    var a$prime = Hydrogen_Schema_Color_Opacity.toUnitInterval(v.alpha);
    return "hsla(" + (show(Hydrogen_Schema_Color_Hue.unwrap(v.hue)) + (", " + (show(Hydrogen_Schema_Color_Saturation.unwrap(v.saturation)) + ("%" + (", " + (show(Hydrogen_Schema_Color_Lightness.unwrap(v.lightness)) + ("%" + (", " + (show1(a$prime) + ")")))))))));
};
var showHSLA = {
    show: hslaToCss
};

// | Create from already-validated components.
// |
// | Use when you already have valid Hue, Saturation, Lightness, Opacity atoms.
var hslaFromComponents = function (h) {
    return function (s) {
        return function (l) {
            return function (a) {
                return {
                    hue: h,
                    saturation: s,
                    lightness: l,
                    alpha: a
                };
            };
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // constructors
// ═══════════════════════════════════════════════════════════════════════════════
// | Create an HSLA color from raw values.
// |
// | - Hue: 0-359 (wraps)
// | - Saturation: 0-100 (percentage)
// | - Lightness: 0-100 (percentage)
// | - Alpha: 0-100 (percentage): 0 = transparent, 100 = opaque
// |
// | ```purescript
// | hsla 210 80 50 100  -- Ocean blue, fully opaque
// | hsla 0 100 50 50    -- Red, half transparent
// | hsla 120 100 25 0   -- Dark green, fully transparent
// | ```
var hsla = function (h) {
    return function (s) {
        return function (l) {
            return function (a) {
                return {
                    hue: Hydrogen_Schema_Color_Hue.hue(h),
                    saturation: Hydrogen_Schema_Color_Saturation.saturation(s),
                    lightness: Hydrogen_Schema_Color_Lightness.lightness(l),
                    alpha: Hydrogen_Schema_Color_Opacity.opacity(a)
                };
            };
        };
    };
};

// | Create an HSLA color from a record.
// |
// | Alpha is a percentage (0-100).
var hslaFromRecord = function (v) {
    return hsla(v.h)(v.s)(v.l)(v.a);
};

// | Convert to grayscale (saturation = 0).
// |
// | Preserves hue information (can be re-saturated later) and alpha.
// |
// | ```purescript
// | grayscale (hsla 0 100 50 50)  -- Gray, half transparent
// | ```
var grayscale = function (v) {
    return {
        hue: v.hue,
        saturation: Hydrogen_Schema_Color_Saturation.saturation(0),
        lightness: v.lightness,
        alpha: v.alpha
    };
};

// | Convert HSLA to HSL (drops alpha).
var fromHSLA = function (v) {
    return Hydrogen_Schema_Color_HSL.fromComponents(v.hue)(v.saturation)(v.lightness);
};

// | Decrease opacity by percentage points (make more transparent).
// |
// | Alias for `transparentize` - makes color more transparent.
// |
// | ```purescript
// | fadeOut 20 (hsla 0 100 50 50)  -- Alpha: 50 → 30
// | ```
var fadeOut = function (amount) {
    return function (v) {
        return {
            hue: v.hue,
            saturation: v.saturation,
            lightness: v.lightness,
            alpha: Hydrogen_Schema_Color_Opacity.decrease(amount)(v.alpha)
        };
    };
};

// | Decrease opacity by percentage points (make more transparent).
// |
// | Same as `fadeOut` - provided for semantic clarity in different contexts.
var transparentize = fadeOut;

// | Increase opacity by percentage points (make more opaque).
// |
// | Alias for `opacify` - makes color less transparent.
// |
// | ```purescript
// | fadeIn 20 (hsla 0 100 50 30)  -- Alpha: 30 → 50
// | ```
var fadeIn = function (amount) {
    return function (v) {
        return {
            hue: v.hue,
            saturation: v.saturation,
            lightness: v.lightness,
            alpha: Hydrogen_Schema_Color_Opacity.increase(amount)(v.alpha)
        };
    };
};

// | Increase opacity by percentage points (make more opaque).
// |
// | Same as `fadeIn` - provided for semantic clarity in different contexts.
var opacify = fadeIn;
var eqHSLA = {
    eq: function (x) {
        return function (y) {
            return eq(x.alpha)(y.alpha) && eq1(x.hue)(y.hue) && eq2(x.lightness)(y.lightness) && eq3(x.saturation)(y.saturation);
        };
    }
};
var ordHSLA = {
    compare: function (x) {
        return function (y) {
            var v = compare(x.alpha)(y.alpha);
            if (v instanceof Data_Ordering.LT) {
                return Data_Ordering.LT.value;
            };
            if (v instanceof Data_Ordering.GT) {
                return Data_Ordering.GT.value;
            };
            var v1 = compare1(x.hue)(y.hue);
            if (v1 instanceof Data_Ordering.LT) {
                return Data_Ordering.LT.value;
            };
            if (v1 instanceof Data_Ordering.GT) {
                return Data_Ordering.GT.value;
            };
            var v2 = compare2(x.lightness)(y.lightness);
            if (v2 instanceof Data_Ordering.LT) {
                return Data_Ordering.LT.value;
            };
            if (v2 instanceof Data_Ordering.GT) {
                return Data_Ordering.GT.value;
            };
            return compare3(x.saturation)(y.saturation);
        };
    },
    Eq0: function () {
        return eqHSLA;
    }
};

// | Decrease saturation by percentage points.
// |
// | Preserves alpha.
// |
// | ```purescript
// | desaturate 20 (hsla 0 100 50 50)  -- S: 100 → 80, alpha unchanged
// | ```
var desaturate = function (amount) {
    return function (v) {
        return {
            hue: v.hue,
            saturation: Hydrogen_Schema_Color_Saturation.decrease(amount)(v.saturation),
            lightness: v.lightness,
            alpha: v.alpha
        };
    };
};

// | Decrease lightness by percentage points.
// |
// | Preserves alpha.
// |
// | ```purescript
// | darken 20 (hsla 0 100 50 50)  -- L: 50 → 30, alpha unchanged
// | ```
var darken = function (amount) {
    return function (v) {
        return {
            hue: v.hue,
            saturation: v.saturation,
            lightness: Hydrogen_Schema_Color_Lightness.darken(amount)(v.lightness),
            alpha: v.alpha
        };
    };
};

// | Get the complementary color (opposite on color wheel).
// |
// | Preserves alpha.
// |
// | ```purescript
// | complement (hsla 0 100 50 50)   -- Red → Cyan (180°), half transparent
// | complement (hsla 60 100 50 100)  -- Yellow → Blue (240°), opaque
// | ```
var complement = /* #__PURE__ */ rotate(180);

// | Extract the alpha (opacity).
var alpha = function (v) {
    return v.alpha;
};
export {
    hsla,
    hslaFromRecord,
    hslaFromComponents,
    hue,
    saturation,
    lightness,
    alpha,
    hslaToRecord,
    rotate,
    complement,
    lighten,
    darken,
    saturate,
    desaturate,
    grayscale,
    fadeIn,
    fadeOut,
    opacify,
    transparentize,
    hslaToCss,
    toHSLA,
    fromHSLA,
    eqHSLA,
    ordHSLA,
    showHSLA
};
