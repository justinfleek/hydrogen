// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                         // hydrogen // schema // color // hsl
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | HSL color molecule - composition of Hue, Saturation, Lightness atoms.
// |
// | HSL (Hue, Saturation, Lightness) is a cylindrical color space that
// | separates color identity (hue) from color properties (saturation, lightness).
// | This makes it intuitive for color manipulation:
// |
// | - **Hue**: Position on the color wheel (0-359°)
// | - **Saturation**: Color intensity/purity (0-100%)
// | - **Lightness**: Light/dark level (0-100%)
// |
// | ## Color Wheel Reference
// |
// | ```
// |   0°/360° = Red
// |      60°  = Yellow
// |     120°  = Green
// |     180°  = Cyan
// |     240°  = Blue
// |     300°  = Magenta
// | ```
// |
// | ## Lightness Behavior
// |
// | - At L=0%, any hue is black
// | - At L=50%, colors are most vivid
// | - At L=100%, any hue is white
import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Ordering from "../Data.Ordering/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Hydrogen_Schema_Color_Hue from "../Hydrogen.Schema.Color.Hue/index.js";
import * as Hydrogen_Schema_Color_Lightness from "../Hydrogen.Schema.Color.Lightness/index.js";
import * as Hydrogen_Schema_Color_Saturation from "../Hydrogen.Schema.Color.Saturation/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);
var eq = /* #__PURE__ */ Data_Eq.eq(Hydrogen_Schema_Color_Hue.eqHue);
var eq1 = /* #__PURE__ */ Data_Eq.eq(Hydrogen_Schema_Color_Lightness.eqLightness);
var eq2 = /* #__PURE__ */ Data_Eq.eq(Hydrogen_Schema_Color_Saturation.eqSaturation);
var compare = /* #__PURE__ */ Data_Ord.compare(Hydrogen_Schema_Color_Hue.ordHue);
var compare1 = /* #__PURE__ */ Data_Ord.compare(Hydrogen_Schema_Color_Lightness.ordLightness);
var compare2 = /* #__PURE__ */ Data_Ord.compare(Hydrogen_Schema_Color_Saturation.ordSaturation);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                         // hsl
// ═══════════════════════════════════════════════════════════════════════════════
// | HSL color value - a molecule composed of three atoms.
// |
// | This is a lawful composition: if Hue, Saturation, and Lightness are each
// | correct (valid bounds, proper semantics), then HSL is correct by construction.
var HSL = function (x) {
    return x;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // css output
// ═══════════════════════════════════════════════════════════════════════════════
// | Convert to CSS hsl() function string.
// |
// | ```purescript
// | toCss (hsl 210 80 50)  -- "hsl(210, 80%, 50%)"
// | ```
var toCss = function (v) {
    return "hsl(" + (show(Hydrogen_Schema_Color_Hue.unwrap(v.hue)) + (", " + (show(Hydrogen_Schema_Color_Saturation.unwrap(v.saturation)) + ("%" + (", " + (show(Hydrogen_Schema_Color_Lightness.unwrap(v.lightness)) + "%)"))))));
};
var showHSL = {
    show: toCss
};

// | Extract the saturation component.
var saturation = function (v) {
    return v.saturation;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // operations
// ═══════════════════════════════════════════════════════════════════════════════
// ═══════════════════════════════════════════════════════════════════════════════
//                                                 // operations // explicit names
// ═══════════════════════════════════════════════════════════════════════════════
// | Rotate hue by degrees (wraps around the color wheel).
// |
// | **Semantically explicit name:** `rotateHue` makes clear this operates on hue angle.
// |
// | ```purescript
// | rotateHue 120 (hsl 0 100 50)   -- Red → Green
// | rotateHue (-60) (hsl 60 100 50) -- Yellow → Red
// | ```
var rotateHue = function (degrees) {
    return function (v) {
        return {
            hue: Hydrogen_Schema_Color_Hue.rotate(degrees)(v.hue),
            saturation: v.saturation,
            lightness: v.lightness
        };
    };
};

// | Extract the lightness component.
var lightness = function (v) {
    return v.lightness;
};

// | Increase HSL saturation by percentage points.
// |
// | **NOTE:** HSL saturation differs from LCH chroma. For perceptually uniform saturation
// | adjustments, use LCH.increaseChroma.
// |
// | ```purescript
// | increaseSaturation 20 (hsl 0 50 50)  -- S: 50 → 70
// | ```
var increaseSaturation = function (amount) {
    return function (v) {
        return {
            hue: v.hue,
            saturation: Hydrogen_Schema_Color_Saturation.increase(amount)(v.saturation),
            lightness: v.lightness
        };
    };
};

// | Increase HSL lightness by percentage points.
// |
// | **WARNING:** HSL lightness is NOT perceptually uniform. For accurate "looks 10% lighter"
// | operations, convert to LAB via Conversion module and use `LAB.increaseLuminance`.
// |
// | ```purescript
// | increaseLightness 20 (hsl 0 100 50)  -- L: 50 → 70 (HSL space, not perceptual)
// | ```
var increaseLightness = function (amount) {
    return function (v) {
        return {
            hue: v.hue,
            saturation: v.saturation,
            lightness: Hydrogen_Schema_Color_Lightness.lighten(amount)(v.lightness)
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

// | Convert to a record of raw Int values.
// |
// | Useful for interop with other systems or JSON serialization.
// | **Explicitly named for backend persistence** - no conflicts with other color spaces.
var hslToRecord = function (v) {
    return {
        h: Hydrogen_Schema_Color_Hue.unwrap(v.hue),
        s: Hydrogen_Schema_Color_Saturation.unwrap(v.saturation),
        l: Hydrogen_Schema_Color_Lightness.unwrap(v.lightness)
    };
};

// | Generic alias for hslToRecord
var toRecord = hslToRecord;

// | Convert to legacy Value.purs HSL record.
// |
// | For interop with code still using `Hydrogen.Schema.Color.Value`.
var toLegacy = toRecord;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // constructors
// ═══════════════════════════════════════════════════════════════════════════════
// | Create an HSL color from raw values.
// |
// | Values are normalized by the underlying atoms:
// | - Hue clamps to 0-359 (use `rotate` for wrapping behavior)
// | - Saturation clamps to 0-100
// | - Lightness clamps to 0-100
// |
// | ```purescript
// | hsl 210 80 50  -- Ocean blue
// | hsl 0 100 50   -- Pure red
// | hsl 120 100 25 -- Dark green
// | ```
var hsl = function (h) {
    return function (s) {
        return function (l) {
            return {
                hue: Hydrogen_Schema_Color_Hue.hue(h),
                saturation: Hydrogen_Schema_Color_Saturation.saturation(s),
                lightness: Hydrogen_Schema_Color_Lightness.lightness(l)
            };
        };
    };
};

// | Create from a record of raw values.
// | **Explicitly named for backend persistence** - no conflicts with other color spaces.
var hslFromRecord = function (v) {
    return hsl(v.h)(v.s)(v.l);
};

// | Convert to grayscale (saturation = 0).
// |
// | Preserves hue information (can be re-saturated later).
var grayscale = function (v) {
    return {
        hue: v.hue,
        saturation: Hydrogen_Schema_Color_Saturation.saturation(0),
        lightness: v.lightness
    };
};

// | Generic alias for hslFromRecord
var fromRecord = hslFromRecord;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // interop
// ═══════════════════════════════════════════════════════════════════════════════
// | Convert from legacy Value.purs HSL record.
// |
// | For migration from `Hydrogen.Schema.Color.Value.HSL` to this module.
var fromLegacy = fromRecord;

// | Create from already-validated atoms.
// |
// | Use when you already have valid Hue, Saturation, Lightness values.
var fromComponents = function (h) {
    return function (s) {
        return function (l) {
            return {
                hue: h,
                saturation: s,
                lightness: l
            };
        };
    };
};
var eqHSL = {
    eq: function (x) {
        return function (y) {
            return eq(x.hue)(y.hue) && eq1(x.lightness)(y.lightness) && eq2(x.saturation)(y.saturation);
        };
    }
};
var ordHSL = {
    compare: function (x) {
        return function (y) {
            var v = compare(x.hue)(y.hue);
            if (v instanceof Data_Ordering.LT) {
                return Data_Ordering.LT.value;
            };
            if (v instanceof Data_Ordering.GT) {
                return Data_Ordering.GT.value;
            };
            var v1 = compare1(x.lightness)(y.lightness);
            if (v1 instanceof Data_Ordering.LT) {
                return Data_Ordering.LT.value;
            };
            if (v1 instanceof Data_Ordering.GT) {
                return Data_Ordering.GT.value;
            };
            return compare2(x.saturation)(y.saturation);
        };
    },
    Eq0: function () {
        return eqHSL;
    }
};

// | Decrease HSL saturation by percentage points.
// |
// | **NOTE:** HSL saturation differs from LCH chroma. For perceptually uniform saturation
// | adjustments, use LCH.decreaseChroma.
// |
// | ```purescript
// | decreaseSaturation 20 (hsl 0 100 50)  -- S: 100 → 80
// | ```
var decreaseSaturation = function (amount) {
    return function (v) {
        return {
            hue: v.hue,
            saturation: Hydrogen_Schema_Color_Saturation.decrease(amount)(v.saturation),
            lightness: v.lightness
        };
    };
};

// | Decrease HSL lightness by percentage points.
// |
// | **WARNING:** HSL lightness is NOT perceptually uniform. For accurate "looks 10% darker"
// | operations, convert to LAB via Conversion module and use `LAB.decreaseLuminance`.
// |
// | ```purescript
// | decreaseLightness 20 (hsl 0 100 50)  -- L: 50 → 30 (HSL space, not perceptual)
// | ```
var decreaseLightness = function (amount) {
    return function (v) {
        return {
            hue: v.hue,
            saturation: v.saturation,
            lightness: Hydrogen_Schema_Color_Lightness.darken(amount)(v.lightness)
        };
    };
};

// | Get the complementary color (opposite on color wheel).
// |
// | ```purescript
// | complement (hsl 0 100 50)   -- Red → Cyan (180°)
// | complement (hsl 60 100 50)  -- Yellow → Blue (240°)
// | ```
var complement = /* #__PURE__ */ rotateHue(180);
export {
    hsl,
    hslFromRecord,
    fromRecord,
    fromComponents,
    hue,
    saturation,
    lightness,
    hslToRecord,
    toRecord,
    rotateHue,
    complement,
    increaseLightness,
    decreaseLightness,
    increaseSaturation,
    decreaseSaturation,
    grayscale,
    toCss,
    fromLegacy,
    toLegacy,
    eqHSL,
    ordHSL,
    showHSL
};
