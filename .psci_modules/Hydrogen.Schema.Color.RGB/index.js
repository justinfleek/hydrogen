// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                         // hydrogen // schema // color // rgb
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | RGB color molecule — composition of three Channel atoms.
// |
// | RGB (Red, Green, Blue) is the additive color model used by displays.
// | Each channel represents light intensity from 0 (none) to 255 (full).
// |
// | - **Red**: Long wavelength light (~700nm)
// | - **Green**: Medium wavelength light (~546nm)
// | - **Blue**: Short wavelength light (~436nm)
// |
// | ## Additive Color Mixing
// |
// | ```
// | Red + Green       = Yellow
// | Green + Blue      = Cyan
// | Blue + Red        = Magenta
// | Red + Green + Blue = White
// | ```
// |
// | ## Device Dependency
// |
// | RGB values are device-dependent — the same values can appear differently
// | on different displays. For color-accurate work, use a color-managed
// | workflow with a defined color space (sRGB, Display P3, etc.).
import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_EuclideanRing from "../Data.EuclideanRing/index.js";
import * as Data_Int from "../Data.Int/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Ordering from "../Data.Ordering/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Hydrogen_Schema_Bounded from "../Hydrogen.Schema.Bounded/index.js";
import * as Hydrogen_Schema_Color_Channel from "../Hydrogen.Schema.Color.Channel/index.js";
import * as Hydrogen_Schema_Color_Opacity from "../Hydrogen.Schema.Color.Opacity/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);
var show1 = /* #__PURE__ */ Data_Show.show(Data_Show.showNumber);
var mod = /* #__PURE__ */ Data_EuclideanRing.mod(Data_EuclideanRing.euclideanRingInt);
var div1 = /* #__PURE__ */ Data_EuclideanRing.div(Data_EuclideanRing.euclideanRingInt);
var eq = /* #__PURE__ */ Data_Eq.eq(Hydrogen_Schema_Color_Opacity.eqOpacity);
var eq1 = /* #__PURE__ */ Data_Eq.eq(Hydrogen_Schema_Color_Channel.eqChannel);
var compare = /* #__PURE__ */ Data_Ord.compare(Hydrogen_Schema_Color_Opacity.ordOpacity);
var compare1 = /* #__PURE__ */ Data_Ord.compare(Hydrogen_Schema_Color_Channel.ordChannel);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                        // rgba
// ═══════════════════════════════════════════════════════════════════════════════
// | RGBA color value — RGB with an alpha channel.
// |
// | Alpha is an Opacity (0-100%): 0% = fully transparent, 100% = fully opaque.
// | This matches the pattern of other percentage-based atoms in the Schema.
var RGBA = function (x) {
    return x;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                         // rgb
// ═══════════════════════════════════════════════════════════════════════════════
// | RGB color value — a molecule composed of three Channel atoms.
// |
// | This is a lawful composition: if each Channel is correct (0-255, clamped),
// | then RGB is correct by construction. No invalid RGB values can exist.
var RGB = function (x) {
    return x;
};

// | Convert RGB to RGBA with full opacity (100%).
var toRGBA = function (v) {
    return {
        red: v.red,
        green: v.green,
        blue: v.blue,
        alpha: Hydrogen_Schema_Color_Opacity.opacity(100)
    };
};

// | Screen blend mode.
// |
// | Result = 255 - ((255 - A) × (255 - B)) / 255. Always lightens.
var screen = function (v) {
    return function (v1) {
        var screenChannels = function (a) {
            return function (b) {
                var b$prime = 255.0 - Data_Int.toNumber(Hydrogen_Schema_Color_Channel.unwrap(b));
                var a$prime = 255.0 - Data_Int.toNumber(Hydrogen_Schema_Color_Channel.unwrap(a));
                var result = 255.0 - (a$prime * b$prime) / 255.0;
                return Hydrogen_Schema_Color_Channel.channel(Data_Int.round(result));
            };
        };
        return {
            red: screenChannels(v.red)(v1.red),
            green: screenChannels(v.green)(v1.green),
            blue: screenChannels(v.blue)(v1.blue)
        };
    };
};

// | Convert RGBA to a record of raw Int values.
// |
// | Alpha is returned as percentage (0-100).
var rgbaToRecord = function (v) {
    return {
        r: Hydrogen_Schema_Color_Channel.unwrap(v.red),
        g: Hydrogen_Schema_Color_Channel.unwrap(v.green),
        b: Hydrogen_Schema_Color_Channel.unwrap(v.blue),
        a: Hydrogen_Schema_Color_Opacity.unwrap(v.alpha)
    };
};

// | Alias for rgbaToRecord (legacy name).
var toRecordA = rgbaToRecord;

// | Convert to CSS rgba() function string.
// |
// | CSS expects alpha as 0.0-1.0, so we use Opacity.toUnitInterval.
// |
// | ```purescript
// | rgbaToCss (rgba 255 128 0 100)  -- "rgba(255, 128, 0, 1.0)"
// | rgbaToCss (rgba 255 0 0 50)     -- "rgba(255, 0, 0, 0.5)"
// | ```
var rgbaToCss = function (v) {
    var a$prime = Hydrogen_Schema_Color_Opacity.toUnitInterval(v.alpha);
    return "rgba(" + (show(Hydrogen_Schema_Color_Channel.unwrap(v.red)) + (", " + (show(Hydrogen_Schema_Color_Channel.unwrap(v.green)) + (", " + (show(Hydrogen_Schema_Color_Channel.unwrap(v.blue)) + (", " + (show1(a$prime) + ")")))))));
};
var showRGBA = {
    show: rgbaToCss
};

// | Alias for rgbaToCss (legacy name).
var toCssA = rgbaToCss;

// | Create an RGBA color from raw values.
// |
// | Alpha is a percentage (0-100): 0 = transparent, 100 = opaque.
// |
// | ```purescript
// | rgba 255 128 0 100  -- Orange, fully opaque
// | rgba 255 0 0 50     -- Red, half transparent
// | rgba 0 0 0 0        -- Black, fully transparent
// | ```
var rgba = function (r) {
    return function (g) {
        return function (b) {
            return function (a) {
                return {
                    red: Hydrogen_Schema_Color_Channel.channel(r),
                    green: Hydrogen_Schema_Color_Channel.channel(g),
                    blue: Hydrogen_Schema_Color_Channel.channel(b),
                    alpha: Hydrogen_Schema_Color_Opacity.opacity(a)
                };
            };
        };
    };
};

// | Create an RGBA color from a record.
var rgbaFromRecord = function (v) {
    return rgba(v.r)(v.g)(v.b)(v.a);
};

// | Convert to a record of raw Int values.
// |
// | Useful for interop with other systems or JSON serialization.
var rgbToRecord = function (v) {
    return {
        r: Hydrogen_Schema_Color_Channel.unwrap(v.red),
        g: Hydrogen_Schema_Color_Channel.unwrap(v.green),
        b: Hydrogen_Schema_Color_Channel.unwrap(v.blue)
    };
};

// | Alias for rgbToRecord (legacy name).
var toRecord = rgbToRecord;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // css output
// ═══════════════════════════════════════════════════════════════════════════════
// | Convert to CSS rgb() function string.
// |
// | ```purescript
// | rgbToCss (rgb 255 128 0)  -- "rgb(255, 128, 0)"
// | ```
var rgbToCss = function (v) {
    return "rgb(" + (show(Hydrogen_Schema_Color_Channel.unwrap(v.red)) + (", " + (show(Hydrogen_Schema_Color_Channel.unwrap(v.green)) + (", " + (show(Hydrogen_Schema_Color_Channel.unwrap(v.blue)) + ")")))));
};
var showRGB = {
    show: rgbToCss
};

// | Alias for rgbToCss (legacy name).
var toCss = rgbToCss;

// | Create from already-validated Channel atoms.
// |
// | Use when you already have valid Channel values.
var rgbFromChannels = function (r) {
    return function (g) {
        return function (b) {
            return {
                red: r,
                green: g,
                blue: b
            };
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // constructors
// ═══════════════════════════════════════════════════════════════════════════════
// | Create an RGB color from raw values.
// |
// | Values are clamped to 0-255 by the underlying Channel atoms.
// |
// | ```purescript
// | rgb 255 128 0    -- Orange
// | rgb 0 0 0        -- Black
// | rgb 255 255 255  -- White
// | ```
var rgb = function (r) {
    return function (g) {
        return function (b) {
            return {
                red: Hydrogen_Schema_Color_Channel.channel(r),
                green: Hydrogen_Schema_Color_Channel.channel(g),
                blue: Hydrogen_Schema_Color_Channel.channel(b)
            };
        };
    };
};

// | Create from a record of raw values.
var rgbFromRecord = function (v) {
    return rgb(v.r)(v.g)(v.b);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // accessors
// ═══════════════════════════════════════════════════════════════════════════════
// | Extract the red channel.
var red = function (v) {
    return v.red;
};

// | Multiply blend mode.
// |
// | Result = (A × B) / 255. Always darkens.
var multiply = function (v) {
    return function (v1) {
        var multiplyChannels = function (a) {
            return function (b) {
                var product = (Data_Int.toNumber(Hydrogen_Schema_Color_Channel.unwrap(a)) * Data_Int.toNumber(Hydrogen_Schema_Color_Channel.unwrap(b))) / 255.0;
                return Hydrogen_Schema_Color_Channel.channel(Data_Int.round(product));
            };
        };
        return {
            red: multiplyChannels(v.red)(v1.red),
            green: multiplyChannels(v.green)(v1.green),
            blue: multiplyChannels(v.blue)(v1.blue)
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // operations
// ═══════════════════════════════════════════════════════════════════════════════
// | Invert the color (255 - each channel).
// |
// | ```purescript
// | invert (rgb 255 0 0)  -- rgb 0 255 255 (cyan)
// | invert (rgb 0 0 0)    -- rgb 255 255 255 (white)
// | ```
var invert = function (v) {
    return {
        red: Hydrogen_Schema_Color_Channel.invert(v.red),
        green: Hydrogen_Schema_Color_Channel.invert(v.green),
        blue: Hydrogen_Schema_Color_Channel.invert(v.blue)
    };
};

// | Convert int (0-15) to hex char.
var intToHexChar = function (n) {
    if (n === 0) {
        return "0";
    };
    if (n === 1) {
        return "1";
    };
    if (n === 2) {
        return "2";
    };
    if (n === 3) {
        return "3";
    };
    if (n === 4) {
        return "4";
    };
    if (n === 5) {
        return "5";
    };
    if (n === 6) {
        return "6";
    };
    if (n === 7) {
        return "7";
    };
    if (n === 8) {
        return "8";
    };
    if (n === 9) {
        return "9";
    };
    if (n === 10) {
        return "a";
    };
    if (n === 11) {
        return "b";
    };
    if (n === 12) {
        return "c";
    };
    if (n === 13) {
        return "d";
    };
    if (n === 14) {
        return "e";
    };
    if (n === 15) {
        return "f";
    };
    return "0";
};

// ─────────────────────────────────────────────────────────────────────────────
//                                                                  // internal
// ─────────────────────────────────────────────────────────────────────────────
// | Convert int (0-255) to 2-char hex string.
var intToHex = function (n) {
    var lo = mod(n)(16);
    var hi = div1(n)(16);
    return intToHexChar(hi) + intToHexChar(lo);
};

// | Convert to 6-character hex string (without #).
// |
// | ```purescript
// | rgbToHex (rgb 255 128 0)  -- "ff8000"
// | ```
var rgbToHex = function (v) {
    return intToHex(Hydrogen_Schema_Color_Channel.unwrap(v.red)) + (intToHex(Hydrogen_Schema_Color_Channel.unwrap(v.green)) + intToHex(Hydrogen_Schema_Color_Channel.unwrap(v.blue)));
};

// | Alias for rgbToHex (legacy name).
var toHex = rgbToHex;

// | Extract the green channel.
var green = function (v) {
    return v.green;
};

// | Alias for rgbFromRecord (legacy name).
var fromRecord = rgbFromRecord;

// | Convert RGBA to RGB (drops alpha).
var fromRGBA = function (v) {
    return {
        red: v.red,
        green: v.green,
        blue: v.blue
    };
};

// | Alias for rgbFromChannels (legacy name).
var fromChannels = rgbFromChannels;
var eqRGBA = {
    eq: function (x) {
        return function (y) {
            return eq(x.alpha)(y.alpha) && eq1(x.blue)(y.blue) && eq1(x.green)(y.green) && eq1(x.red)(y.red);
        };
    }
};
var ordRGBA = {
    compare: function (x) {
        return function (y) {
            var v = compare(x.alpha)(y.alpha);
            if (v instanceof Data_Ordering.LT) {
                return Data_Ordering.LT.value;
            };
            if (v instanceof Data_Ordering.GT) {
                return Data_Ordering.GT.value;
            };
            var v1 = compare1(x.blue)(y.blue);
            if (v1 instanceof Data_Ordering.LT) {
                return Data_Ordering.LT.value;
            };
            if (v1 instanceof Data_Ordering.GT) {
                return Data_Ordering.GT.value;
            };
            var v2 = compare1(x.green)(y.green);
            if (v2 instanceof Data_Ordering.LT) {
                return Data_Ordering.LT.value;
            };
            if (v2 instanceof Data_Ordering.GT) {
                return Data_Ordering.GT.value;
            };
            return compare1(x.red)(y.red);
        };
    },
    Eq0: function () {
        return eqRGBA;
    }
};
var eqRGB = {
    eq: function (x) {
        return function (y) {
            return eq1(x.blue)(y.blue) && eq1(x.green)(y.green) && eq1(x.red)(y.red);
        };
    }
};
var ordRGB = {
    compare: function (x) {
        return function (y) {
            var v = compare1(x.blue)(y.blue);
            if (v instanceof Data_Ordering.LT) {
                return Data_Ordering.LT.value;
            };
            if (v instanceof Data_Ordering.GT) {
                return Data_Ordering.GT.value;
            };
            var v1 = compare1(x.green)(y.green);
            if (v1 instanceof Data_Ordering.LT) {
                return Data_Ordering.LT.value;
            };
            if (v1 instanceof Data_Ordering.GT) {
                return Data_Ordering.GT.value;
            };
            return compare1(x.red)(y.red);
        };
    },
    Eq0: function () {
        return eqRGB;
    }
};

// | Extract the blue channel.
var blue = function (v) {
    return v.blue;
};

// | Blend two colors with a weight (0.0 = all first, 1.0 = all second).
// |
// | ```purescript
// | blend 0.5 (rgb 255 0 0) (rgb 0 0 255)  -- Purple-ish
// | ```
var blend = function (weight) {
    return function (v) {
        return function (v1) {
            var w = Hydrogen_Schema_Bounded.clampNumber(0.0)(1.0)(weight);
            return {
                red: Hydrogen_Schema_Color_Channel.blend(w)(v.red)(v1.red),
                green: Hydrogen_Schema_Color_Channel.blend(w)(v.green)(v1.green),
                blue: Hydrogen_Schema_Color_Channel.blend(w)(v.blue)(v1.blue)
            };
        };
    };
};

// | Extract the alpha (opacity).
var alpha = function (v) {
    return v.alpha;
};

// | Add two colors (clamped at 255).
// |
// | Additive blending — used for light mixing effects.
var add = function (v) {
    return function (v1) {
        return {
            red: Hydrogen_Schema_Color_Channel.add(v.red)(v1.red),
            green: Hydrogen_Schema_Color_Channel.add(v.green)(v1.green),
            blue: Hydrogen_Schema_Color_Channel.add(v.blue)(v1.blue)
        };
    };
};
export {
    rgb,
    rgbFromRecord,
    fromRecord,
    rgbFromChannels,
    fromChannels,
    red,
    green,
    blue,
    rgbToRecord,
    toRecord,
    invert,
    blend,
    add,
    multiply,
    screen,
    rgbToCss,
    toCss,
    rgbToHex,
    toHex,
    rgba,
    rgbaFromRecord,
    alpha,
    rgbaToRecord,
    toRecordA,
    rgbaToCss,
    toCssA,
    toRGBA,
    fromRGBA,
    eqRGB,
    ordRGB,
    showRGB,
    eqRGBA,
    ordRGBA,
    showRGBA
};
