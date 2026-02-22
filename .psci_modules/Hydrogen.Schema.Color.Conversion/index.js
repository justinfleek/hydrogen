// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                   // hydrogen // schema // color // conversion
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Color space conversions for picker/wheel synchronization.
// |
// | **BIDIRECTIONAL SYNC REQUIREMENT:**
// | When a user adjusts any color property (hue slider, RGB input, hex code),
// | ALL representations must update synchronously. This module provides the
// | mathematical conversions to maintain consistency across color spaces.
// |
// | **Use case: Playground color picker**
// | 1. User adjusts Hue slider (0-359)
// | 2. HSL updates → rgbToHsl converts → RGB updates
// | 3. RGB updates → rgbToHex converts → Hex display updates
// | 4. All views show the same color, zero drift
// |
// | **Color space conversions:**
// | - HSL ↔ RGB (color wheel ↔ display values)
// | - RGB ↔ CMYK (screen ↔ print)
// | - RGB ↔ Hex (code ↔ human-readable)
// | - Kelvin → RGB (temperature ↔ display)
// |
// | **Billion-agent scale requirement:**
// | All conversions use industry-standard algorithms. Two agents converting
// | the same color will get identical results (within floating point precision).
import * as Data_Boolean from "../Data.Boolean/index.js";
import * as Data_EuclideanRing from "../Data.EuclideanRing/index.js";
import * as Data_Int from "../Data.Int/index.js";
import * as Data_Number from "../Data.Number/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_String_CodePoints from "../Data.String.CodePoints/index.js";
import * as Data_String_CodeUnits from "../Data.String.CodeUnits/index.js";
import * as Hydrogen_Math_Core from "../Hydrogen.Math.Core/index.js";
import * as Hydrogen_Schema_Color_CMYK from "../Hydrogen.Schema.Color.CMYK/index.js";
import * as Hydrogen_Schema_Color_Channel from "../Hydrogen.Schema.Color.Channel/index.js";
import * as Hydrogen_Schema_Color_Cyan from "../Hydrogen.Schema.Color.Cyan/index.js";
import * as Hydrogen_Schema_Color_HSL from "../Hydrogen.Schema.Color.HSL/index.js";
import * as Hydrogen_Schema_Color_HWB from "../Hydrogen.Schema.Color.HWB/index.js";
import * as Hydrogen_Schema_Color_Hue from "../Hydrogen.Schema.Color.Hue/index.js";
import * as Hydrogen_Schema_Color_Kelvin from "../Hydrogen.Schema.Color.Kelvin/index.js";
import * as Hydrogen_Schema_Color_Key from "../Hydrogen.Schema.Color.Key/index.js";
import * as Hydrogen_Schema_Color_LAB from "../Hydrogen.Schema.Color.LAB/index.js";
import * as Hydrogen_Schema_Color_LCH from "../Hydrogen.Schema.Color.LCH/index.js";
import * as Hydrogen_Schema_Color_Lightness from "../Hydrogen.Schema.Color.Lightness/index.js";
import * as Hydrogen_Schema_Color_Magenta from "../Hydrogen.Schema.Color.Magenta/index.js";
import * as Hydrogen_Schema_Color_OKLAB from "../Hydrogen.Schema.Color.OKLAB/index.js";
import * as Hydrogen_Schema_Color_OKLCH from "../Hydrogen.Schema.Color.OKLCH/index.js";
import * as Hydrogen_Schema_Color_RGB from "../Hydrogen.Schema.Color.RGB/index.js";
import * as Hydrogen_Schema_Color_Saturation from "../Hydrogen.Schema.Color.Saturation/index.js";
import * as Hydrogen_Schema_Color_XYZ from "../Hydrogen.Schema.Color.XYZ/index.js";
import * as Hydrogen_Schema_Color_YUV from "../Hydrogen.Schema.Color.YUV/index.js";
import * as Hydrogen_Schema_Color_Yellow from "../Hydrogen.Schema.Color.Yellow/index.js";
var max = /* #__PURE__ */ Data_Ord.max(Data_Ord.ordNumber);
var min = /* #__PURE__ */ Data_Ord.min(Data_Ord.ordNumber);
var mod = /* #__PURE__ */ Data_EuclideanRing.mod(Data_EuclideanRing.euclideanRingInt);
var div1 = /* #__PURE__ */ Data_EuclideanRing.div(Data_EuclideanRing.euclideanRingInt);

// | YUV → RGB
var yuvToRgb = function (yuv) {
    var y = Hydrogen_Schema_Color_YUV.unwrapLuma(Hydrogen_Schema_Color_YUV.getLuma(yuv));
    var v = Hydrogen_Schema_Color_YUV.unwrapV(Hydrogen_Schema_Color_YUV.getV(yuv));
    var u = Hydrogen_Schema_Color_YUV.unwrapU(Hydrogen_Schema_Color_YUV.getU(yuv));
    
    // ITU-R BT.601 inverse
var r = y + 1.14 * v;
    var g = y - 0.395 * u - 0.581 * v;
    var b = y + 2.032 * u;
    return Hydrogen_Schema_Color_RGB.rgb(Data_Int.round(r * 255.0))(Data_Int.round(g * 255.0))(Data_Int.round(b * 255.0));
};

// | Convert XYZ to RGB (device-independent to device-dependent)
// |
// | Assumes sRGB color space with D65 white point.
// | Steps:
// | 1. Apply XYZ → sRGB matrix transformation
// | 2. Apply sRGB companding (gamma correction)
// | 3. Convert 0-1 to RGB 0-255
// |
// | ```purescript
// | xyzToRgb XYZ.d65White  -- RGB(255, 255, 255)
// | ```
var xyzToRgb = function (xyzColor) {
    var clamp01 = function (n) {
        if (n < 0.0) {
            return 0.0;
        };
        if (n > 1.0) {
            return 1.0;
        };
        if (Data_Boolean.otherwise) {
            return n;
        };
        throw new Error("Failed pattern match at Hydrogen.Schema.Color.Conversion (line 409, column 5 - line 412, column 22): " + [ n.constructor.name ]);
    };
    var rec = Hydrogen_Schema_Color_XYZ.toRecord(xyzColor);
    
    // Apply XYZ → sRGB matrix (D65)
var r$prime = rec.x * 3.2404542 + rec.y * -1.5371385 + rec.z * -0.4985314;
    
    // Apply sRGB companding (gamma correction)
var r = (function () {
        var $26 = r$prime <= 3.1308e-3;
        if ($26) {
            return r$prime * 12.92;
        };
        return 1.055 * Data_Number.pow(r$prime)(1.0 / 2.4) - 5.5e-2;
    })();
    
    // Clamp and convert to 0-255
var rInt = Data_Int.round(clamp01(r) * 255.0);
    var g$prime = rec.x * -0.969266 + rec.y * 1.8760108 + rec.z * 4.1556e-2;
    var g = (function () {
        var $27 = g$prime <= 3.1308e-3;
        if ($27) {
            return g$prime * 12.92;
        };
        return 1.055 * Data_Number.pow(g$prime)(1.0 / 2.4) - 5.5e-2;
    })();
    var gInt = Data_Int.round(clamp01(g) * 255.0);
    var b$prime = rec.x * 5.56434e-2 + rec.y * -0.2040259 + rec.z * 1.0572252;
    var b = (function () {
        var $28 = b$prime <= 3.1308e-3;
        if ($28) {
            return b$prime * 12.92;
        };
        return 1.055 * Data_Number.pow(b$prime)(1.0 / 2.4) - 5.5e-2;
    })();
    var bInt = Data_Int.round(clamp01(b) * 255.0);
    return Hydrogen_Schema_Color_RGB.rgb(rInt)(gInt)(bInt);
};

// | XYZ → Record (for JSON serialization / backend persistence)
var xyzToRecord = Hydrogen_Schema_Color_XYZ.xyzToRecord;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // xyz ↔ lab
// ═══════════════════════════════════════════════════════════════════════════════
// | Convert XYZ to LAB (device-independent to perceptual)
// |
// | Uses D65 white point and CIE standard formulas.
// | This is where the perceptual uniformity is created.
// |
// | ```purescript
// | xyzToLab XYZ.d65White  -- LAB(100, 0, 0) - white
// | ```
var xyzToLab = function (xyzColor) {
    
    // CIE LAB function (piecewise)
var labF = function (t) {
        var $29 = t > 8.856e-3;
        if ($29) {
            return Data_Number.pow(t)(1.0 / 3.0);
        };
        return 7.787 * t + 16.0 / 116.0;
    };
    var rec = Hydrogen_Schema_Color_XYZ.toRecord(xyzColor);
    
    // Normalize by D65 white point
var xr = rec.x / 0.95047;
    var yr = rec.y / 1.0;
    var zr = rec.z / 1.08883;
    var fz = labF(zr);
    var fy = labF(yr);
    
    // Calculate L*, a*, b*
var l = 116.0 * fy - 16.0;
    
    // Apply CIE LAB function
var fx = labF(xr);
    var b = 200.0 * (fy - fz);
    var a = 500.0 * (fx - fy);
    return Hydrogen_Schema_Color_LAB.lab(l)(a)(b);
};

// | Record → XYZ (from JSON deserialization / backend)
var xyzFromRecord = Hydrogen_Schema_Color_XYZ.xyzFromRecord;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // rgb ↔ yuv
// ═══════════════════════════════════════════════════════════════════════════════
// | RGB → YUV (video color space)
var rgbToYuv = function (rgb) {
    var r = Hydrogen_Schema_Color_Channel.toNumber(Hydrogen_Schema_Color_RGB.red(rgb)) / 255.0;
    var g = Hydrogen_Schema_Color_Channel.toNumber(Hydrogen_Schema_Color_RGB.green(rgb)) / 255.0;
    var b = Hydrogen_Schema_Color_Channel.toNumber(Hydrogen_Schema_Color_RGB.blue(rgb)) / 255.0;
    
    // ITU-R BT.601 coefficients (standard definition)
var y = 0.299 * r + 0.587 * g + 0.114 * b;
    var u = 0.492 * (b - y);
    var v = 0.877 * (r - y);
    return Hydrogen_Schema_Color_YUV.yuv(y)(u)(v);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // rgb ↔ xyz
// ═══════════════════════════════════════════════════════════════════════════════
// | Convert RGB to XYZ (device-dependent to device-independent)
// |
// | Assumes sRGB color space with D65 white point.
// | Steps:
// | 1. Convert RGB 0-255 to 0-1
// | 2. Apply inverse sRGB companding (gamma correction)
// | 3. Apply sRGB → XYZ matrix transformation
// |
// | ```purescript
// | rgbToXyz (RGB.rgb 255 255 255)  -- D65 white point
// | rgbToXyz (RGB.rgb 0 0 0)        -- Black
// | ```
var rgbToXyz = function (rgb) {
    var r = Data_Int.toNumber(Hydrogen_Schema_Color_Channel.unwrap(Hydrogen_Schema_Color_RGB.red(rgb))) / 255.0;
    
    // Apply inverse sRGB companding (gamma correction)
var r$prime = (function () {
        var $30 = r <= 4.045e-2;
        if ($30) {
            return r / 12.92;
        };
        return Data_Number.pow((r + 5.5e-2) / 1.055)(2.4);
    })();
    var g = Data_Int.toNumber(Hydrogen_Schema_Color_Channel.unwrap(Hydrogen_Schema_Color_RGB.green(rgb))) / 255.0;
    var g$prime = (function () {
        var $31 = g <= 4.045e-2;
        if ($31) {
            return g / 12.92;
        };
        return Data_Number.pow((g + 5.5e-2) / 1.055)(2.4);
    })();
    var b = Data_Int.toNumber(Hydrogen_Schema_Color_Channel.unwrap(Hydrogen_Schema_Color_RGB.blue(rgb))) / 255.0;
    var b$prime = (function () {
        var $32 = b <= 4.045e-2;
        if ($32) {
            return b / 12.92;
        };
        return Data_Number.pow((b + 5.5e-2) / 1.055)(2.4);
    })();
    
    // Apply sRGB → XYZ matrix (D65)
var x = r$prime * 0.4124564 + g$prime * 0.3575761 + b$prime * 0.1804375;
    var y = r$prime * 0.2126729 + g$prime * 0.7151522 + b$prime * 7.2175e-2;
    var z = r$prime * 1.93339e-2 + g$prime * 0.119192 + b$prime * 0.9503041;
    return Hydrogen_Schema_Color_XYZ.xyz(x)(y)(z);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                         // record // serialization // conversions
// ═══════════════════════════════════════════════════════════════════════════════
// | RGB → Record (for JSON serialization / backend persistence)
var rgbToRecord = Hydrogen_Schema_Color_RGB.rgbToRecord;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                             // rgb ↔ oklab
// ═══════════════════════════════════════════════════════════════════════════════
// | RGB → OKLAB (modern perceptual uniform space)
// | Uses linear RGB → LMS → OKLAB transformation
var rgbToOklab = function (rgb) {
    var toLinear = function (c) {
        if (c <= 4.045e-2) {
            return c / 12.92;
        };
        if (Data_Boolean.otherwise) {
            return Data_Number.pow((c + 5.5e-2) / 1.055)(2.4);
        };
        throw new Error("Failed pattern match at Hydrogen.Schema.Color.Conversion (line 710, column 3 - line 712, column 48): " + [ c.constructor.name ]);
    };
    
    // Cube root (∛x)
var cbrt = function (x) {
        return Data_Number.pow(x)(1.0 / 3.0);
    };
    
    // Convert to linear RGB (remove sRGB gamma)
var r = toLinear(Hydrogen_Schema_Color_Channel.toNumber(Hydrogen_Schema_Color_RGB.red(rgb)) / 255.0);
    var g = toLinear(Hydrogen_Schema_Color_Channel.toNumber(Hydrogen_Schema_Color_RGB.green(rgb)) / 255.0);
    var b = toLinear(Hydrogen_Schema_Color_Channel.toNumber(Hydrogen_Schema_Color_RGB.blue(rgb)) / 255.0);
    
    // Linear RGB → LMS (cone response)
var l = 0.4122214708 * r + 0.5363325363 * g + 5.14459929e-2 * b;
    
    // LMS → OKLAB (cube root for perceptual uniformity)
var l$prime = cbrt(l);
    var m = 0.2119034982 * r + 0.6806995451 * g + 0.1073969566 * b;
    var m$prime = cbrt(m);
    var s = 8.83024619e-2 * r + 0.2817188376 * g + 0.6299787005 * b;
    var s$prime = cbrt(s);
    var okA = (1.9779984951 * l$prime - 2.428592205 * m$prime) + 0.4505937099 * s$prime;
    var okB = (2.59040371e-2 * l$prime + 0.7827717662 * m$prime) - 0.808675766 * s$prime;
    var okL = (0.2104542553 * l$prime + 0.793617785 * m$prime) - 4.0720468e-3 * s$prime;
    return Hydrogen_Schema_Color_OKLAB.oklab(okL)(okA)(okB);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                    // rgb ↔ lab (convenience)
// ═══════════════════════════════════════════════════════════════════════════════
// | Convert RGB to LAB (convenience function)
// |
// | Goes through XYZ: RGB → XYZ → LAB
// |
// | ```purescript
// | rgbToLab (RGB.rgb 255 0 0)  -- Red in perceptual space
// | ```
var rgbToLab = function ($71) {
    return xyzToLab(rgbToXyz($71));
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                    // rgb ↔ lch (convenience)
// ═══════════════════════════════════════════════════════════════════════════════
// | Convert RGB to LCH (convenience function)
// |
// | Goes through XYZ and LAB: RGB → XYZ → LAB → LCH
// |
// | ```purescript
// | rgbToLch (RGB.rgb 255 0 0)  -- Red in cylindrical perceptual space
// | ```
var rgbToLch = function ($72) {
    return Hydrogen_Schema_Color_LCH.labToLch(rgbToLab($72));
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // rgb ↔ cmyk
// ═══════════════════════════════════════════════════════════════════════════════
// | Convert RGB to CMYK (screen to print)
// |
// | Uses standard RGB → CMYK algorithm:
// | 1. Normalize RGB to 0-1 range
// | 2. Calculate K (black key) = 1 - max(R, G, B)
// | 3. If K = 1 (pure black), C=M=Y=0
// | 4. Otherwise: C = (1-R-K)/(1-K), same for M and Y
// |
// | ```purescript
// | rgbToCmyk (RGB.rgb 255 0 0)    -- CMYK(0, 100, 100, 0) - red
// | rgbToCmyk (RGB.rgb 0 0 0)      -- CMYK(0, 0, 0, 100) - black
// | ```
var rgbToCmyk = function (rgb) {
    var r = Data_Int.toNumber(Hydrogen_Schema_Color_Channel.unwrap(Hydrogen_Schema_Color_RGB.red(rgb))) / 255.0;
    var g = Data_Int.toNumber(Hydrogen_Schema_Color_Channel.unwrap(Hydrogen_Schema_Color_RGB.green(rgb))) / 255.0;
    var b = Data_Int.toNumber(Hydrogen_Schema_Color_Channel.unwrap(Hydrogen_Schema_Color_RGB.blue(rgb))) / 255.0;
    var k = 1.0 - max(r)(max(g)(b));
    var v = (function () {
        var $34 = k >= 1.0;
        if ($34) {
            return {
                c: 0.0,
                m: 0.0,
                y: 0.0
            };
        };
        return {
            c: (1.0 - r - k) / (1.0 - k),
            m: (1.0 - g - k) / (1.0 - k),
            y: (1.0 - b - k) / (1.0 - k)
        };
    })();
    var yInt = Data_Int.round(v.y * 100.0);
    var mInt = Data_Int.round(v.m * 100.0);
    var kInt = Data_Int.round(k * 100.0);
    
    // Convert to percentages
var cInt = Data_Int.round(v.c * 100.0);
    return Hydrogen_Schema_Color_CMYK.cmyk(cInt)(mInt)(yInt)(kInt);
};

// | Record → RGB (from JSON deserialization / backend)
var rgbFromRecord = Hydrogen_Schema_Color_RGB.rgbFromRecord;

// | OKLCH → OKLAB (cylindrical → rectangular)
var oklchToOklab = function (oklch) {
    var sin = function (x) {
        return Hydrogen_Math_Core.sin(x);
    };
    var cos = function (x) {
        return Hydrogen_Math_Core.cos(x);
    };
    var okL = Hydrogen_Schema_Color_OKLAB.unwrapOkL(Hydrogen_Schema_Color_OKLCH.oklchL(oklch));
    var h = Data_Int.toNumber(Hydrogen_Schema_Color_Hue.unwrap(Hydrogen_Schema_Color_OKLCH.hue(oklch)));
    
    // Convert hue to radians
var hRad = (h * Hydrogen_Math_Core.pi) / 180.0;
    var c = Hydrogen_Schema_Color_OKLCH.unwrapChroma(Hydrogen_Schema_Color_OKLCH.chroma(oklch));
    
    // Chroma and hue → a,b
var okA = c * cos(hRad);
    var okB = c * sin(hRad);
    return Hydrogen_Schema_Color_OKLAB.oklab(okL)(okA)(okB);
};

// | OKLAB → RGB
var oklabToRgb = function (oklab) {
    var toGamma = function (c) {
        if (c <= 3.1308e-3) {
            return 12.92 * c;
        };
        if (Data_Boolean.otherwise) {
            return 1.055 * Data_Number.pow(c)(1.0 / 2.4) - 5.5e-2;
        };
        throw new Error("Failed pattern match at Hydrogen.Schema.Color.Conversion (line 747, column 3 - line 749, column 52): " + [ c.constructor.name ]);
    };
    var okL = Hydrogen_Schema_Color_OKLAB.unwrapOkL(Hydrogen_Schema_Color_OKLAB.okL(oklab));
    var okB = Hydrogen_Schema_Color_OKLAB.unwrapOkB(Hydrogen_Schema_Color_OKLAB.okB(oklab));
    var okA = Hydrogen_Schema_Color_OKLAB.unwrapOkA(Hydrogen_Schema_Color_OKLAB.okA(oklab));
    var s$prime = okL - 8.94841775e-2 * okA - 1.291485548 * okB;
    var s = s$prime * s$prime * s$prime;
    var m$prime = okL - 0.1055613458 * okA - 6.38541728e-2 * okB;
    var m = m$prime * m$prime * m$prime;
    
    // OKLAB → LMS (inverse)
var l$prime = okL + 0.3963377774 * okA + 0.2158037573 * okB;
    
    // LMS → Linear RGB (cube and inverse matrix)
var l = l$prime * l$prime * l$prime;
    var r = (4.0767416621 * l - 3.3077115913 * m) + 0.2309699292 * s;
    
    // Linear RGB → sRGB (apply gamma)
var rGamma = toGamma(r);
    var g = (-1.2684380046 * l + 2.6097574011 * m) - 0.3413193965 * s;
    var gGamma = toGamma(g);
    var b = (-4.1960863e-3 * l - 0.7034186147 * m) + 1.707614701 * s;
    var bGamma = toGamma(b);
    return Hydrogen_Schema_Color_RGB.rgb(Data_Int.round(rGamma * 255.0))(Data_Int.round(gGamma * 255.0))(Data_Int.round(bGamma * 255.0));
};

// | OKLCH → RGB (convenience)
var oklchToRgb = function ($73) {
    return oklabToRgb(oklchToOklab($73));
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // oklab ↔ oklch
// ═══════════════════════════════════════════════════════════════════════════════
// | OKLAB → OKLCH (rectangular → cylindrical)
var oklabToOklch = function (oklab) {
    var sqrt = function (x) {
        return Hydrogen_Math_Core.sqrt(x);
    };
    var atan2 = function (y) {
        return function (x) {
            return Hydrogen_Math_Core.atan2(y)(x);
        };
    };
    var okL = Hydrogen_Schema_Color_OKLAB.unwrapOkL(Hydrogen_Schema_Color_OKLAB.okL(oklab));
    var okB = Hydrogen_Schema_Color_OKLAB.unwrapOkB(Hydrogen_Schema_Color_OKLAB.okB(oklab));
    var okA = Hydrogen_Schema_Color_OKLAB.unwrapOkA(Hydrogen_Schema_Color_OKLAB.okA(oklab));
    
    // Hue (angle in degrees)
var h = (atan2(okB)(okA) * 180.0) / Hydrogen_Math_Core.pi;
    var hNormalized = (function () {
        var $40 = h < 0.0;
        if ($40) {
            return h + 360.0;
        };
        return h;
    })();
    
    // Chroma (distance from neutral)
var c = sqrt(okA * okA + okB * okB);
    return Hydrogen_Schema_Color_OKLCH.oklch(okL)(c)(Data_Int.round(hNormalized));
};

// | RGB → OKLCH (convenience)
var rgbToOklch = function ($74) {
    return oklabToOklch(rgbToOklab($74));
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // helpers
// ═══════════════════════════════════════════════════════════════════════════════
// | Floating point modulo
var mod$prime = function (a) {
    return function (b) {
        return a - b * Data_Int.toNumber(Data_Int.floor(a / b));
    };
};

// | Convert RGB to HSL
// |
// | Uses standard RGB → HSL algorithm:
// | 1. Normalize RGB to 0-1 range
// | 2. Find min, max, delta
// | 3. Calculate hue, saturation, lightness
// |
// | ```purescript
// | rgbToHsl (RGB.rgb 255 0 0)   -- HSL(0°, 100%, 50%) - red
// | rgbToHsl (RGB.rgb 128 128 128) -- HSL(0°, 0%, 50%) - gray
// | ```
var rgbToHsl = function (rgb) {
    var r = Data_Int.toNumber(Hydrogen_Schema_Color_Channel.unwrap(Hydrogen_Schema_Color_RGB.red(rgb))) / 255.0;
    var g = Data_Int.toNumber(Hydrogen_Schema_Color_Channel.unwrap(Hydrogen_Schema_Color_RGB.green(rgb))) / 255.0;
    var b = Data_Int.toNumber(Hydrogen_Schema_Color_Channel.unwrap(Hydrogen_Schema_Color_RGB.blue(rgb))) / 255.0;
    var cmax = max(r)(max(g)(b));
    var cmin = min(r)(min(g)(b));
    var delta = cmax - cmin;
    
    // Calculate lightness
var l = (cmax + cmin) / 2.0;
    var lInt = Data_Int.round(l * 100.0);
    
    // Calculate saturation
var s = (function () {
        var $41 = delta === 0.0;
        if ($41) {
            return 0.0;
        };
        return delta / (1.0 - Data_Number.abs(2.0 * l - 1.0));
    })();
    var sInt = Data_Int.round(s * 100.0);
    
    // Calculate hue
var h$prime = (function () {
        var $42 = delta === 0.0;
        if ($42) {
            return 0.0;
        };
        var $43 = cmax === r;
        if ($43) {
            return mod$prime((g - b) / delta)(6.0);
        };
        var $44 = cmax === g;
        if ($44) {
            return (b - r) / delta + 2.0;
        };
        return (r - g) / delta + 4.0;
    })();
    var h = h$prime * 60.0;
    
    // Convert to integer percentages
var hInt = Data_Int.round((function () {
        var $45 = h < 0.0;
        if ($45) {
            return h + 360.0;
        };
        return h;
    })());
    return Hydrogen_Schema_Color_HSL.hsl(hInt)(sInt)(lInt);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // rgb ↔ hwb
// ═══════════════════════════════════════════════════════════════════════════════
// | RGB → HWB (via HSL)
var rgbToHwb = function (rgb) {
    var hsl = rgbToHsl(rgb);
    var l = Hydrogen_Schema_Color_Lightness.unwrap(Hydrogen_Schema_Color_HSL.lightness(hsl));
    var lNum = Data_Int.toNumber(l);
    var s = Hydrogen_Schema_Color_Saturation.unwrap(Hydrogen_Schema_Color_HSL.saturation(hsl));
    
    // Calculate whiteness and blackness from HSL
var sNum = Data_Int.toNumber(s);
    var w = ((100.0 - sNum) * lNum) / 100.0;
    var h = Hydrogen_Schema_Color_Hue.unwrap(Hydrogen_Schema_Color_HSL.hue(hsl));
    var b = 100.0 - lNum - (sNum * lNum) / 100.0;
    return Hydrogen_Schema_Color_HWB.hwb(h)(Data_Int.round(w))(Data_Int.round(b));
};

// | LCH → Record (for JSON serialization / backend persistence)
var lchToRecord = Hydrogen_Schema_Color_LCH.lchToRecord;

// | Record → LCH (from JSON deserialization / backend)
var lchFromRecord = Hydrogen_Schema_Color_LCH.lchFromRecord;

// | Convert LAB to XYZ (perceptual to device-independent)
// |
// | Inverse of xyzToLab.
// |
// | ```purescript
// | labToXyz (LAB.lab 100.0 0.0 0.0)  -- D65 white point
// | ```
var labToXyz = function (labColor) {
    
    // Inverse CIE LAB function (piecewise)
var labFInv = function (t) {
        var t3 = t * t * t;
        var $46 = t3 > 8.856e-3;
        if ($46) {
            return t3;
        };
        return (t - 16.0 / 116.0) / 7.787;
    };
    var rec = Hydrogen_Schema_Color_LAB.toRecord(labColor);
    
    // Calculate intermediate values
var fy = (rec.l + 16.0) / 116.0;
    var yr = labFInv(fy);
    var y = yr * 1.0;
    var fz = fy - rec.b / 200.0;
    var zr = labFInv(fz);
    var z = zr * 1.08883;
    var fx = rec.a / 500.0 + fy;
    
    // Apply inverse CIE LAB function
var xr = labFInv(fx);
    
    // Denormalize by D65 white point
var x = xr * 0.95047;
    return Hydrogen_Schema_Color_XYZ.xyz(x)(y)(z);
};

// | Convert LAB to RGB (convenience function)
// |
// | Goes through XYZ: LAB → XYZ → RGB
// |
// | ```purescript
// | labToRgb (LAB.lab 50.0 80.0 67.0)  -- Perceptual red to display RGB
// | ```
var labToRgb = function ($75) {
    return xyzToRgb(labToXyz($75));
};

// | Convert LCH to RGB (convenience function)
// |
// | Goes through LAB and XYZ: LCH → LAB → XYZ → RGB
// |
// | ```purescript
// | lchToRgb (LCH.lch 50.0 100.0 0.0)  -- Perceptual cylindrical to display RGB
// | ```
var lchToRgb = function ($76) {
    return labToRgb(Hydrogen_Schema_Color_LCH.lchToLab($76));
};

// | LAB → Record (for JSON serialization / backend persistence)
var labToRecord = Hydrogen_Schema_Color_LAB.labToRecord;

// | Record → LAB (from JSON deserialization / backend)
var labFromRecord = Hydrogen_Schema_Color_LAB.labFromRecord;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // kelvin → rgb
// ═══════════════════════════════════════════════════════════════════════════════
// | Convert Kelvin color temperature to RGB
// |
// | Re-export from Kelvin module for convenience.
// | Uses Tanner Helland's algorithm for accurate temperature conversion.
// |
// | ```purescript
// | kelvinToRgb (K.kelvin 2700)  -- Warm tungsten light
// | kelvinToRgb (K.kelvin 6500)  -- Cool daylight
// | ```
var kelvinToRgb = Hydrogen_Schema_Color_Kelvin.kelvinToRgb;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // hsl ↔ rgb
// ═══════════════════════════════════════════════════════════════════════════════
// | Convert HSL to RGB
// |
// | Uses standard HSL → RGB algorithm:
// | 1. Convert HSL percentages to 0-1 range
// | 2. Calculate chroma and intermediate values
// | 3. Map to RGB cube
// |
// | ```purescript
// | hslToRgb (HSL.hsl 0 100 50)     -- Pure red: RGB(255, 0, 0)
// | hslToRgb (HSL.hsl 120 100 50)   -- Pure green: RGB(0, 255, 0)
// | hslToRgb (HSL.hsl 240 100 50)   -- Pure blue: RGB(0, 0, 255)
// | ```
var hslToRgb = function (hsl) {
    var s = Data_Int.toNumber(Hydrogen_Schema_Color_Saturation.unwrap(Hydrogen_Schema_Color_HSL.saturation(hsl))) / 100.0;
    var l = Data_Int.toNumber(Hydrogen_Schema_Color_Lightness.unwrap(Hydrogen_Schema_Color_HSL.lightness(hsl))) / 100.0;
    var h = Data_Int.toNumber(Hydrogen_Schema_Color_Hue.unwrap(Hydrogen_Schema_Color_HSL.hue(hsl))) / 360.0;
    
    // Calculate chroma
var c = (1.0 - Data_Number.abs(2.0 * l - 1.0)) * s;
    var m = l - c / 2.0;
    var x = c * (1.0 - Data_Number.abs(mod$prime(h * 6.0)(2.0) - 1.0));
    var v = (function () {
        var $47 = h < 1.0 / 6.0;
        if ($47) {
            return {
                r: c,
                g: x,
                b: 0.0
            };
        };
        var $48 = h < 2.0 / 6.0;
        if ($48) {
            return {
                r: x,
                g: c,
                b: 0.0
            };
        };
        var $49 = h < 3.0 / 6.0;
        if ($49) {
            return {
                r: 0.0,
                g: c,
                b: x
            };
        };
        var $50 = h < 4.0 / 6.0;
        if ($50) {
            return {
                r: 0.0,
                g: x,
                b: c
            };
        };
        var $51 = h < 5.0 / 6.0;
        if ($51) {
            return {
                r: x,
                g: 0.0,
                b: c
            };
        };
        return {
            r: c,
            g: 0.0,
            b: x
        };
    })();
    
    // Convert to 0-255 range
var r = Data_Int.round((v.r + m) * 255.0);
    var g = Data_Int.round((v.g + m) * 255.0);
    var b = Data_Int.round((v.b + m) * 255.0);
    return Hydrogen_Schema_Color_RGB.rgb(r)(g)(b);
};

// | HWB → RGB (via HSL)
var hwbToRgb = function (hwb) {
    var min1 = function (a) {
        return function (b) {
            var $56 = a < b;
            if ($56) {
                return a;
            };
            return b;
        };
    };
    var w = Data_Int.toNumber(Hydrogen_Schema_Color_HWB.unwrapWhiteness(Hydrogen_Schema_Color_HWB.getWhiteness(hwb)));
    var h = Hydrogen_Schema_Color_Hue.unwrap(Hydrogen_Schema_Color_HWB.hue(hwb));
    var b = Data_Int.toNumber(Hydrogen_Schema_Color_HWB.unwrapBlackness(Hydrogen_Schema_Color_HWB.getBlackness(hwb)));
    
    // Normalize if w + b > 100
var total = w + b;
    var b$prime = (function () {
        var $57 = total > 100.0;
        if ($57) {
            return (b * 100.0) / total;
        };
        return b;
    })();
    var w$prime = (function () {
        var $58 = total > 100.0;
        if ($58) {
            return (w * 100.0) / total;
        };
        return w;
    })();
    
    // Convert to HSL
var l = 100.0 - b$prime - (100.0 - b$prime - w$prime) / 2.0;
    var s = (function () {
        var $59 = l === 0.0 || l === 100.0;
        if ($59) {
            return 0.0;
        };
        return ((100.0 - b$prime - l) * 100.0) / min1(l)(100.0 - l);
    })();
    return hslToRgb(Hydrogen_Schema_Color_HSL.hsl(h)(Data_Int.round(s))(Data_Int.round(l)));
};

// | HSL → Record (for JSON serialization / backend persistence)
var hslToRecord = Hydrogen_Schema_Color_HSL.hslToRecord;

// | Record → HSL (from JSON deserialization / backend)
var hslFromRecord = Hydrogen_Schema_Color_HSL.hslFromRecord;

// | Get numeric value of hex character
var hexValue = function (c) {
    if (c === "0") {
        return 0;
    };
    if (c === "1") {
        return 1;
    };
    if (c === "2") {
        return 2;
    };
    if (c === "3") {
        return 3;
    };
    if (c === "4") {
        return 4;
    };
    if (c === "5") {
        return 5;
    };
    if (c === "6") {
        return 6;
    };
    if (c === "7") {
        return 7;
    };
    if (c === "8") {
        return 8;
    };
    if (c === "9") {
        return 9;
    };
    if (c === "A") {
        return 10;
    };
    if (c === "B") {
        return 11;
    };
    if (c === "C") {
        return 12;
    };
    if (c === "D") {
        return 13;
    };
    if (c === "E") {
        return 14;
    };
    if (c === "F") {
        return 15;
    };
    if (c === "a") {
        return 10;
    };
    if (c === "b") {
        return 11;
    };
    if (c === "c") {
        return 12;
    };
    if (c === "d") {
        return 13;
    };
    if (c === "e") {
        return 14;
    };
    if (c === "f") {
        return 15;
    };
    return 0;
};

// | Convert digit to hex character
var hexDigit = function (n) {
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
        return "A";
    };
    if (n === 11) {
        return "B";
    };
    if (n === 12) {
        return "C";
    };
    if (n === 13) {
        return "D";
    };
    if (n === 14) {
        return "E";
    };
    if (n === 15) {
        return "F";
    };
    return "0";
};

// | Convert int to 2-character hex string
var toHex = function (n) {
    var lo = mod(n)(16);
    var hi = div1(n)(16);
    return hexDigit(hi) + hexDigit(lo);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // rgb ↔ hex
// ═══════════════════════════════════════════════════════════════════════════════
// | Convert RGB to hex string
// |
// | Returns 6-character hex string (no # prefix).
// | Agents can prepend # if needed for CSS/HTML contexts.
// |
// | ```purescript
// | rgbToHex (RGB.rgb 255 0 0)     -- "FF0000"
// | rgbToHex (RGB.rgb 128 128 128) -- "808080"
// | ```
var rgbToHex = function (rgb) {
    var r = Hydrogen_Schema_Color_Channel.unwrap(Hydrogen_Schema_Color_RGB.red(rgb));
    var g = Hydrogen_Schema_Color_Channel.unwrap(Hydrogen_Schema_Color_RGB.green(rgb));
    var b = Hydrogen_Schema_Color_Channel.unwrap(Hydrogen_Schema_Color_RGB.blue(rgb));
    return toHex(r) + (toHex(g) + toHex(b));
};

// | Parse 2-character hex string to int
var fromHex = function (str) {
    var v = Data_String_CodeUnits.toCharArray(str);
    if (v.length === 2) {
        return (hexValue(v[0]) * 16 | 0) + hexValue(v[1]) | 0;
    };
    if (v.length === 1) {
        return hexValue(v[0]);
    };
    return 0;
};

// | Convert hex string to RGB
// |
// | Accepts formats:
// | - "FF0000" (6 chars)
// | - "#FF0000" (7 chars with #)
// | - "F00" (3 chars, expands to FF0000)
// | - "#F00" (4 chars with #)
// |
// | Invalid hex returns black RGB(0, 0, 0).
// |
// | ```purescript
// | hexToRgb "FF0000"   -- RGB(255, 0, 0)
// | hexToRgb "#FF0000"  -- RGB(255, 0, 0)
// | hexToRgb "F00"      -- RGB(255, 0, 0)
// | hexToRgb "invalid"  -- RGB(0, 0, 0) - fallback
// | ```
var hexToRgb = function (hex) {
    
    // Strip # if present
var cleaned = (function () {
        var $66 = Data_String_CodePoints.take(1)(hex) === "#";
        if ($66) {
            return Data_String_CodePoints.drop(1)(hex);
        };
        return hex;
    })();
    
    // Expand 3-char format to 6-char
var expanded = (function () {
        var v = Data_String_CodeUnits.toCharArray(cleaned);
        if (v.length === 3) {
            return Data_String_CodeUnits.fromCharArray([ v[0], v[0], v[1], v[1], v[2], v[2] ]);
        };
        return cleaned;
    })();
    var g = fromHex(Data_String_CodePoints.take(2)(Data_String_CodePoints.drop(2)(expanded)));
    
    // Parse hex components
var r = fromHex(Data_String_CodePoints.take(2)(expanded));
    var b = fromHex(Data_String_CodePoints.take(2)(Data_String_CodePoints.drop(4)(expanded)));
    return Hydrogen_Schema_Color_RGB.rgb(r)(g)(b);
};

// | Convert CMYK to RGB (print to screen)
// |
// | Uses standard CMYK → RGB algorithm:
// | 1. R = 255 * (1 - C) * (1 - K)
// | 2. G = 255 * (1 - M) * (1 - K)
// | 3. B = 255 * (1 - Y) * (1 - K)
// |
// | ```purescript
// | cmykToRgb (CMYK.cmyk 0 100 100 0)  -- RGB(255, 0, 0) - red
// | cmykToRgb (CMYK.cmyk 0 0 0 100)    -- RGB(0, 0, 0) - black
// | ```
var cmykToRgb = function (cmyk) {
    var y = Data_Int.toNumber(Hydrogen_Schema_Color_Yellow.unwrap(Hydrogen_Schema_Color_CMYK.yellow(cmyk))) / 100.0;
    var m = Data_Int.toNumber(Hydrogen_Schema_Color_Magenta.unwrap(Hydrogen_Schema_Color_CMYK.magenta(cmyk))) / 100.0;
    var k = Data_Int.toNumber(Hydrogen_Schema_Color_Key.unwrap(Hydrogen_Schema_Color_CMYK.key(cmyk))) / 100.0;
    var g = Data_Int.round(255.0 * (1.0 - m) * (1.0 - k));
    var c = Data_Int.toNumber(Hydrogen_Schema_Color_Cyan.unwrap(Hydrogen_Schema_Color_CMYK.cyan(cmyk))) / 100.0;
    var r = Data_Int.round(255.0 * (1.0 - c) * (1.0 - k));
    var b = Data_Int.round(255.0 * (1.0 - y) * (1.0 - k));
    return Hydrogen_Schema_Color_RGB.rgb(r)(g)(b);
};

// | CMYK → Record (for JSON serialization / backend persistence)
var cmykToRecord = Hydrogen_Schema_Color_CMYK.cmykToRecord;

// | Record → CMYK (from JSON deserialization / backend)
var cmykFromRecord = Hydrogen_Schema_Color_CMYK.cmykFromRecord;
export {
    hslToRgb,
    rgbToHsl,
    rgbToCmyk,
    cmykToRgb,
    rgbToHex,
    hexToRgb,
    rgbToXyz,
    xyzToRgb,
    xyzToLab,
    labToXyz,
    rgbToLab,
    labToRgb,
    rgbToLch,
    lchToRgb,
    kelvinToRgb,
    rgbToOklab,
    oklabToRgb,
    oklabToOklch,
    oklchToOklab,
    rgbToOklch,
    oklchToRgb,
    rgbToHwb,
    hwbToRgb,
    rgbToYuv,
    yuvToRgb,
    rgbToRecord,
    rgbFromRecord,
    hslToRecord,
    hslFromRecord,
    cmykToRecord,
    cmykFromRecord,
    labToRecord,
    labFromRecord,
    lchToRecord,
    lchFromRecord,
    xyzToRecord,
    xyzFromRecord
};
