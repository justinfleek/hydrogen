// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                    // hydrogen // schema // color // properties
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Color properties - measurable characteristics.
// |
// | Perceptual properties for color analysis:
// | - **Colorfulness**: How vivid/chromatic a color appears
// | - **Brightness**: Simple average RGB brightness
// | - **Perceived Lightness**: L* from CIELAB (perceptually uniform)
import * as Data_Int from "../Data.Int/index.js";
import * as Hydrogen_Math_Core from "../Hydrogen.Math.Core/index.js";
import * as Hydrogen_Schema_Color_Channel from "../Hydrogen.Schema.Color.Channel/index.js";
import * as Hydrogen_Schema_Color_Contrast from "../Hydrogen.Schema.Color.Contrast/index.js";
import * as Hydrogen_Schema_Color_HSL from "../Hydrogen.Schema.Color.HSL/index.js";
import * as Hydrogen_Schema_Color_Lightness from "../Hydrogen.Schema.Color.Lightness/index.js";
import * as Hydrogen_Schema_Color_RGB from "../Hydrogen.Schema.Color.RGB/index.js";
import * as Hydrogen_Schema_Color_Saturation from "../Hydrogen.Schema.Color.Saturation/index.js";

// | HSV Value (maximum of RGB channels)
// |
// | The "V" in HSV color space.
var value = function (color) {
    var r = Hydrogen_Schema_Color_Channel.unwrap(Hydrogen_Schema_Color_RGB.red(color));
    var g = Hydrogen_Schema_Color_Channel.unwrap(Hydrogen_Schema_Color_RGB.green(color));
    var b = Hydrogen_Schema_Color_Channel.unwrap(Hydrogen_Schema_Color_RGB.blue(color));
    return Hydrogen_Math_Core.max(Hydrogen_Math_Core.max(Data_Int.toNumber(r))(Data_Int.toNumber(g)))(Data_Int.toNumber(b)) / 255.0;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // perceived lightness
// ═══════════════════════════════════════════════════════════════════════════════
// | Perceived lightness (L* from CIELAB)
// |
// | This is perceptually uniform: a change of 10 L* units looks like
// | the same lightness difference regardless of the starting point.
// |
// | Returns 0-100 range.
var perceivedLightness = function (color) {
    var y = Hydrogen_Schema_Color_Contrast.luminanceRGB(color);
    var $5 = y > 8.856e-3;
    if ($5) {
        return 116.0 * Hydrogen_Math_Core.cbrt(y) - 16.0;
    };
    return 903.3 * y;
};

// | Alias for perceivedLightness (CIELAB terminology)
var labLightness = perceivedLightness;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // colorfulness
// ═══════════════════════════════════════════════════════════════════════════════
// | Perceived colorfulness (chroma relative to lightness)
// |
// | A measure of how vivid a color appears. Highly saturated colors
// | at mid-lightness have maximum colorfulness.
var colorfulness = function (color) {
    var s = Hydrogen_Schema_Color_Saturation.unwrap(Hydrogen_Schema_Color_HSL.saturation(color));
    var l = Hydrogen_Schema_Color_Lightness.unwrap(Hydrogen_Schema_Color_HSL.lightness(color));
    return Data_Int.toNumber(s) * (1.0 - Hydrogen_Math_Core.abs(Data_Int.toNumber(l) / 50.0 - 1.0));
};

// | Chroma - saturation normalized to 0-1 range
var chroma = function (color) {
    var s = Hydrogen_Schema_Color_Saturation.unwrap(Hydrogen_Schema_Color_HSL.saturation(color));
    return Data_Int.toNumber(s) / 100.0;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // brightness
// ═══════════════════════════════════════════════════════════════════════════════
// | Simple brightness (average of RGB channels)
// |
// | Returns 0-1 range. This is a naive measure; use perceivedLightness
// | for perceptually accurate results.
var brightness = function (color) {
    var r = Hydrogen_Schema_Color_Channel.unwrap(Hydrogen_Schema_Color_RGB.red(color));
    var g = Hydrogen_Schema_Color_Channel.unwrap(Hydrogen_Schema_Color_RGB.green(color));
    var b = Hydrogen_Schema_Color_Channel.unwrap(Hydrogen_Schema_Color_RGB.blue(color));
    return Data_Int.toNumber((r + g | 0) + b | 0) / 3.0 / 255.0;
};
export {
    colorfulness,
    chroma,
    brightness,
    value,
    perceivedLightness,
    labLightness
};
