// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                               // hydrogen // schema // color
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Color pillar - complete color science foundation for autonomous agents.
// |
// | **ATOMIC COMPOSITION ARCHITECTURE:**
// | Built from atoms → molecules → compounds for zero ambiguity at billion-agent scale.
// |
// | ## Color Spaces (all bidirectionally convertible)
// |
// | **Device-dependent (display colors):**
// | - **RGB** - Red, Green, Blue (0-255 per channel) - sRGB display colors
// | - **HSL** - Hue (0-360°), Saturation (0-100%), Lightness (0-100%) - intuitive color wheel
// | - **CMYK** - Cyan, Magenta, Yellow, Key/Black (0-100% ink) - print colors
// |
// | **Device-independent (bridging space):**
// | - **XYZ** - CIE 1931 tristimulus values - the mathematical bridge between all spaces
// |
// | **Perceptually uniform (accurate "10% lighter" operations):**
// | - **LAB** - L*a*b* perceptual color space - industry standard for color math
// | - **LCH** - L*C*h° cylindrical LAB - perceptually correct color wheel
// |
// | **Specialized:**
// | - **Kelvin** - Color temperature (1000-40000K) - warm/cool light
// | - **Hex** - Web colors (#FF0000) - human-readable codes
// |
// | ## Accessibility (8% males, 0.5% females affected)
// |
// | - **CVD** - Color Vision Deficiency simulation for all types (Protanopia, Deuteranopia, etc.)
// | - **Contrast** - WCAG compliance checking with deltaE calculations
// | - **Accurate prevalence data** - cited from authoritative sources (NEI, Colour Blind Awareness)
// |
// | ## Compositing & Effects
// |
// | - **BlendMode** - 36 blend modes (Photoshop/After Effects parity, trade dress compliant)
// | - **Glow** - Atomic glow effects (color + intensity + spread)
// |
// | ## Professional Color Grading
// |
// | - **WhiteBalance** - Temperature + tint correction with presets (Daylight, Tungsten, etc.)
// | - **ColorWheels** - Lift/Gamma/Gain for shadows/midtones/highlights
// |
// | ## Design Tools
// |
// | - **Harmony** - Color wheel relationships (complementary, triadic, analogous, etc.)
// | - **Palette** - Systematic palette generation (tints, shades, tones, semantic roles)
// | - **Conversion** - Bidirectional sync for color picker integration
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Schema.Color as Color
// |
// | -- RGB color
// | primary = Color.rgb 59 130 246
// |
// | -- Serialize for backend
// | json = Color.rgbToRecord primary
// |
// | -- Deserialize from backend
// | color = Color.rgbFromRecord { r: 59, g: 130, b: 246 }
// |
// | -- Convert to perceptually uniform space
// | lab = Color.rgbToLab primary
// | ```
import * as Hydrogen_Schema_Color_Blend from "../Hydrogen.Schema.Color.Blend/index.js";
import * as Hydrogen_Schema_Color_CMYK from "../Hydrogen.Schema.Color.CMYK/index.js";
import * as Hydrogen_Schema_Color_CVD from "../Hydrogen.Schema.Color.CVD/index.js";
import * as Hydrogen_Schema_Color_ColorWheels from "../Hydrogen.Schema.Color.ColorWheels/index.js";
import * as Hydrogen_Schema_Color_Contrast from "../Hydrogen.Schema.Color.Contrast/index.js";
import * as Hydrogen_Schema_Color_Conversion from "../Hydrogen.Schema.Color.Conversion/index.js";
import * as Hydrogen_Schema_Color_Glow from "../Hydrogen.Schema.Color.Glow/index.js";
import * as Hydrogen_Schema_Color_HSL from "../Hydrogen.Schema.Color.HSL/index.js";
import * as Hydrogen_Schema_Color_Harmony from "../Hydrogen.Schema.Color.Harmony/index.js";
import * as Hydrogen_Schema_Color_LAB from "../Hydrogen.Schema.Color.LAB/index.js";
import * as Hydrogen_Schema_Color_LCH from "../Hydrogen.Schema.Color.LCH/index.js";
import * as Hydrogen_Schema_Color_Mood from "../Hydrogen.Schema.Color.Mood/index.js";
import * as Hydrogen_Schema_Color_Properties from "../Hydrogen.Schema.Color.Properties/index.js";
import * as Hydrogen_Schema_Color_RGB from "../Hydrogen.Schema.Color.RGB/index.js";
import * as Hydrogen_Schema_Color_Temperature from "../Hydrogen.Schema.Color.Temperature/index.js";
import * as Hydrogen_Schema_Color_WhiteBalance from "../Hydrogen.Schema.Color.WhiteBalance/index.js";
import * as Hydrogen_Schema_Color_XYZ from "../Hydrogen.Schema.Color.XYZ/index.js";
var zComponent = Hydrogen_Schema_Color_XYZ.zComponent;
var yellow = Hydrogen_Schema_Color_CMYK.yellow;
var yComponent = Hydrogen_Schema_Color_XYZ.yComponent;
var xyzToRgb = Hydrogen_Schema_Color_Conversion.xyzToRgb;
var xyzToRecord = Hydrogen_Schema_Color_Conversion.xyzToRecord;
var xyzToLab = Hydrogen_Schema_Color_Conversion.xyzToLab;
var xyzFromRecord = Hydrogen_Schema_Color_Conversion.xyzFromRecord;
var xyz = Hydrogen_Schema_Color_XYZ.xyz;
var xComponent = Hydrogen_Schema_Color_XYZ.xComponent;
var withTint = Hydrogen_Schema_Color_WhiteBalance.withTint;
var withTemperature = Hydrogen_Schema_Color_WhiteBalance.withTemperature;
var withSpread = Hydrogen_Schema_Color_Glow.withSpread;
var withLift = Hydrogen_Schema_Color_ColorWheels.withLift;
var withIntensity = Hydrogen_Schema_Color_Glow.withIntensity;
var withGamma = Hydrogen_Schema_Color_ColorWheels.withGamma;
var withGain = Hydrogen_Schema_Color_ColorWheels.withGain;
var withColor = Hydrogen_Schema_Color_Glow.withColor;
var whiteBalanceApplyToRgb = Hydrogen_Schema_Color_WhiteBalance.applyToRgb;
var whiteBalance = Hydrogen_Schema_Color_WhiteBalance.whiteBalance;
var wheelAdjustment = Hydrogen_Schema_Color_ColorWheels.wheelAdjustment;
var warmGlow = Hydrogen_Schema_Color_Glow.warmGlow;
var value = Hydrogen_Schema_Color_Properties.value;
var toRGBA = Hydrogen_Schema_Color_RGB.toRGBA;
var toHex = Hydrogen_Schema_Color_RGB.toHex;
var toCssA = Hydrogen_Schema_Color_RGB.toCssA;
var toCss = Hydrogen_Schema_Color_RGB.toCss;
var tint = Hydrogen_Schema_Color_WhiteBalance.tint;
var temperatureFromHSL = Hydrogen_Schema_Color_Temperature.temperatureFromHSL;
var temperature = Hydrogen_Schema_Color_WhiteBalance.temperature;
var suggestForeground = Hydrogen_Schema_Color_Contrast.suggestForeground;
var suggestAccessibleAlternative = Hydrogen_Schema_Color_CVD.suggestAccessibleAlternative;
var simulateCVD = Hydrogen_Schema_Color_CVD.simulateCVD;
var screen = Hydrogen_Schema_Color_RGB.screen;
var saturation = Hydrogen_Schema_Color_HSL.saturation;
var rgba = Hydrogen_Schema_Color_RGB.rgba;
var rgbToXyz = Hydrogen_Schema_Color_Conversion.rgbToXyz;
var rgbToRecord = Hydrogen_Schema_Color_Conversion.rgbToRecord;
var rgbToLch = Hydrogen_Schema_Color_Conversion.rgbToLch;
var rgbToLab = Hydrogen_Schema_Color_Conversion.rgbToLab;
var rgbToHsl = Hydrogen_Schema_Color_Conversion.rgbToHsl;
var rgbToHex = Hydrogen_Schema_Color_Conversion.rgbToHex;
var rgbToCmyk = Hydrogen_Schema_Color_Conversion.rgbToCmyk;
var rgbFromRecord = Hydrogen_Schema_Color_Conversion.rgbFromRecord;
var rgb = Hydrogen_Schema_Color_RGB.rgb;
var relativeLuminance = Hydrogen_Schema_Color_Contrast.relativeLuminance;
var red = Hydrogen_Schema_Color_RGB.red;
var perceivedLightness = Hydrogen_Schema_Color_Properties.perceivedLightness;
var neutralWheels = Hydrogen_Schema_Color_ColorWheels.neutralWheels;
var neutralGlow = Hydrogen_Schema_Color_Glow.neutralGlow;
var neutralAdjustment = Hydrogen_Schema_Color_ColorWheels.neutralAdjustment;
var multiply = Hydrogen_Schema_Color_RGB.multiply;
var moodFromHSL = Hydrogen_Schema_Color_Mood.moodFromHSL;
var moodDescription = Hydrogen_Schema_Color_Mood.moodDescription;
var mixRGBA = Hydrogen_Schema_Color_Blend.mixRGBA;
var mixRGB = Hydrogen_Schema_Color_Blend.mixRGB;
var meetsWCAG = Hydrogen_Schema_Color_Contrast.meetsWCAG;
var magenta = Hydrogen_Schema_Color_CMYK.magenta;
var luminanceRGB = Hydrogen_Schema_Color_Contrast.luminanceRGB;
var lightness = Hydrogen_Schema_Color_HSL.lightness;
var lift = Hydrogen_Schema_Color_ColorWheels.lift;
var lerpRGB = Hydrogen_Schema_Color_Blend.lerpRGB;
var lchToRgb = Hydrogen_Schema_Color_Conversion.lchToRgb;
var lchToRecord = Hydrogen_Schema_Color_Conversion.lchToRecord;
var lchL = Hydrogen_Schema_Color_LCH.lchL;
var lchH = Hydrogen_Schema_Color_LCH.lchH;
var lchFromRecord = Hydrogen_Schema_Color_Conversion.lchFromRecord;
var lchC = Hydrogen_Schema_Color_LCH.lchC;
var lch = Hydrogen_Schema_Color_LCH.lch;
var labToXyz = Hydrogen_Schema_Color_Conversion.labToXyz;
var labToRgb = Hydrogen_Schema_Color_Conversion.labToRgb;
var labToRecord = Hydrogen_Schema_Color_Conversion.labToRecord;
var labLightness = Hydrogen_Schema_Color_Properties.labLightness;
var labL = Hydrogen_Schema_Color_LAB.labL;
var labFromRecord = Hydrogen_Schema_Color_Conversion.labFromRecord;
var labB = Hydrogen_Schema_Color_LAB.labB;
var labA = Hydrogen_Schema_Color_LAB.labA;
var lab = Hydrogen_Schema_Color_LAB.lab;
var key = Hydrogen_Schema_Color_CMYK.key;
var kelvinToRgb = Hydrogen_Schema_Color_Conversion.kelvinToRgb;
var kelvin = Hydrogen_Schema_Color_Temperature.kelvin;
var isDistinguishable = Hydrogen_Schema_Color_CVD.isDistinguishable;
var invert = Hydrogen_Schema_Color_RGB.invert;
var hue = Hydrogen_Schema_Color_HSL.hue;

// Conversions
var hslToRgb = Hydrogen_Schema_Color_Conversion.hslToRgb;
var hslToRecord = Hydrogen_Schema_Color_Conversion.hslToRecord;
var hslFromRecord = Hydrogen_Schema_Color_Conversion.hslFromRecord;
var hsl = Hydrogen_Schema_Color_HSL.hsl;
var hexToRgb = Hydrogen_Schema_Color_Conversion.hexToRgb;
var green = Hydrogen_Schema_Color_RGB.green;
var glowToRgb = Hydrogen_Schema_Color_Glow.glowToRgb;
var glowToRecord = Hydrogen_Schema_Color_Glow.glowToRecord;
var glowToCss = Hydrogen_Schema_Color_Glow.glowToCss;
var glowSpread = Hydrogen_Schema_Color_Glow.glowSpread;
var glowIntensity = Hydrogen_Schema_Color_Glow.glowIntensity;
var glowFromRecord = Hydrogen_Schema_Color_Glow.glowFromRecord;
var glowColor = Hydrogen_Schema_Color_Glow.glowColor;
var glow = Hydrogen_Schema_Color_Glow.glow;
var generateHarmony = Hydrogen_Schema_Color_Harmony.generateHarmony;
var gamma = Hydrogen_Schema_Color_ColorWheels.gamma;
var gain = Hydrogen_Schema_Color_ColorWheels.gain;
var fromRGBA = Hydrogen_Schema_Color_RGB.fromRGBA;
var fromPreset = Hydrogen_Schema_Color_WhiteBalance.fromPreset;
var fromComponents = Hydrogen_Schema_Color_HSL.fromComponents;
var fromChannels = Hydrogen_Schema_Color_RGB.fromChannels;
var ensureAccessible = Hydrogen_Schema_Color_CVD.ensureAccessible;
var deltaE = Hydrogen_Schema_Color_LAB.deltaE;
var d65White = Hydrogen_Schema_Color_XYZ.d65White;
var cyan = Hydrogen_Schema_Color_CMYK.cyan;
var cvdSafeContrast = Hydrogen_Schema_Color_CVD.cvdSafeContrast;
var cvdPrevalence = Hydrogen_Schema_Color_CVD.cvdPrevalence;
var coolGlow = Hydrogen_Schema_Color_Glow.coolGlow;
var contrastRatio = Hydrogen_Schema_Color_Contrast.contrastRatio;
var contrastBetween = Hydrogen_Schema_Color_Contrast.contrastBetween;
var compositeOpToCss = Hydrogen_Schema_Color_Blend.compositeOpToCss;
var composite = Hydrogen_Schema_Color_Blend.composite;

// Properties
var colorfulness = Hydrogen_Schema_Color_Properties.colorfulness;
var colorWheelsApplyToRgb = Hydrogen_Schema_Color_ColorWheels.applyToRgb;
var colorWheels = Hydrogen_Schema_Color_ColorWheels.colorWheels;
var cmykToRgb = Hydrogen_Schema_Color_Conversion.cmykToRgb;
var cmykToRecord = Hydrogen_Schema_Color_Conversion.cmykToRecord;
var cmykToCss = Hydrogen_Schema_Color_CMYK.cmykToCss;
var cmykFromRecord = Hydrogen_Schema_Color_Conversion.cmykFromRecord;
var cmykFromComponents = Hydrogen_Schema_Color_CMYK.cmykFromComponents;
var cmyk = Hydrogen_Schema_Color_CMYK.cmyk;
var chroma = Hydrogen_Schema_Color_Properties.chroma;
var checkAccessibility = Hydrogen_Schema_Color_CVD.checkAccessibility;
var brightness = Hydrogen_Schema_Color_Properties.brightness;
var blue = Hydrogen_Schema_Color_RGB.blue;
var blendRGBA = Hydrogen_Schema_Color_Blend.blendRGBA;
var blendModeToCss = Hydrogen_Schema_Color_Blend.blendModeToCss;
var blendChannel = Hydrogen_Schema_Color_Blend.blendChannel;
var blend = Hydrogen_Schema_Color_RGB.blend;
var alpha = Hydrogen_Schema_Color_RGB.alpha;
var add = Hydrogen_Schema_Color_RGB.add;
export {
    rgb,
    rgba,
    fromChannels,
    red,
    green,
    blue,
    alpha,
    invert,
    blend,
    add,
    multiply,
    screen,
    toCss,
    toHex,
    toCssA,
    toRGBA,
    fromRGBA,
    hsl,
    fromComponents,
    hue,
    saturation,
    lightness,
    cmyk,
    cmykFromComponents,
    cyan,
    magenta,
    yellow,
    key,
    cmykToCss,
    lab,
    labL,
    labA,
    labB,
    deltaE,
    lch,
    lchL,
    lchC,
    lchH,
    xyz,
    xComponent,
    yComponent,
    zComponent,
    d65White,
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
    xyzFromRecord,
    blendRGBA,
    blendChannel,
    composite,
    mixRGB,
    mixRGBA,
    lerpRGB,
    blendModeToCss,
    compositeOpToCss,
    glow,
    glowFromRecord,
    glowColor,
    glowIntensity,
    glowSpread,
    glowToRecord,
    glowToRgb,
    glowToCss,
    withColor,
    withIntensity,
    withSpread,
    warmGlow,
    coolGlow,
    neutralGlow,
    cvdPrevalence,
    simulateCVD,
    isDistinguishable,
    checkAccessibility,
    suggestAccessibleAlternative,
    ensureAccessible,
    cvdSafeContrast,
    contrastRatio,
    contrastBetween,
    meetsWCAG,
    suggestForeground,
    luminanceRGB,
    relativeLuminance,
    generateHarmony,
    colorfulness,
    chroma,
    brightness,
    value,
    perceivedLightness,
    labLightness,
    temperatureFromHSL,
    kelvin,
    moodFromHSL,
    moodDescription,
    whiteBalance,
    fromPreset,
    temperature,
    tint,
    whiteBalanceApplyToRgb,
    withTemperature,
    withTint,
    colorWheels,
    neutralWheels,
    wheelAdjustment,
    neutralAdjustment,
    lift,
    gamma,
    gain,
    colorWheelsApplyToRgb,
    withLift,
    withGamma,
    withGain
};
