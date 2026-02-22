// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                  // hydrogen // schema // color // color wheels
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | ColorWheels - Lift/Gamma/Gain color grading (shadows/midtones/highlights).
// |
// | **PROFESSIONAL COLOR GRADING:**
// | The three-wheel color grading system used in DaVinci Resolve, Premiere Pro,
// | and professional color grading applications.
// |
// | **Three tonal ranges:**
// | - **Lift** (Blacks/Shadows): Affects darkest areas, minimal impact on highlights
// | - **Gamma** (Midtones): Affects middle tones, preserves blacks and whites
// | - **Gain** (Whites/Highlights): Affects brightest areas, minimal impact on shadows
// |
// | **Each wheel controls:**
// | - Color shift (hue rotation on color picker wheel)
// | - Intensity (distance from center = amount of color added)
// | - Luminance (master brightness control for that tonal range)
// |
// | **Common use cases:**
// | - Warm shadows, cool highlights (cinematic look)
// | - Teal shadows, orange midtones (blockbuster style)
// | - Correct color cast in specific tonal ranges
// | - Create mood through selective color
// |
// | **Integration:**
// | Part of ColorGrading compound - applied after WhiteBalance, before Curves.
import * as Data_Boolean from "../Data.Boolean/index.js";
import * as Data_Int from "../Data.Int/index.js";
import * as Data_Number from "../Data.Number/index.js";
import * as Hydrogen_Schema_Color_Channel from "../Hydrogen.Schema.Color.Channel/index.js";
import * as Hydrogen_Schema_Color_RGB from "../Hydrogen.Schema.Color.RGB/index.js";

// | Update lift (shadows) adjustment
var withLift = function (newLift) {
    return function (wheels) {
        return {
            gamma: wheels.gamma,
            gain: wheels.gain,
            lift: newLift
        };
    };
};

// | Update gamma (midtones) adjustment
var withGamma = function (newGamma) {
    return function (wheels) {
        return {
            lift: wheels.lift,
            gain: wheels.gain,
            gamma: newGamma
        };
    };
};

// | Update gain (highlights) adjustment
var withGain = function (newGain) {
    return function (wheels) {
        return {
            lift: wheels.lift,
            gamma: wheels.gamma,
            gain: newGain
        };
    };
};

// | Create wheel adjustment
// |
// | ```purescript
// | wheelAdjustment 30.0 0.3 0.1  -- Orange tint, moderate intensity, slightly brighter
// | wheelAdjustment 200.0 0.5 0.0 -- Cyan tint, strong intensity, neutral brightness
// | ```
var wheelAdjustment = function (angle) {
    return function (intensity) {
        return function (lum) {
            var normalizeAngle = function (a) {
                return a - Data_Int.toNumber(Data_Int.floor(a / 360.0)) * 360.0;
            };
            var clamp = function (min$prime) {
                return function (max$prime) {
                    return function (val) {
                        if (val < min$prime) {
                            return min$prime;
                        };
                        if (val > max$prime) {
                            return max$prime;
                        };
                        if (Data_Boolean.otherwise) {
                            return val;
                        };
                        throw new Error("Failed pattern match at Hydrogen.Schema.Color.ColorWheels (line 83, column 5 - line 86, column 24): " + [ min$prime.constructor.name, max$prime.constructor.name, val.constructor.name ]);
                    };
                };
            };
            return {
                angle: normalizeAngle(angle),
                intensity: clamp(0.0)(1.0)(intensity),
                luminance: clamp(-1.0)(1.0)(lum)
            };
        };
    };
};

// | Neutral adjustment (no color shift)
var neutralAdjustment = /* #__PURE__ */ wheelAdjustment(0.0)(0.0)(0.0);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // accessors
// ═══════════════════════════════════════════════════════════════════════════════
// | Get lift (shadows) adjustment
var lift = function (wheels) {
    return wheels.lift;
};

// | Get gamma (midtones) adjustment
var gamma = function (wheels) {
    return wheels.gamma;
};

// | Get gain (highlights) adjustment
var gain = function (wheels) {
    return wheels.gain;
};

// | Create color wheels grading
// |
// | ```purescript
// | colorWheels liftAdj gammaAdj gainAdj
// | ```
var colorWheels = function (liftAdj) {
    return function (gammaAdj) {
        return function (gainAdj) {
            return {
                lift: liftAdj,
                gamma: gammaAdj,
                gain: gainAdj
            };
        };
    };
};

// | Neutral color wheels (no grading applied)
var neutralWheels = /* #__PURE__ */ colorWheels(neutralAdjustment)(neutralAdjustment)(neutralAdjustment);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // operations
// ═══════════════════════════════════════════════════════════════════════════════
// | Apply color wheels grading to RGB color
// |
// | **Algorithm:**
// | 1. Calculate luminance to determine tonal range weights
// | 2. Apply lift, gamma, gain based on luminance
// | 3. Blend color shifts proportionally to tonal range
// |
// | ```purescript
// | applyToRgb wheels rgbColor
// | ```
var applyToRgb = function (wheels) {
    return function (rgb) {
        var clamp = function (min$prime) {
            return function (max$prime) {
                return function (val) {
                    if (val < min$prime) {
                        return min$prime;
                    };
                    if (val > max$prime) {
                        return max$prime;
                    };
                    if (Data_Boolean.otherwise) {
                        return val;
                    };
                    throw new Error("Failed pattern match at Hydrogen.Schema.Color.ColorWheels (line 203, column 5 - line 206, column 24): " + [ min$prime.constructor.name, max$prime.constructor.name, val.constructor.name ]);
                };
            };
        };
        
        // Apply single wheel adjustment to a channel value
var applyWheel = function (adj) {
            return function (val) {
                return function (weight) {
                    
                    // Apply luminance shift
var lumShift = adj.luminance * weight;
                    
                    // Convert angle to RGB shift
var angleRad = (adj.angle * Data_Number.pi) / 180.0;
                    var blueShift = Data_Number.sin(angleRad) * adj.intensity * weight;
                    var redShift = Data_Number.cos(angleRad) * adj.intensity * weight;
                    
                    // Combined adjustment (blend both color axes with luminance)
var result = val + lumShift + redShift * 0.5 + blueShift * 0.5;
                    return result;
                };
            };
        };
        var r = Data_Int.toNumber(Hydrogen_Schema_Color_Channel.unwrap(Hydrogen_Schema_Color_RGB.red(rgb))) / 255.0;
        var g = Data_Int.toNumber(Hydrogen_Schema_Color_Channel.unwrap(Hydrogen_Schema_Color_RGB.green(rgb))) / 255.0;
        var b = Data_Int.toNumber(Hydrogen_Schema_Color_Channel.unwrap(Hydrogen_Schema_Color_RGB.blue(rgb))) / 255.0;
        
        // Calculate relative luminance
var luma = 0.2126 * r + 0.7152 * g + 7.22e-2 * b;
        var gainWeight = luma * luma;
        
        // Calculate tonal range weights (sum to 1.0)
        // Lift affects shadows (low luma)
        // Gamma affects midtones (mid luma)
        // Gain affects highlights (high luma)
var liftWeight = (1.0 - luma) * (1.0 - luma);
        var bLift = applyWheel(wheels.lift)(b)(liftWeight);
        var gLift = applyWheel(wheels.lift)(g)(liftWeight);
        var gammaWeight = 1.0 - liftWeight - gainWeight;
        var bGamma = applyWheel(wheels.gamma)(bLift)(gammaWeight);
        var bGain = applyWheel(wheels.gain)(bGamma)(gainWeight);
        var bFinal = Data_Int.round(clamp(0.0)(1.0)(bGain) * 255.0);
        var gGamma = applyWheel(wheels.gamma)(gLift)(gammaWeight);
        var gGain = applyWheel(wheels.gain)(gGamma)(gainWeight);
        var gFinal = Data_Int.round(clamp(0.0)(1.0)(gGain) * 255.0);
        
        // Apply each wheel with its weight
var rLift = applyWheel(wheels.lift)(r)(liftWeight);
        var rGamma = applyWheel(wheels.gamma)(rLift)(gammaWeight);
        var rGain = applyWheel(wheels.gain)(rGamma)(gainWeight);
        
        // Clamp and convert to 0-255
var rFinal = Data_Int.round(clamp(0.0)(1.0)(rGain) * 255.0);
        return Hydrogen_Schema_Color_RGB.rgb(rFinal)(gFinal)(bFinal);
    };
};
export {
    colorWheels,
    neutralWheels,
    wheelAdjustment,
    neutralAdjustment,
    lift,
    gamma,
    gain,
    applyToRgb,
    withLift,
    withGamma,
    withGain
};
