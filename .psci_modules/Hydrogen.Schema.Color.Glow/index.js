// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                          // hydrogen // schema // color // glow
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Glow - compound for emissive light effects.
// |
// | **ATOMIC COMPOSITION DESIGN:**
// | Glow is a single, static effect. For complex effects, compose:
// | - **Gradient glow**: `Array Glow` with positions (Geometry pillar)
// | - **Animated glow**: `Animation Glow` with keyframes (Temporal pillar)
// | - **Multi-layer glow**: `Array Glow` for inner + outer effects
// |
// | Glow combines color temperature, intensity, and spread:
// | - **glowColor**: Warm to cool (Kelvin)
// | - **glowIntensity**: Subtle to intense (Luminance in nits)
// | - **glowSpread**: Blur radius in pixels (>= 0, Gaussian sigma)
// |
// | ## Spread Semantics
// |
// | Spread is Gaussian blur sigma in CSS pixels:
// | - `0` = no blur, hard edge
// | - `5` = tight halo
// | - `20` = soft diffuse glow
// | - `50+` = very diffuse, bloom-like
// |
// | Renders as CSS `filter: drop-shadow(0 0 {spread}px {color})`
// | or WebGL Gaussian blur with sigma = spread.
// |
// | ## Use Cases
// |
// | - Button hover states with warm glow
// | - Neon text effects
// | - Active UI element highlights
// | - Emissive materials in 3D
// | - HDR bloom effects
// |
// | ## Playground Integration
// |
// | The visual studio presents sliders:
// | - \"Glow Color\" (warm tungsten to cool daylight)
// | - \"Glow Intensity\" (off to intense HDR)
// | - \"Glow Spread\" (tight halo to soft diffuse)
// |
// | These map to physically accurate Kelvin/Luminance values internally.
import * as Data_Boolean from "../Data.Boolean/index.js";
import * as Data_Int from "../Data.Int/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Hydrogen_Schema_Color_Channel from "../Hydrogen.Schema.Color.Channel/index.js";
import * as Hydrogen_Schema_Color_Kelvin from "../Hydrogen.Schema.Color.Kelvin/index.js";
import * as Hydrogen_Schema_Color_Luminance from "../Hydrogen.Schema.Color.Luminance/index.js";
import * as Hydrogen_Schema_Color_RGB from "../Hydrogen.Schema.Color.RGB/index.js";
var min = /* #__PURE__ */ Data_Ord.min(Data_Ord.ordNumber);
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showNumber);

// | Update glow spread
var withSpread = function (s) {
    return function (g) {
        return {
            glowColor: g.glowColor,
            glowIntensity: g.glowIntensity,
            glowSpread: s
        };
    };
};

// | Update glow intensity
var withIntensity = function (l) {
    return function (g) {
        return {
            glowColor: g.glowColor,
            glowSpread: g.glowSpread,
            glowIntensity: l
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // operations
// ═══════════════════════════════════════════════════════════════════════════════
// | Update glow color temperature
var withColor = function (k) {
    return function (g) {
        return {
            glowIntensity: g.glowIntensity,
            glowSpread: g.glowSpread,
            glowColor: k
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // predicates
// ═══════════════════════════════════════════════════════════════════════════════
// | Check if glow is effectively off (intensity < 1 nit)
var isOff = function (g) {
    return Hydrogen_Schema_Color_Luminance.isOff(g.glowIntensity);
};

// | Convert glow color temperature to RGB
// |
// | Returns the RGB color that agents should render for the glow.
// | Luminance and spread are separate - this only converts the Kelvin color.
// |
// | ```purescript
// | glowToRgb warmGlow  -- RGB approximation of 2700K
// | ```
var glowToRgb = function (g) {
    return Hydrogen_Schema_Color_Kelvin.kelvinToRgb(g.glowColor);
};

// | Convert to record for serialization
var glowToRecord = function (g) {
    return {
        color: Hydrogen_Schema_Color_Kelvin.unwrap(g.glowColor),
        intensity: Hydrogen_Schema_Color_Luminance.unwrap(g.glowIntensity),
        spread: g.glowSpread
    };
};

// | Convert to CSS drop-shadow filter
// |
// | Renders as `filter: drop-shadow(0 0 {spread}px rgba({r}, {g}, {b}, {alpha}))`
// | where alpha is derived from luminance intensity.
// |
// | **Alpha calculation:**
// | - 0-100 nits: alpha 0.0-0.3 (subtle)
// | - 100-500 nits: alpha 0.3-0.7 (visible)
// | - 500+ nits: alpha 0.7-1.0 (intense)
// |
// | ```purescript
// | glowToCss myGlow  -- "drop-shadow(0 0 20px rgba(255, 200, 150, 0.6))"
// | ```
var glowToCss = function (g) {
    var rgb = glowToRgb(g);
    var r = Data_Int.toNumber(Hydrogen_Schema_Color_Channel.unwrap(Hydrogen_Schema_Color_RGB.red(rgb)));
    var intensity = Hydrogen_Schema_Color_Luminance.unwrap(g.glowIntensity);
    var gv = Data_Int.toNumber(Hydrogen_Schema_Color_Channel.unwrap(Hydrogen_Schema_Color_RGB.green(rgb)));
    var b = Data_Int.toNumber(Hydrogen_Schema_Color_Channel.unwrap(Hydrogen_Schema_Color_RGB.blue(rgb)));
    
    // Map luminance (nits) to CSS alpha
    // 0-100 nits: 0.0-0.3
    // 100-500 nits: 0.3-0.7
    // 500-2000 nits: 0.7-1.0
var alpha = (function () {
        var $16 = intensity < 100.0;
        if ($16) {
            return (intensity / 100.0) * 0.3;
        };
        var $17 = intensity < 500.0;
        if ($17) {
            return 0.3 + ((intensity - 100.0) / 400.0) * 0.4;
        };
        return 0.7 + min((intensity - 500.0) / 1500.0)(1.0) * 0.3;
    })();
    return "drop-shadow(0 0 " + (show(g.glowSpread) + ("px rgba(" + (show(r) + (", " + (show(gv) + (", " + (show(b) + (", " + (show(alpha) + "))")))))))));
};

// | Get the glow spread
var glowSpread = function (g) {
    return g.glowSpread;
};

// | Get the glow intensity
var glowIntensity = function (g) {
    return g.glowIntensity;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // accessors
// ═══════════════════════════════════════════════════════════════════════════════
// | Get the glow color temperature
var glowColor = function (g) {
    return g.glowColor;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // constructors
// ═══════════════════════════════════════════════════════════════════════════════
// | Create a glow effect from raw values
// |
// | Spread is clamped to >= 0 (negative blur is nonsensical).
// | Spread must be finite (no Infinity or NaN).
// |
// | ```purescript
// | glow 3000 200 20   -- Warm glow, 200 nits, 20px spread
// | glow 6500 100 10   -- Cool glow, 100 nits, 10px spread
// | glow 2700 50 (-5)  -- Negative spread clamped to 0
// | ```
var glow = function (kelvinVal) {
    return function (luminanceVal) {
        return function (spreadVal) {
            var $$isFinite = function (n) {
                return !(n !== n) && (n !== 1.0 / 0.0 && n !== -1.0 / 0.0);
            };
            var clampSpread = function (s) {
                if (s < 0.0) {
                    return 0.0;
                };
                if (!$$isFinite(s)) {
                    return 0.0;
                };
                if (Data_Boolean.otherwise) {
                    return s;
                };
                throw new Error("Failed pattern match at Hydrogen.Schema.Color.Glow (line 111, column 5 - line 114, column 22): " + [ s.constructor.name ]);
            };
            return {
                glowColor: Hydrogen_Schema_Color_Kelvin.kelvin(kelvinVal),
                glowIntensity: Hydrogen_Schema_Color_Luminance.luminance(luminanceVal),
                glowSpread: clampSpread(spreadVal)
            };
        };
    };
};

// | Create from a record
var glowFromRecord = function (v) {
    return glow(v.color)(v.intensity)(v.spread);
};

// | Intense glow (1000 nits, 30px spread)
var intense = function (k) {
    return glow(Hydrogen_Schema_Color_Kelvin.unwrap(k))(1000.0)(30.0);
};

// | Neutral glow preset (neutral white ~4000K)
var neutralGlow = function (intensity) {
    return function (spread) {
        return glow(4000)(intensity)(spread);
    };
};

// | Subtle glow (50 nits, 10px spread)
var subtle = function (k) {
    return glow(Hydrogen_Schema_Color_Kelvin.unwrap(k))(50.0)(10.0);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // presets
// ═══════════════════════════════════════════════════════════════════════════════
// | Warm glow preset (tungsten ~2700K)
var warmGlow = function (intensity) {
    return function (spread) {
        return glow(2700)(intensity)(spread);
    };
};

// | Cool glow preset (daylight ~6500K)
var coolGlow = function (intensity) {
    return function (spread) {
        return glow(6500)(intensity)(spread);
    };
};

// | Bright glow (200 nits, 20px spread)
var bright = function (k) {
    return glow(Hydrogen_Schema_Color_Kelvin.unwrap(k))(200.0)(20.0);
};
export {
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
    subtle,
    bright,
    intense,
    isOff
};
