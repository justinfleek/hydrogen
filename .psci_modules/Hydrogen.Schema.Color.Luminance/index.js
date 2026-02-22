// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                    // hydrogen // schema // color // luminance
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Luminance - absolute light emission intensity.
// |
// | Measured in candelas per square meter (cd/m², also called "nits"):
// | - **0.0**: No light emission (black)
// | - **80-200**: Typical SDR displays
// | - **400-600**: Bright SDR displays
// | - **1,000+**: HDR content (HDR10 standard)
// | - **4,000+**: Peak HDR highlights
// | - **10,000+**: Ultra HDR displays
// |
// | ## vs Lightness
// |
// | - **Lightness (HSL)**: Perceptual - "how light/dark does this look?"
// | - **Luminance**: Physical - "how much light does this emit?"
// |
// | Luminance is for:
// | - Emissive UI elements (glowing buttons, neon text)
// | - HDR rendering (bloom effects, bright highlights)
// | - Light source definitions (how bright is this light?)
// | - Self-illuminating materials
// |
// | ## Use Cases
// |
// | - Glow effects (button with 200 nit glow)
// | - HDR content (sunset at 4000 nits peak)
// | - Light sources (LED panel at 500 nits)
// | - Emissive materials (neon sign at 1000 nits)
import * as Data_Int from "../Data.Int/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Hydrogen_Schema_Bounded from "../Hydrogen.Schema.Bounded/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showNumber);
var compare = /* #__PURE__ */ Data_Ord.compare(Data_Ord.ordNumber);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // luminance
// ═══════════════════════════════════════════════════════════════════════════════
// | Luminance value in nits (cd/m²)
// |
// | Represents absolute light emission intensity. 0 = no light, higher values
// | = brighter emission. Unbounded to support HDR (can exceed 10,000 nits).
var Luminance = function (x) {
    return x;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // accessors
// ═══════════════════════════════════════════════════════════════════════════════
// | Extract the raw Number value (nits)
var unwrap = function (v) {
    return v;
};

// | Create a luminance value without clamping
// |
// | Use only when you know the value is valid (>= 0.0).
var unsafeLuminance = Luminance;

// | Convert to Number (alias for unwrap)
var toNumber = unwrap;

// | Round to nearest integer nit
// |
// | Useful for display and serialization:
// | ```purescript
// | toInt (luminance 147.3)  -- 147
// | toInt (luminance 999.8)  -- 1000
// | ```
var toInt = function (v) {
    return Data_Int.round(v);
};
var showLuminance = {
    show: function (v) {
        return show(v) + " nits";
    }
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // constructors
// ═══════════════════════════════════════════════════════════════════════════════
// | Create a luminance value, clamping to >= 0.0
// |
// | Negative luminance is physically meaningless and is clamped to 0.
// | Upper bound is unbounded to support HDR.
// |
// | ```purescript
// | luminance 0.0      -- No emission (black)
// | luminance 100.0    -- Typical display
// | luminance 1000.0   -- HDR content
// | luminance (-50.0)  -- Clamped to 0.0
// | ```
var luminance = function (n) {
    return Hydrogen_Schema_Bounded.clampNumber(0.0)(100000.0)(n);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // operations
// ═══════════════════════════════════════════════════════════════════════════════
// | Scale luminance by a factor
// |
// | Useful for relative adjustments:
// | ```purescript
// | scale 2.0 (luminance 100.0)  -- Double brightness → 200 nits
// | scale 0.5 (luminance 100.0)  -- Half brightness → 50 nits
// | ```
var scale = function (factor) {
    return function (v) {
        return luminance(v * factor);
    };
};

// | Check if subtle glow (1-100 nits)
// |
// | Subtle glows: dim button highlights, ambient UI lighting
var isSubtle = function (v) {
    return v >= 1.0 && v <= 100.0;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // predicates
// ═══════════════════════════════════════════════════════════════════════════════
// | Check if luminance is effectively off (< 1.0 nit)
// |
// | Useful for optimization - non-emissive surfaces don't need glow rendering.
var isOff = function (v) {
    return v < 1.0;
};

// | Check if HDR range (> 1000 nits)
// |
// | HDR content: peak highlights, sun reflections, neon signs, explosions
var isHDR = function (v) {
    return v > 1000.0;
};

// | Check if bright (100-1000 nits)
// |
// | Bright emissions: prominent buttons, active elements, LED indicators
var isBright = function (v) {
    return v > 100.0 && v <= 1000.0;
};

// | Increase luminance by amount
// |
// | ```purescript
// | increase 50.0 (luminance 100.0)  -- 150 nits
// | ```
var increase = function (amount) {
    return function (v) {
        return luminance(v + amount);
    };
};

// | Create luminance from integer nit value
// |
// | Common in display specifications and UI:
// | ```purescript
// | fromInt 100   -- 100 nits (typical display)
// | fromInt 1000  -- 1000 nits (HDR)
// | ```
var fromInt = function (n) {
    return luminance(Data_Int.toNumber(n));
};
var eqLuminance = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordLuminance = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqLuminance;
    }
};

// | Decrease luminance by amount
// |
// | ```purescript
// | decrease 50.0 (luminance 100.0)  -- 50 nits
// | ```
var decrease = function (amount) {
    return function (v) {
        return luminance(v - amount);
    };
};

// | Bounds documentation for this type
var bounds = /* #__PURE__ */ Hydrogen_Schema_Bounded.numberBounds(0.0)(100000.0)("luminance")("Light emission intensity in nits (cd/m\xb2)");
export {
    luminance,
    fromInt,
    unsafeLuminance,
    unwrap,
    toInt,
    toNumber,
    scale,
    increase,
    decrease,
    bounds,
    isOff,
    isSubtle,
    isBright,
    isHDR,
    eqLuminance,
    ordLuminance,
    showLuminance
};
