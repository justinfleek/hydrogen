// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                         // hydrogen // schema // color // lch
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | LCH - CIE L*C*h° perceptually uniform color space (cylindrical LAB).
// |
// | **WHY LCH?**
// | LCH is LAB expressed in cylindrical coordinates, like HSL but perceptually
// | uniform. This makes it easier to:
// | - Adjust saturation (chroma) independently
// | - Rotate hue while maintaining perceptual correctness
// | - Create harmonious palettes with accurate color relationships
// |
// | **Components:**
// | - **L*** (Lightness): 0 (black) to 100 (white) - same as LAB
// | - **C*** (Chroma): 0 (gray) to ~230 (most saturated), unbounded
// | - **h°** (Hue): 0-360 degrees on perceptual color wheel
// |
// | **Advantage over HSL:**
// | HSL's "saturation" and "lightness" are NOT perceptually uniform.
// | LCH's "chroma" and "lightness" ARE perceptually uniform.
// |
// | **Use cases:**
// | - Color wheel with accurate perceptual distances
// | - "More saturated" operations that actually look more saturated
// | - Hue rotation that preserves perceived brightness
// | - Professional color grading
import * as Data_Boolean from "../Data.Boolean/index.js";
import * as Data_EuclideanRing from "../Data.EuclideanRing/index.js";
import * as Data_Number from "../Data.Number/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Hydrogen_Schema_Color_LAB from "../Hydrogen.Schema.Color.LAB/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showNumber);
var mod = /* #__PURE__ */ Data_EuclideanRing.mod(Data_EuclideanRing.euclideanRingNumber);
var compare = /* #__PURE__ */ Data_Ord.compare(Data_Ord.ordNumber);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // atoms
// ═══════════════════════════════════════════════════════════════════════════════
// | L* component (Lightness): 0-100 (same as LAB)
var LchL = function (x) {
    return x;
};

// | h° component (Hue): 0-360 degrees (wraps)
var LchH = function (x) {
    return x;
};

// | C* component (Chroma/Saturation): 0+ (unbounded, but typically 0-230)
var LchC = function (x) {
    return x;
};
var unwrapLchL = function (v) {
    return v;
};
var unwrapLchH = function (v) {
    return v;
};
var unwrapLchC = function (v) {
    return v;
};
var showLchL = {
    show: function (v) {
        return "LchL " + show(v);
    }
};
var showLchH = {
    show: function (v) {
        return "LchH " + show(v);
    }
};
var showLchC = {
    show: function (v) {
        return "LchC " + show(v);
    }
};

// | Convert to record - explicitly named for backend persistence
var lchToRecord = function (color) {
    return {
        l: unwrapLchL(color.l),
        c: unwrapLchC(color.c),
        h: unwrapLchH(color.h)
    };
};

// | Generic alias for lchToRecord
var toRecord = lchToRecord;

// | Convert LCH to LAB (cylindrical to rectangular)
// |
// | ```purescript
// | lchToLab lchColor  -- Convert back to LAB for other operations
// | ```
var lchToLab = function (lchColor) {
    var l = unwrapLchL(lchColor.l);
    var h = unwrapLchH(lchColor.h);
    
    // Convert hue to radians
var hRad = (h * Data_Number.pi) / 180.0;
    var c = unwrapLchC(lchColor.c);
    var b = c * Data_Number.sin(hRad);
    
    // Calculate a* and b* from polar coordinates
var a = c * Data_Number.cos(hRad);
    return Hydrogen_Schema_Color_LAB.lab(l)(a)(b);
};
var lchLValue = function (n) {
    if (n < 0.0) {
        return 0.0;
    };
    if (n > 100.0) {
        return 100.0;
    };
    if (Data_Boolean.otherwise) {
        return n;
    };
    throw new Error("Failed pattern match at Hydrogen.Schema.Color.LCH (line 77, column 1 - line 77, column 28): " + [ n.constructor.name ]);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // accessors
// ═══════════════════════════════════════════════════════════════════════════════
// | Get L* (lightness) component
var lchL = function (color) {
    return color.l;
};
var lchHValue = function (n) {
    var floor$prime = function (x) {
        var i = x - mod(x)(1.0);
        var $56 = x < 0.0 && i !== x;
        if ($56) {
            return i - 1.0;
        };
        return i;
    };
    var mod$prime = function (a) {
        return function (b) {
            return a - b * floor$prime(a / b);
        };
    };
    return mod$prime(n)(360.0);
};

// | Rotate hue by degrees
// |
// | ```purescript
// | rotateHue 180.0 color  -- Complementary color (perceptually accurate)
// | rotateHue 120.0 color  -- Triadic relationship
// | ```
var rotateHue = function (degrees) {
    return function (color) {
        var h = unwrapLchH(color.h);
        var h$prime = h + degrees;
        return {
            l: color.l,
            c: color.c,
            h: lchHValue(h$prime)
        };
    };
};

// | Get h° (hue) component
var lchH = function (color) {
    return color.h;
};
var lchCValue = function (n) {
    if (n < 0.0) {
        return 0.0;
    };
    if (Data_Boolean.otherwise) {
        return n;
    };
    throw new Error("Failed pattern match at Hydrogen.Schema.Color.LCH (line 95, column 1 - line 95, column 28): " + [ n.constructor.name ]);
};

// | Get C* (chroma) component
var lchC = function (color) {
    return color.c;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // constructors
// ═══════════════════════════════════════════════════════════════════════════════
// | Create LCH color from components
// |
// | ```purescript
// | lch 50.0 50.0 0.0    -- Red-ish
// | lch 50.0 0.0 0.0     -- Gray (no chroma)
// | lch 100.0 0.0 0.0    -- White
// | ```
var lch = function (l) {
    return function (c) {
        return function (h) {
            return {
                l: lchLValue(l),
                c: lchCValue(c),
                h: lchHValue(h)
            };
        };
    };
};

// | Create from record
var lchFromRecord = function (v) {
    return lch(v.l)(v.c)(v.h);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // conversion
// ═══════════════════════════════════════════════════════════════════════════════
// | Convert LAB to LCH (rectangular to cylindrical)
// |
// | ```purescript
// | labToLch labColor  -- Convert to cylindrical for easier hue manipulation
// | ```
var labToLch = function (labColor) {
    var rec = Hydrogen_Schema_Color_LAB.toRecord(labColor);
    
    // Calculate chroma (distance from gray axis)
var c = Data_Number.sqrt(rec.a * rec.a + rec.b * rec.b);
    
    // Calculate hue angle (degrees)
    // atan2 returns radians, convert to degrees
var hRad = Data_Number.atan2(rec.b)(rec.a);
    var hDeg = (hRad * 180.0) / Data_Number.pi;
    
    // Normalize to 0-360
var h = (function () {
        var $62 = hDeg < 0.0;
        if ($62) {
            return hDeg + 360.0;
        };
        return hDeg;
    })();
    return lch(rec.l)(c)(h);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // operations
// ═══════════════════════════════════════════════════════════════════════════════
// ═══════════════════════════════════════════════════════════════════════════════
//                                       // operations // perceptually // uniform
// ═══════════════════════════════════════════════════════════════════════════════
// | Increase LCH L* (luminance) by percentage - PERCEPTUALLY UNIFORM.
// |
// | Same as LAB.increaseLuminance but operates directly on cylindrical LCH.
// |
// | **Semantically explicit:** `increaseLuminance` distinguishes from HSL.increaseLightness.
// |
// | ```purescript
// | increaseLuminance 10.0 color  -- Actually looks 10% lighter (perceptual)
// | ```
var increaseLuminance = function (percent) {
    return function (color) {
        var l = unwrapLchL(color.l);
        var l$prime = l + percent;
        return {
            c: color.c,
            h: color.h,
            l: lchLValue(l$prime)
        };
    };
};

// | Increase LCH C (chroma) by percentage - PERCEPTUALLY UNIFORM.
// |
// | **Chroma vs Saturation:** LCH C is perceptually uniform chroma, distinct from
// | HSL saturation. Use this for accurate "20% more vivid" operations.
// |
// | **Semantically explicit:** `increaseChroma` distinguishes from HSL.increaseSaturation.
// |
// | ```purescript
// | increaseChroma 20.0 color  -- 20% more vivid (perceptually accurate)
// | ```
var increaseChroma = function (percent) {
    return function (color) {
        var c = unwrapLchC(color.c);
        var c$prime = c * (1.0 + percent / 100.0);
        return {
            l: color.l,
            h: color.h,
            c: lchCValue(c$prime)
        };
    };
};
var eqLchL = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordLchL = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqLchL;
    }
};
var eqLchH = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordLchH = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqLchH;
    }
};
var eqLchC = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordLchC = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqLchC;
    }
};

// | Decrease LCH L* (luminance) by percentage - PERCEPTUALLY UNIFORM.
// |
// | ```purescript
// | decreaseLuminance 10.0 color  -- Actually looks 10% darker (perceptual)
// | ```
var decreaseLuminance = function (percent) {
    return function (color) {
        var l = unwrapLchL(color.l);
        var l$prime = l - percent;
        return {
            c: color.c,
            h: color.h,
            l: lchLValue(l$prime)
        };
    };
};

// | Decrease LCH C (chroma) by percentage - PERCEPTUALLY UNIFORM.
// |
// | ```purescript
// | decreaseChroma 20.0 color  -- 20% less vivid (perceptually accurate)
// | ```
var decreaseChroma = function (percent) {
    return function (color) {
        var c = unwrapLchC(color.c);
        var c$prime = c * (1.0 - percent / 100.0);
        return {
            l: color.l,
            h: color.h,
            c: lchCValue(c$prime)
        };
    };
};
export {
    lch,
    lchFromRecord,
    lchL,
    lchC,
    lchH,
    lchToRecord,
    toRecord,
    increaseLuminance,
    decreaseLuminance,
    increaseChroma,
    decreaseChroma,
    rotateHue,
    labToLch,
    lchToLab,
    eqLchL,
    ordLchL,
    showLchL,
    eqLchC,
    ordLchC,
    showLchC,
    eqLchH,
    ordLchH,
    showLchH
};
