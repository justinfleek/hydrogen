// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                         // hydrogen // schema // color // lab
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | LAB - CIE L*a*b* perceptually uniform color space.
// |
// | **PERCEPTUAL UNIFORMITY:**
// | Unlike HSL, LAB is designed so that equal distances in the color space
// | correspond to equal perceptual differences. This means:
// | - "10% lighter" actually LOOKS 10% lighter
// | - Color math matches human vision
// | - Gradients appear smooth and natural
// |
// | **Components:**
// | - **L*** (Lightness): 0 (black) to 100 (white)
// | - **a***: Green (negative) to Red (positive), typically -128 to +127
// | - **b***: Blue (negative) to Yellow (positive), typically -128 to +127
// |
// | **Use cases:**
// | - Accurate "lighter/darker" operations
// | - Perceptually uniform gradients
// | - Color difference calculations (ΔE)
// | - Professional color grading
// | - Autonomous palette generation
// |
// | **Conversion note:**
// | LAB uses D65 white point (standard for sRGB displays).
// | Conversion path: RGB → XYZ → LAB
import * as Data_Boolean from "../Data.Boolean/index.js";
import * as Data_Number from "../Data.Number/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Show from "../Data.Show/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showNumber);
var compare = /* #__PURE__ */ Data_Ord.compare(Data_Ord.ordNumber);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // atoms
// ═══════════════════════════════════════════════════════════════════════════════
// | L* component (Lightness): 0-100
var LabL = function (x) {
    return x;
};

// | b* component (Blue-Yellow axis): unbounded, typically -128 to +127
var LabB = function (x) {
    return x;
};

// | a* component (Green-Red axis): unbounded, typically -128 to +127
var LabA = function (x) {
    return x;
};
var unwrapLabL = function (v) {
    return v;
};
var unwrapLabB = function (v) {
    return v;
};
var unwrapLabA = function (v) {
    return v;
};
var showLabL = {
    show: function (v) {
        return "LabL " + show(v);
    }
};
var showLabB = {
    show: function (v) {
        return "LabB " + show(v);
    }
};
var showLabA = {
    show: function (v) {
        return "LabA " + show(v);
    }
};

// | Convert to record - explicitly named for backend persistence
var labToRecord = function (c) {
    return {
        l: unwrapLabL(c.l),
        a: unwrapLabA(c.a),
        b: unwrapLabB(c.b)
    };
};

// | Generic alias for labToRecord
var toRecord = labToRecord;

// | Create L* value (clamped 0-100)
var labLValue = function (n) {
    if (n < 0.0) {
        return 0.0;
    };
    if (n > 100.0) {
        return 100.0;
    };
    if (Data_Boolean.otherwise) {
        return n;
    };
    throw new Error("Failed pattern match at Hydrogen.Schema.Color.LAB (line 72, column 1 - line 72, column 28): " + [ n.constructor.name ]);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // accessors
// ═══════════════════════════════════════════════════════════════════════════════
// | Get L* (lightness) component
var labL = function (c) {
    return c.l;
};

// | Create b* value (unbounded, but clamped for practical range)
var labBValue = function (n) {
    if (n < -128.0) {
        return -128.0;
    };
    if (n > 127.0) {
        return 127.0;
    };
    if (Data_Boolean.otherwise) {
        return n;
    };
    throw new Error("Failed pattern match at Hydrogen.Schema.Color.LAB (line 110, column 1 - line 110, column 28): " + [ n.constructor.name ]);
};

// | Get b* (blue-yellow) component  
var labB = function (c) {
    return c.b;
};

// | Create a* value (unbounded, but clamped for practical range)
var labAValue = function (n) {
    if (n < -128.0) {
        return -128.0;
    };
    if (n > 127.0) {
        return 127.0;
    };
    if (Data_Boolean.otherwise) {
        return n;
    };
    throw new Error("Failed pattern match at Hydrogen.Schema.Color.LAB (line 91, column 1 - line 91, column 28): " + [ n.constructor.name ]);
};

// | Get a* (green-red) component
var labA = function (c) {
    return c.a;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // constructors
// ═══════════════════════════════════════════════════════════════════════════════
// | Create LAB color from components
// |
// | ```purescript
// | lab 50.0 0.0 0.0      -- Mid gray
// | lab 100.0 0.0 0.0     -- White
// | lab 50.0 80.0 67.0    -- Red-ish
// | ```
var lab = function (l) {
    return function (a) {
        return function (b) {
            return {
                l: labLValue(l),
                a: labAValue(a),
                b: labBValue(b)
            };
        };
    };
};

// | Create from record
var labFromRecord = function (v) {
    return lab(v.l)(v.a)(v.b);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // operations
// ═══════════════════════════════════════════════════════════════════════════════
// | Lighten by percentage (perceptually accurate)
// |
// ═══════════════════════════════════════════════════════════════════════════════
//                                       // operations // perceptually // uniform
// ═══════════════════════════════════════════════════════════════════════════════
// | Increase LAB L* (luminance) by percentage - PERCEPTUALLY UNIFORM.
// |
// | Unlike HSL.increaseLightness, this produces consistent perceived brightness changes.
// | Adding 10 to L* actually looks 10% lighter to the human eye.
// |
// | **Semantically explicit:** `increaseLuminance` makes clear this operates on L* (luminance),
// | not HSL lightness. Critical for billion-agent disambiguation.
// |
// | ```purescript
// | increaseLuminance 10.0 color  -- Actually looks 10% lighter (perceptual)
// | ```
var increaseLuminance = function (percent) {
    return function (color) {
        var l = unwrapLabL(color.l);
        var l$prime = l + percent;
        return {
            a: color.a,
            b: color.b,
            l: labLValue(l$prime)
        };
    };
};
var eqLabL = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordLabL = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqLabL;
    }
};
var eqLabB = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordLabB = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqLabB;
    }
};
var eqLabA = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordLabA = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqLabA;
    }
};

// | Calculate color difference (ΔE - Delta E)
// |
// | Returns perceptual distance between two colors:
// | - 0: Identical colors
// | - < 1: Imperceptible difference
// | - 1-2: Just noticeable difference
// | - 2-10: Perceptible at a glance
// | - 11-49: Colors are more similar than opposite
// | - 100: Maximum difference (black to white)
// |
// | Uses CIE76 formula: ΔE = √[(L2-L1)² + (a2-a1)² + (b2-b1)²]
// |
// | ```purescript
// | deltaE color1 color2  -- How different are these colors?
// | ```
var deltaE = function (c1) {
    return function (c2) {
        var l2 = unwrapLabL(c2.l);
        var l1 = unwrapLabL(c1.l);
        var dL = l2 - l1;
        var b2 = unwrapLabB(c2.b);
        var b1 = unwrapLabB(c1.b);
        var dB = b2 - b1;
        var a2 = unwrapLabA(c2.a);
        var a1 = unwrapLabA(c1.a);
        var dA = a2 - a1;
        return Data_Number.sqrt(dL * dL + dA * dA + dB * dB);
    };
};

// | Decrease LAB L* (luminance) by percentage - PERCEPTUALLY UNIFORM.
// |
// | Unlike HSL.decreaseLightness, this produces consistent perceived brightness changes.
// | Subtracting 10 from L* actually looks 10% darker to the human eye.
// |
// | ```purescript
// | decreaseLuminance 10.0 color  -- Actually looks 10% darker (perceptual)
// | ```
var decreaseLuminance = function (percent) {
    return function (color) {
        var l = unwrapLabL(color.l);
        var l$prime = l - percent;
        return {
            a: color.a,
            b: color.b,
            l: labLValue(l$prime)
        };
    };
};
export {
    lab,
    labFromRecord,
    labL,
    labA,
    labB,
    labToRecord,
    toRecord,
    increaseLuminance,
    decreaseLuminance,
    deltaE,
    eqLabL,
    ordLabL,
    showLabL,
    eqLabA,
    ordLabA,
    showLabA,
    eqLabB,
    ordLabB,
    showLabB
};
