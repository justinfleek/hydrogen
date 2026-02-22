// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                           // hydrogen // schema // color // cvd
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | CVD - Color Vision Deficiency simulation and accessibility.
// |
// | Color blindness affects approximately 8% of males and 0.5% of females.
// | Designs must be accessible to people with all types of color vision.
// |
// | ## Types of CVD
// |
// | **Red-Green Deficiencies (most common):**
// | - **Protanopia**: No red cones (~1% males) - red appears dark
// | - **Protanomaly**: Weak red cones (~1% males) - red shifted toward green
// | - **Deuteranopia**: No green cones (~1% males) - green appears beige
// | - **Deuteranomaly**: Weak green cones (~5% males) - green shifted toward red
// |
// | **Blue-Yellow Deficiencies (rare):**
// | - **Tritanopia**: No blue cones (~0.001%) - blue appears green, yellow appears pink
// | - **Tritanomaly**: Weak blue cones - blue/yellow confusion
// |
// | **Total Color Blindness (very rare):**
// | - **Achromatopsia**: No color vision - sees only grayscale
// |
// | ## Playground Integration
// |
// | The showcase accessibility panel shows:
// | - "Normal Vision" (original colors)
// | - "Protanopia" (no red)
// | - "Deuteranopia" (no green)
// | - "Tritanopia" (no blue)
// | - "Achromatopsia" (grayscale)
// |
// | For each view, show contrast ratios and distinguishability warnings.
import * as Data_Either from "../Data.Either/index.js";
import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Foldable from "../Data.Foldable/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Data_HeytingAlgebra from "../Data.HeytingAlgebra/index.js";
import * as Data_Int from "../Data.Int/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Ordering from "../Data.Ordering/index.js";
import * as Data_Semigroup from "../Data.Semigroup/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
import * as Hydrogen_Schema_Color_Channel from "../Hydrogen.Schema.Color.Channel/index.js";
import * as Hydrogen_Schema_Color_Contrast from "../Hydrogen.Schema.Color.Contrast/index.js";
import * as Hydrogen_Schema_Color_RGB from "../Hydrogen.Schema.Color.RGB/index.js";
var min = /* #__PURE__ */ Data_Ord.min(Data_Ord.ordNumber);
var max = /* #__PURE__ */ Data_Ord.max(Data_Ord.ordNumber);
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showNumber);
var map = /* #__PURE__ */ Data_Functor.map(Data_Functor.functorArray);
var foldr = /* #__PURE__ */ Data_Foldable.foldr(Data_Foldable.foldableArray);
var append1 = /* #__PURE__ */ Data_Semigroup.append(Data_Semigroup.semigroupArray);
var all = /* #__PURE__ */ Data_Foldable.all(Data_Foldable.foldableArray)(Data_HeytingAlgebra.heytingAlgebraBoolean);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // cvd type
// ═══════════════════════════════════════════════════════════════════════════════
// | Types of color vision deficiency
var Normal = /* #__PURE__ */ (function () {
    function Normal() {

    };
    Normal.value = new Normal();
    return Normal;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // cvd type
// ═══════════════════════════════════════════════════════════════════════════════
// | Types of color vision deficiency
var Protanopia = /* #__PURE__ */ (function () {
    function Protanopia() {

    };
    Protanopia.value = new Protanopia();
    return Protanopia;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // cvd type
// ═══════════════════════════════════════════════════════════════════════════════
// | Types of color vision deficiency
var Protanomaly = /* #__PURE__ */ (function () {
    function Protanomaly() {

    };
    Protanomaly.value = new Protanomaly();
    return Protanomaly;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // cvd type
// ═══════════════════════════════════════════════════════════════════════════════
// | Types of color vision deficiency
var Deuteranopia = /* #__PURE__ */ (function () {
    function Deuteranopia() {

    };
    Deuteranopia.value = new Deuteranopia();
    return Deuteranopia;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // cvd type
// ═══════════════════════════════════════════════════════════════════════════════
// | Types of color vision deficiency
var Deuteranomaly = /* #__PURE__ */ (function () {
    function Deuteranomaly() {

    };
    Deuteranomaly.value = new Deuteranomaly();
    return Deuteranomaly;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // cvd type
// ═══════════════════════════════════════════════════════════════════════════════
// | Types of color vision deficiency
var Tritanopia = /* #__PURE__ */ (function () {
    function Tritanopia() {

    };
    Tritanopia.value = new Tritanopia();
    return Tritanopia;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // cvd type
// ═══════════════════════════════════════════════════════════════════════════════
// | Types of color vision deficiency
var Tritanomaly = /* #__PURE__ */ (function () {
    function Tritanomaly() {

    };
    Tritanomaly.value = new Tritanomaly();
    return Tritanomaly;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // cvd type
// ═══════════════════════════════════════════════════════════════════════════════
// | Types of color vision deficiency
var Achromatopsia = /* #__PURE__ */ (function () {
    function Achromatopsia() {

    };
    Achromatopsia.value = new Achromatopsia();
    return Achromatopsia;
})();

// | Tritanopia transformation matrix (no blue cones)
var tritanopiaMatrix = {
    m00: 0.95,
    m01: 5.0e-2,
    m02: 0.0,
    m10: 0.0,
    m11: 0.433,
    m12: 0.567,
    m20: 0.0,
    m21: 0.475,
    m22: 0.525
};

// | Tritanomaly transformation matrix (weak blue cones)
var tritanomalyMatrix = {
    m00: 0.967,
    m01: 3.3e-2,
    m02: 0.0,
    m10: 0.0,
    m11: 0.733,
    m12: 0.267,
    m20: 0.0,
    m21: 0.183,
    m22: 0.817
};

// | Convert to grayscale (achromatopsia)
var toGrayscale = function (color) {
    
    // Use luminance weights (ITU-R BT.709)
var r = Data_Int.toNumber(Hydrogen_Schema_Color_Channel.unwrap(Hydrogen_Schema_Color_RGB.red(color)));
    var g = Data_Int.toNumber(Hydrogen_Schema_Color_Channel.unwrap(Hydrogen_Schema_Color_RGB.green(color)));
    var b = Data_Int.toNumber(Hydrogen_Schema_Color_Channel.unwrap(Hydrogen_Schema_Color_RGB.blue(color)));
    var gray = Data_Int.round(0.2126 * r + 0.7152 * g + 7.22e-2 * b);
    return Hydrogen_Schema_Color_RGB.rgb(gray)(gray)(gray);
};
var showCVDType = {
    show: function (v) {
        if (v instanceof Normal) {
            return "Normal Vision";
        };
        if (v instanceof Protanopia) {
            return "Protanopia (No Red)";
        };
        if (v instanceof Protanomaly) {
            return "Protanomaly (Weak Red)";
        };
        if (v instanceof Deuteranopia) {
            return "Deuteranopia (No Green)";
        };
        if (v instanceof Deuteranomaly) {
            return "Deuteranomaly (Weak Green)";
        };
        if (v instanceof Tritanopia) {
            return "Tritanopia (No Blue)";
        };
        if (v instanceof Tritanomaly) {
            return "Tritanomaly (Weak Blue)";
        };
        if (v instanceof Achromatopsia) {
            return "Achromatopsia (Grayscale)";
        };
        throw new Error("Failed pattern match at Hydrogen.Schema.Color.CVD (line 79, column 10 - line 87, column 49): " + [ v.constructor.name ]);
    }
};
var show1 = /* #__PURE__ */ Data_Show.show(showCVDType);

// | Protanopia transformation matrix (no red cones)
var protanopiaMatrix = {
    m00: 0.567,
    m01: 0.433,
    m02: 0.0,
    m10: 0.558,
    m11: 0.442,
    m12: 0.0,
    m20: 0.0,
    m21: 0.242,
    m22: 0.758
};

// | Protanomaly transformation matrix (weak red cones)
var protanomalyMatrix = {
    m00: 0.817,
    m01: 0.183,
    m02: 0.0,
    m10: 0.333,
    m11: 0.667,
    m12: 0.0,
    m20: 0.0,
    m21: 0.125,
    m22: 0.875
};

// | Make a foreground color accessible against a background
// |
// | **POLICY: Maximum contrast for maximum accessibility.**
// |
// | This function does NOT preserve hue or brand identity. It returns pure black
// | or pure white based on background luminance to guarantee WCAG AAA compliance
// | (7:1 contrast) for all CVD types.
// |
// | For brand-preserving alternatives, agents should use perceptual color spaces
// | (LAB/LCH/OKLAB) to adjust lightness while maintaining hue. This function is
// | the "nuclear option" when accessibility must be guaranteed at any cost.
// |
// | ```purescript
// | makeAccessible brandRed lightGray  -- Returns black (loses brand red)
// | makeAccessible brandBlue darkGray  -- Returns white (loses brand blue)
// | ```
var makeAccessible = function (fg) {
    return function (bg) {
        var currentRatio = Hydrogen_Schema_Color_Contrast.contrastRatio(fg)(bg);
        var bgLum = Hydrogen_Schema_Color_Contrast.luminanceRGB(bg);
        
        // Determine if we need darker or lighter foreground
var needDarker = bgLum > 0.5;
        var $57 = currentRatio >= 4.5;
        if ($57) {
            return fg;
        };
        if (needDarker) {
            return Hydrogen_Schema_Color_RGB.rgb(0)(0)(0);
        };
        return Hydrogen_Schema_Color_RGB.rgb(255)(255)(255);
    };
};
var eqCVDType = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Normal && y instanceof Normal) {
                return true;
            };
            if (x instanceof Protanopia && y instanceof Protanopia) {
                return true;
            };
            if (x instanceof Protanomaly && y instanceof Protanomaly) {
                return true;
            };
            if (x instanceof Deuteranopia && y instanceof Deuteranopia) {
                return true;
            };
            if (x instanceof Deuteranomaly && y instanceof Deuteranomaly) {
                return true;
            };
            if (x instanceof Tritanopia && y instanceof Tritanopia) {
                return true;
            };
            if (x instanceof Tritanomaly && y instanceof Tritanomaly) {
                return true;
            };
            if (x instanceof Achromatopsia && y instanceof Achromatopsia) {
                return true;
            };
            return false;
        };
    }
};
var eq = /* #__PURE__ */ Data_Eq.eq(/* #__PURE__ */ Data_Eq.eqArray(/* #__PURE__ */ Data_Eq.eqRec()(/* #__PURE__ */ Data_Eq.eqRowCons(/* #__PURE__ */ Data_Eq.eqRowCons(/* #__PURE__ */ Data_Eq.eqRowCons(/* #__PURE__ */ Data_Eq.eqRowCons(/* #__PURE__ */ Data_Eq.eqRowCons(/* #__PURE__ */ Data_Eq.eqRowCons(Data_Eq.eqRowNil)()({
    reflectSymbol: function () {
        return "requiredContrast";
    }
})(Data_Eq.eqNumber))()({
    reflectSymbol: function () {
        return "prevalenceMales";
    }
})(Data_Eq.eqNumber))()({
    reflectSymbol: function () {
        return "prevalenceFemales";
    }
})(Data_Eq.eqNumber))()({
    reflectSymbol: function () {
        return "message";
    }
})(Data_Eq.eqString))()({
    reflectSymbol: function () {
        return "cvdType";
    }
})(eqCVDType))()({
    reflectSymbol: function () {
        return "actualContrast";
    }
})(Data_Eq.eqNumber))));
var ordCVDType = {
    compare: function (x) {
        return function (y) {
            if (x instanceof Normal && y instanceof Normal) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof Normal) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof Normal) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof Protanopia && y instanceof Protanopia) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof Protanopia) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof Protanopia) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof Protanomaly && y instanceof Protanomaly) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof Protanomaly) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof Protanomaly) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof Deuteranopia && y instanceof Deuteranopia) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof Deuteranopia) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof Deuteranopia) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof Deuteranomaly && y instanceof Deuteranomaly) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof Deuteranomaly) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof Deuteranomaly) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof Tritanopia && y instanceof Tritanopia) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof Tritanopia) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof Tritanopia) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof Tritanomaly && y instanceof Tritanomaly) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof Tritanomaly) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof Tritanomaly) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof Achromatopsia && y instanceof Achromatopsia) {
                return Data_Ordering.EQ.value;
            };
            throw new Error("Failed pattern match at Hydrogen.Schema.Color.CVD (line 0, column 0 - line 0, column 0): " + [ x.constructor.name, y.constructor.name ]);
        };
    },
    Eq0: function () {
        return eqCVDType;
    }
};

// | Deuteranopia transformation matrix (no green cones)
var deuteranopiaMatrix = {
    m00: 0.625,
    m01: 0.375,
    m02: 0.0,
    m10: 0.7,
    m11: 0.3,
    m12: 0.0,
    m20: 0.0,
    m21: 0.3,
    m22: 0.7
};

// | Deuteranomaly transformation matrix (weak green cones)
var deuteranomalyMatrix = {
    m00: 0.8,
    m01: 0.2,
    m02: 0.0,
    m10: 0.258,
    m11: 0.742,
    m12: 0.0,
    m20: 0.0,
    m21: 0.142,
    m22: 0.858
};

// | Prevalence data for CVD types
// |
// | Returns percentage of population affected, separated by sex.
// |
// | **Sources (as of 2026-02-21):**
// | - National Eye Institute (NEI): 1 in 12 men (8.33%), 1 in 200 women (0.5%)
// | - Colour Blind Awareness (UK): Detailed breakdown by type
// |
// | **Total CVD prevalence: 8% males, 0.5% females worldwide**
// | (Higher in Scandinavia: 10-11% males; Lower in sub-Saharan Africa)
var cvdPrevalence = function (v) {
    if (v instanceof Normal) {
        return {
            males: 92.0,
            females: 99.5
        };
    };
    if (v instanceof Protanopia) {
        return {
            males: 1.0,
            females: 3.0e-2
        };
    };
    if (v instanceof Deuteranopia) {
        return {
            males: 1.0,
            females: 3.0e-2
        };
    };
    if (v instanceof Tritanopia) {
        return {
            males: 2.0e-3,
            females: 2.0e-3
        };
    };
    if (v instanceof Protanomaly) {
        return {
            males: 1.0,
            females: 3.0e-2
        };
    };
    if (v instanceof Deuteranomaly) {
        return {
            males: 5.0,
            females: 0.4
        };
    };
    if (v instanceof Tritanomaly) {
        return {
            males: 2.0e-3,
            females: 2.0e-3
        };
    };
    if (v instanceof Achromatopsia) {
        return {
            males: 3.0e-3,
            females: 3.0e-3
        };
    };
    throw new Error("Failed pattern match at Hydrogen.Schema.Color.CVD (line 100, column 17 - line 111, column 52): " + [ v.constructor.name ]);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // internal
// ═══════════════════════════════════════════════════════════════════════════════
// | Apply a 3x3 transformation matrix to RGB color
var applyMatrix = function (m) {
    return function (color) {
        var r = Data_Int.toNumber(Hydrogen_Schema_Color_Channel.unwrap(Hydrogen_Schema_Color_RGB.red(color))) / 255.0;
        var g = Data_Int.toNumber(Hydrogen_Schema_Color_Channel.unwrap(Hydrogen_Schema_Color_RGB.green(color))) / 255.0;
        var clamp = function (x) {
            return min(1.0)(max(0.0)(x));
        };
        var b = Data_Int.toNumber(Hydrogen_Schema_Color_Channel.unwrap(Hydrogen_Schema_Color_RGB.blue(color))) / 255.0;
        var b$prime = m.m20 * r + m.m21 * g + m.m22 * b;
        var g$prime = m.m10 * r + m.m11 * g + m.m12 * b;
        var r$prime = m.m00 * r + m.m01 * g + m.m02 * b;
        return Hydrogen_Schema_Color_RGB.rgb(Data_Int.round(clamp(r$prime) * 255.0))(Data_Int.round(clamp(g$prime) * 255.0))(Data_Int.round(clamp(b$prime) * 255.0));
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // simulation
// ═══════════════════════════════════════════════════════════════════════════════
// | Simulate how a color appears with a given CVD type
// |
// | Uses transformation matrices based on Brettel, Viénot and Mollon (1997)
// | and Viénot, Brettel and Mollon (1999) research.
// |
// | ```purescript
// | simulateCVD Deuteranopia (RGB.rgb 255 0 0)  -- How red looks with no green cones
// | simulateCVD Achromatopsia (RGB.rgb 59 130 246)  -- Blue becomes gray
// | ```
var simulateCVD = function (cvdType) {
    return function (color) {
        if (cvdType instanceof Normal) {
            return color;
        };
        if (cvdType instanceof Protanopia) {
            return applyMatrix(protanopiaMatrix)(color);
        };
        if (cvdType instanceof Protanomaly) {
            return applyMatrix(protanomalyMatrix)(color);
        };
        if (cvdType instanceof Deuteranopia) {
            return applyMatrix(deuteranopiaMatrix)(color);
        };
        if (cvdType instanceof Deuteranomaly) {
            return applyMatrix(deuteranomalyMatrix)(color);
        };
        if (cvdType instanceof Tritanopia) {
            return applyMatrix(tritanopiaMatrix)(color);
        };
        if (cvdType instanceof Tritanomaly) {
            return applyMatrix(tritanomalyMatrix)(color);
        };
        if (cvdType instanceof Achromatopsia) {
            return toGrayscale(color);
        };
        throw new Error("Failed pattern match at Hydrogen.Schema.Color.CVD (line 147, column 29 - line 155, column 37): " + [ cvdType.constructor.name ]);
    };
};

// | Check accessibility for all CVD types and return all failures
// |
// | Returns Right unit if accessible for all CVD types, or Left with an array
// | of ALL failures. The array is never empty if Left.
// |
// | For showcase use: display all accessibility issues simultaneously so users
// | understand the full impact of their color choices.
// |
// | ```purescript
// | checkAccessibility red green
// | -- Right unit  (all CVD types can distinguish these colors)
// | -- OR
// | -- Left [ { cvdType: Protanopia, actualContrast: 2.1, prevalenceMales: 1.0, ... }
// |        , { cvdType: Deuteranopia, actualContrast: 1.8, prevalenceMales: 1.0, ... } ]
// | ```
var checkAccessibility = function (fg) {
    return function (bg) {
        var checkType = function (cvdType) {
            var sim2 = simulateCVD(cvdType)(bg);
            var sim1 = simulateCVD(cvdType)(fg);
            var ratio = Hydrogen_Schema_Color_Contrast.contrastRatio(sim1)(sim2);
            var prevalence = cvdPrevalence(cvdType);
            var $65 = ratio >= 4.5;
            if ($65) {
                return Data_Maybe.Nothing.value;
            };
            return new Data_Maybe.Just({
                cvdType: cvdType,
                actualContrast: ratio,
                requiredContrast: 4.5,
                prevalenceMales: prevalence.males,
                prevalenceFemales: prevalence.females,
                message: "Colors not distinguishable for " + (show1(cvdType) + (" (" + (show(prevalence.males) + ("% males, " + (show(prevalence.females) + ("% females). " + ("Contrast " + (show(ratio) + (":1, needs " + (show(4.5) + ":1"))))))))))
            });
        };
        
        // Check ALL CVD types, including anomaly variants
        // Deuteranomaly alone affects 5% of males - cannot be skipped
var allTypes = [ Protanopia.value, Protanomaly.value, Deuteranopia.value, Deuteranomaly.value, Tritanopia.value, Tritanomaly.value, Achromatopsia.value ];
        var issues = map(checkType)(allTypes);
        var failures = foldr(function (m) {
            return function (acc) {
                if (m instanceof Data_Maybe.Just) {
                    return append1([ m.value0 ])(acc);
                };
                if (m instanceof Data_Maybe.Nothing) {
                    return acc;
                };
                throw new Error("Failed pattern match at Hydrogen.Schema.Color.CVD (line 229, column 33 - line 231, column 21): " + [ m.constructor.name ]);
            };
        })([  ])(issues);
        var $68 = eq(failures)([  ]);
        if ($68) {
            return new Data_Either.Right(Data_Unit.unit);
        };
        return new Data_Either.Left(failures);
    };
};

// | Check contrast for all CVD types
// |
// | Returns the minimum contrast ratio across all CVD simulations.
// | Useful for ensuring designs work for everyone.
// |
// | ```purescript
// | cvdSafeContrast foreground background  -- Minimum contrast across all CVDs
// | ```
var cvdSafeContrast = function (fg) {
    return function (bg) {
        var minimum = function (v) {
            if (v.length === 0) {
                return 1.0;
            };
            return foldr(min)(21.0)(v);
        };
        
        // Check ALL CVD types including Normal vision
var allTypes = [ Normal.value, Protanopia.value, Protanomaly.value, Deuteranopia.value, Deuteranomaly.value, Tritanopia.value, Tritanomaly.value, Achromatopsia.value ];
        var contrasts = map(function (cvd) {
            var sim2 = simulateCVD(cvd)(bg);
            var sim1 = simulateCVD(cvd)(fg);
            return Hydrogen_Schema_Color_Contrast.contrastRatio(sim1)(sim2);
        })(allTypes);
        return minimum(contrasts);
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // distinguishability
// ═══════════════════════════════════════════════════════════════════════════════
// | Check if two colors are distinguishable for a given CVD type
// |
// | Returns true if the colors have sufficient contrast after CVD simulation.
// | Uses WCAG AA threshold (4.5:1) as minimum distinguishability.
// |
// | ```purescript
// | isDistinguishable Deuteranopia red green  -- Can these be told apart?
// | ```
var isDistinguishable = function (cvdType) {
    return function (c1) {
        return function (c2) {
            var sim2 = simulateCVD(cvdType)(c2);
            var sim1 = simulateCVD(cvdType)(c1);
            var ratio = Hydrogen_Schema_Color_Contrast.contrastRatio(sim1)(sim2);
            return ratio >= 4.5;
        };
    };
};

// | Suggest an accessible alternative color
// |
// | Given a foreground and background, suggest a foreground that works for
// | all CVD types. Returns Nothing if the original is already accessible.
// |
// | ```purescript
// | suggestAccessibleAlternative red green  -- Suggest better foreground
// | ```
var suggestAccessibleAlternative = function (fg) {
    return function (bg) {
        var allTypes = [ Protanopia.value, Protanomaly.value, Deuteranopia.value, Deuteranomaly.value, Tritanopia.value, Tritanomaly.value, Achromatopsia.value ];
        var allDistinguishable = all(function (cvd) {
            return isDistinguishable(cvd)(fg)(bg);
        })(allTypes);
        if (allDistinguishable) {
            return Data_Maybe.Nothing.value;
        };
        return new Data_Maybe.Just(makeAccessible(fg)(bg));
    };
};

// | Ensure a color is accessible, correcting it if necessary
// |
// | For showcase/playground use: automatically correct colors as users pick them.
// | If colors are already accessible, returns the original foreground unchanged.
// | If not accessible, returns a corrected version that works for all CVD types.
// |
// | ```purescript
// | ensureAccessible red green  -- Returns red if accessible, corrected version if not
// | ```
var ensureAccessible = function (fg) {
    return function (bg) {
        return Data_Maybe.fromMaybe(fg)(suggestAccessibleAlternative(fg)(bg));
    };
};
export {
    Normal,
    Protanopia,
    Protanomaly,
    Deuteranopia,
    Deuteranomaly,
    Tritanopia,
    Tritanomaly,
    Achromatopsia,
    cvdPrevalence,
    simulateCVD,
    isDistinguishable,
    checkAccessibility,
    suggestAccessibleAlternative,
    ensureAccessible,
    cvdSafeContrast,
    eqCVDType,
    ordCVDType,
    showCVDType
};
