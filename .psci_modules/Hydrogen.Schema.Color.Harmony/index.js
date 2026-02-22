// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                       // hydrogen // schema // color // harmony
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Color harmony - relationships on the color wheel.
// |
// | Classic color theory for creating harmonious palettes:
// | - **Complementary**: Opposite colors (180°)
// | - **Triadic**: Three equidistant colors (120°)
// | - **Analogous**: Adjacent colors (30°)
// | - And more...
import * as Data_Boolean from "../Data.Boolean/index.js";
import * as Data_EuclideanRing from "../Data.EuclideanRing/index.js";
import * as Hydrogen_Schema_Color_HSL from "../Hydrogen.Schema.Color.HSL/index.js";
import * as Hydrogen_Schema_Color_Hue from "../Hydrogen.Schema.Color.Hue/index.js";
import * as Hydrogen_Schema_Color_Lightness from "../Hydrogen.Schema.Color.Lightness/index.js";
import * as Hydrogen_Schema_Color_Saturation from "../Hydrogen.Schema.Color.Saturation/index.js";
var mod = /* #__PURE__ */ Data_EuclideanRing.mod(Data_EuclideanRing.euclideanRingInt);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // color harmony
// ═══════════════════════════════════════════════════════════════════════════════
// | Classic color harmony schemes based on the color wheel
var Complementary = /* #__PURE__ */ (function () {
    function Complementary() {

    };
    Complementary.value = new Complementary();
    return Complementary;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // color harmony
// ═══════════════════════════════════════════════════════════════════════════════
// | Classic color harmony schemes based on the color wheel
var SplitComplementary = /* #__PURE__ */ (function () {
    function SplitComplementary() {

    };
    SplitComplementary.value = new SplitComplementary();
    return SplitComplementary;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // color harmony
// ═══════════════════════════════════════════════════════════════════════════════
// | Classic color harmony schemes based on the color wheel
var Triadic = /* #__PURE__ */ (function () {
    function Triadic() {

    };
    Triadic.value = new Triadic();
    return Triadic;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // color harmony
// ═══════════════════════════════════════════════════════════════════════════════
// | Classic color harmony schemes based on the color wheel
var Tetradic = /* #__PURE__ */ (function () {
    function Tetradic() {

    };
    Tetradic.value = new Tetradic();
    return Tetradic;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // color harmony
// ═══════════════════════════════════════════════════════════════════════════════
// | Classic color harmony schemes based on the color wheel
var Square = /* #__PURE__ */ (function () {
    function Square() {

    };
    Square.value = new Square();
    return Square;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // color harmony
// ═══════════════════════════════════════════════════════════════════════════════
// | Classic color harmony schemes based on the color wheel
var Analogous = /* #__PURE__ */ (function () {
    function Analogous() {

    };
    Analogous.value = new Analogous();
    return Analogous;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // color harmony
// ═══════════════════════════════════════════════════════════════════════════════
// | Classic color harmony schemes based on the color wheel
var AnalogousWide = /* #__PURE__ */ (function () {
    function AnalogousWide() {

    };
    AnalogousWide.value = new AnalogousWide();
    return AnalogousWide;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // color harmony
// ═══════════════════════════════════════════════════════════════════════════════
// | Classic color harmony schemes based on the color wheel
var DoubleSplit = /* #__PURE__ */ (function () {
    function DoubleSplit() {

    };
    DoubleSplit.value = new DoubleSplit();
    return DoubleSplit;
})();
var showHarmony = {
    show: function (v) {
        if (v instanceof Complementary) {
            return "Complementary";
        };
        if (v instanceof SplitComplementary) {
            return "Split Complementary";
        };
        if (v instanceof Triadic) {
            return "Triadic";
        };
        if (v instanceof Tetradic) {
            return "Tetradic";
        };
        if (v instanceof Square) {
            return "Square";
        };
        if (v instanceof Analogous) {
            return "Analogous";
        };
        if (v instanceof AnalogousWide) {
            return "Analogous (Wide)";
        };
        if (v instanceof DoubleSplit) {
            return "Double Split";
        };
        throw new Error("Failed pattern match at Hydrogen.Schema.Color.Harmony (line 44, column 10 - line 52, column 34): " + [ v.constructor.name ]);
    }
};
var mod$prime = function (a) {
    return function (b) {
        return mod(mod(a)(b) + b | 0)(b);
    };
};
var eqHarmony = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Complementary && y instanceof Complementary) {
                return true;
            };
            if (x instanceof SplitComplementary && y instanceof SplitComplementary) {
                return true;
            };
            if (x instanceof Triadic && y instanceof Triadic) {
                return true;
            };
            if (x instanceof Tetradic && y instanceof Tetradic) {
                return true;
            };
            if (x instanceof Square && y instanceof Square) {
                return true;
            };
            if (x instanceof Analogous && y instanceof Analogous) {
                return true;
            };
            if (x instanceof AnalogousWide && y instanceof AnalogousWide) {
                return true;
            };
            if (x instanceof DoubleSplit && y instanceof DoubleSplit) {
                return true;
            };
            return false;
        };
    }
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // helpers
// ═══════════════════════════════════════════════════════════════════════════════
var clamp100 = function (n) {
    if (n < 0) {
        return 0;
    };
    if (n > 100) {
        return 100;
    };
    if (Data_Boolean.otherwise) {
        return n;
    };
    throw new Error("Failed pattern match at Hydrogen.Schema.Color.Harmony (line 96, column 1 - line 96, column 23): " + [ n.constructor.name ]);
};

// | Generate colors based on harmony rules
var generateHarmony = function (v) {
    var s = Hydrogen_Schema_Color_Saturation.unwrap(Hydrogen_Schema_Color_HSL.saturation(v.baseColor));
    var s$prime = clamp100(s + v.saturationShift | 0);
    var l = Hydrogen_Schema_Color_Lightness.unwrap(Hydrogen_Schema_Color_HSL.lightness(v.baseColor));
    var l$prime = clamp100(l + v.lightnessShift | 0);
    var makeColor = function (hue$prime) {
        return Hydrogen_Schema_Color_HSL.hsl(mod$prime(hue$prime)(360))(s$prime)(l$prime);
    };
    var h = Hydrogen_Schema_Color_Hue.unwrap(Hydrogen_Schema_Color_HSL.hue(v.baseColor));
    if (v.harmony instanceof Complementary) {
        return [ v.baseColor, makeColor(h + 180 | 0) ];
    };
    if (v.harmony instanceof SplitComplementary) {
        return [ v.baseColor, makeColor(h + 150 | 0), makeColor(h + 210 | 0) ];
    };
    if (v.harmony instanceof Triadic) {
        return [ v.baseColor, makeColor(h + 120 | 0), makeColor(h + 240 | 0) ];
    };
    if (v.harmony instanceof Tetradic) {
        return [ v.baseColor, makeColor(h + 90 | 0), makeColor(h + 180 | 0), makeColor(h + 270 | 0) ];
    };
    if (v.harmony instanceof Square) {
        return [ v.baseColor, makeColor(h + 90 | 0), makeColor(h + 180 | 0), makeColor(h + 270 | 0) ];
    };
    if (v.harmony instanceof Analogous) {
        return [ makeColor(h - 30 | 0), v.baseColor, makeColor(h + 30 | 0) ];
    };
    if (v.harmony instanceof AnalogousWide) {
        return [ makeColor(h - 60 | 0), v.baseColor, makeColor(h + 60 | 0) ];
    };
    if (v.harmony instanceof DoubleSplit) {
        return [ makeColor(h - 30 | 0), makeColor(h + 30 | 0), makeColor(h + 150 | 0), makeColor(h + 210 | 0) ];
    };
    throw new Error("Failed pattern match at Hydrogen.Schema.Color.Harmony (line 72, column 6 - line 90, column 8): " + [ v.harmony.constructor.name ]);
};
export {
    Complementary,
    SplitComplementary,
    Triadic,
    Tetradic,
    Square,
    Analogous,
    AnalogousWide,
    DoubleSplit,
    generateHarmony,
    eqHarmony,
    showHarmony
};
