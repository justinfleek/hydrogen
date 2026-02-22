// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                       // hydrogen // schema // color // oklab
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | OKLAB - Modern perceptually uniform color space.
// |
// | **BETTER THAN LAB:**
// | OKLAB (2020, Björn Ottosson) improves on CIE LAB with:
// | - More uniform hue perception
// | - Better behavior for blue colors
// | - Simpler math (no cube roots)
// | - Faster computation
// | - Better for gradient interpolation
// |
// | **Components:**
// | - **L**: Lightness, 0.0 (black) to 1.0 (white)
// | - **a**: Green-Red axis, typically -0.4 to +0.4
// | - **b**: Blue-Yellow axis, typically -0.4 to +0.4
// |
// | **Use cases:**
// | - Smooth color gradients (better than HSL or LAB)
// | - Perceptually uniform color palettes
// | - Color difference calculations
// | - Modern CSS (oklch() function support)
// |
// | **Reference:**
// | https://bottosson.github.io/posts/oklab/
import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Ordering from "../Data.Ordering/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Hydrogen_Schema_Bounded from "../Hydrogen.Schema.Bounded/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showNumber);
var compare = /* #__PURE__ */ Data_Ord.compare(Data_Ord.ordNumber);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // atoms
// ═══════════════════════════════════════════════════════════════════════════════
// | L component (Lightness): 0.0-1.0
var OkL = function (x) {
    return x;
};

// | b component (Blue-Yellow axis): typically -0.4 to +0.4
var OkB = function (x) {
    return x;
};

// | a component (Green-Red axis): typically -0.4 to +0.4
var OkA = function (x) {
    return x;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // molecule
// ═══════════════════════════════════════════════════════════════════════════════
// | OKLAB color - composition of OkL, OkA, OkB atoms
var OKLAB = function (x) {
    return x;
};
var unwrapOkL = function (v) {
    return v;
};
var unwrapOkB = function (v) {
    return v;
};
var unwrapOkA = function (v) {
    return v;
};
var showOkL = {
    show: function (v) {
        return "OkL " + show(v);
    }
};
var showOkB = {
    show: function (v) {
        return "OkB " + show(v);
    }
};
var showOkA = {
    show: function (v) {
        return "OkA " + show(v);
    }
};
var showOKLAB = {
    show: function (v) {
        return "oklab(" + (show(unwrapOkL(v.l)) + (", " + (show(unwrapOkA(v.a)) + (", " + (show(unwrapOkB(v.b)) + ")")))));
    }
};

// | Convert to record
var oklabToRecord = function (v) {
    return {
        l: unwrapOkL(v.l),
        a: unwrapOkA(v.a),
        b: unwrapOkB(v.b)
    };
};

// | Alias for oklabToRecord
var toRecord = oklabToRecord;

// | Create L value (clamped 0.0-1.0)
var okLValue = function (n) {
    return Hydrogen_Schema_Bounded.clampNumber(0.0)(1.0)(n);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // accessors
// ═══════════════════════════════════════════════════════════════════════════════
// | Extract L component
var okL = function (v) {
    return v.l;
};

// | Create b value (clamped for practical range)
var okBValue = function (n) {
    return Hydrogen_Schema_Bounded.clampNumber(-0.4)(0.4)(n);
};

// | Extract b component
var okB = function (v) {
    return v.b;
};

// | Create a value (clamped for practical range)
var okAValue = function (n) {
    return Hydrogen_Schema_Bounded.clampNumber(-0.4)(0.4)(n);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // constructors
// ═══════════════════════════════════════════════════════════════════════════════
// | Create OKLAB color from raw values
var oklab = function (l) {
    return function (a) {
        return function (b) {
            return {
                l: okLValue(l),
                a: okAValue(a),
                b: okBValue(b)
            };
        };
    };
};

// | Create from record
var oklabFromRecord = function (v) {
    return oklab(v.l)(v.a)(v.b);
};

// | Extract a component
var okA = function (v) {
    return v.a;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // operations
// ═══════════════════════════════════════════════════════════════════════════════
// | Increase lightness (perceptually uniform)
var increaseLightness = function (amount) {
    return function (v) {
        return {
            a: v.a,
            b: v.b,
            l: okLValue(unwrapOkL(v.l) + amount)
        };
    };
};
var eqOkL = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var eq1 = /* #__PURE__ */ Data_Eq.eq(eqOkL);
var ordOkL = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqOkL;
    }
};
var compare1 = /* #__PURE__ */ Data_Ord.compare(ordOkL);
var eqOkB = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var eq2 = /* #__PURE__ */ Data_Eq.eq(eqOkB);
var ordOkB = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqOkB;
    }
};
var compare2 = /* #__PURE__ */ Data_Ord.compare(ordOkB);
var eqOkA = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var eq3 = /* #__PURE__ */ Data_Eq.eq(eqOkA);
var ordOkA = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqOkA;
    }
};
var compare3 = /* #__PURE__ */ Data_Ord.compare(ordOkA);
var eqOKLAB = {
    eq: function (x) {
        return function (y) {
            return eq3(x.a)(y.a) && eq2(x.b)(y.b) && eq1(x.l)(y.l);
        };
    }
};
var ordOKLAB = {
    compare: function (x) {
        return function (y) {
            var v = compare3(x.a)(y.a);
            if (v instanceof Data_Ordering.LT) {
                return Data_Ordering.LT.value;
            };
            if (v instanceof Data_Ordering.GT) {
                return Data_Ordering.GT.value;
            };
            var v1 = compare2(x.b)(y.b);
            if (v1 instanceof Data_Ordering.LT) {
                return Data_Ordering.LT.value;
            };
            if (v1 instanceof Data_Ordering.GT) {
                return Data_Ordering.GT.value;
            };
            return compare1(x.l)(y.l);
        };
    },
    Eq0: function () {
        return eqOKLAB;
    }
};

// | Decrease lightness (perceptually uniform)
var decreaseLightness = function (amount) {
    return function (v) {
        return {
            a: v.a,
            b: v.b,
            l: okLValue(unwrapOkL(v.l) - amount)
        };
    };
};
export {
    oklab,
    oklabFromRecord,
    okLValue,
    okAValue,
    okBValue,
    okL,
    okA,
    okB,
    unwrapOkL,
    unwrapOkA,
    unwrapOkB,
    oklabToRecord,
    toRecord,
    increaseLightness,
    decreaseLightness,
    eqOkL,
    ordOkL,
    showOkL,
    eqOkA,
    ordOkA,
    showOkA,
    eqOkB,
    ordOkB,
    showOkB,
    eqOKLAB,
    ordOKLAB,
    showOKLAB
};
