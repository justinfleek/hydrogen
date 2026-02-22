// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                       // hydrogen // schema // color // oklch
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | OKLCH - Cylindrical version of OKLAB (hue-based).
// |
// | **BEST FOR UI DESIGN:**
// | OKLCH is OKLAB in cylindrical coordinates, making it perfect for:
// | - Color pickers (hue wheel + chroma/lightness)
// | - Generating color palettes (rotate hue, adjust chroma)
// | - CSS (modern browsers support oklch() function)
// |
// | **Components:**
// | - **L**: Lightness, 0.0 (black) to 1.0 (white)
// | - **C**: Chroma (colorfulness), 0.0 (gray) to ~0.4 (vivid)
// | - **H**: Hue, 0-360 degrees (color wheel position)
// |
// | **Why use OKLCH over HSL?**
// | - Perceptually uniform (HSL isn't)
// | - Same lightness = same perceived brightness
// | - Better for accessibility (contrast calculations)
// | - Modern CSS standard
import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Ordering from "../Data.Ordering/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Hydrogen_Schema_Bounded from "../Hydrogen.Schema.Bounded/index.js";
import * as Hydrogen_Schema_Color_Hue from "../Hydrogen.Schema.Color.Hue/index.js";
import * as Hydrogen_Schema_Color_OKLAB from "../Hydrogen.Schema.Color.OKLAB/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showNumber);
var show1 = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);
var compare = /* #__PURE__ */ Data_Ord.compare(Data_Ord.ordNumber);
var eq1 = /* #__PURE__ */ Data_Eq.eq(Hydrogen_Schema_Color_Hue.eqHue);
var eq2 = /* #__PURE__ */ Data_Eq.eq(Hydrogen_Schema_Color_OKLAB.eqOkL);
var compare1 = /* #__PURE__ */ Data_Ord.compare(Hydrogen_Schema_Color_Hue.ordHue);
var compare2 = /* #__PURE__ */ Data_Ord.compare(Hydrogen_Schema_Color_OKLAB.ordOkL);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                        // atom
// ═══════════════════════════════════════════════════════════════════════════════
// | Chroma component (colorfulness): 0.0-0.4 typical range
var OkChroma = function (x) {
    return x;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // molecule
// ═══════════════════════════════════════════════════════════════════════════════
// | OKLCH color - cylindrical OKLAB
var OKLCH = function (x) {
    return x;
};
var unwrapChroma = function (v) {
    return v;
};
var showOkChroma = {
    show: function (v) {
        return "OkChroma " + show(v);
    }
};
var showOKLCH = {
    show: function (v) {
        return "oklch(" + (show(Hydrogen_Schema_Color_OKLAB.unwrapOkL(v.l)) + (", " + (show(unwrapChroma(v.c)) + (", " + (show1(Hydrogen_Schema_Color_Hue.unwrap(v.h)) + ")")))));
    }
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // operations
// ═══════════════════════════════════════════════════════════════════════════════
// | Rotate hue by degrees
var rotateHue = function (degrees) {
    return function (v) {
        return {
            l: v.l,
            c: v.c,
            h: Hydrogen_Schema_Color_Hue.rotate(degrees)(v.h)
        };
    };
};

// | Convert to record
var oklchToRecord = function (v) {
    return {
        l: Hydrogen_Schema_Color_OKLAB.unwrapOkL(v.l),
        c: unwrapChroma(v.c),
        h: Hydrogen_Schema_Color_Hue.unwrap(v.h)
    };
};

// | Alias for oklchToRecord
var toRecord = oklchToRecord;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // accessors
// ═══════════════════════════════════════════════════════════════════════════════
// | Extract lightness
var oklchL = function (v) {
    return v.l;
};

// | Create chroma value (clamped 0.0-0.4)
var okChroma = function (n) {
    return Hydrogen_Schema_Bounded.clampNumber(0.0)(0.4)(n);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // constructors
// ═══════════════════════════════════════════════════════════════════════════════
// | Create OKLCH color
var oklch = function (l) {
    return function (c) {
        return function (h) {
            return {
                l: Hydrogen_Schema_Color_OKLAB.okLValue(l),
                c: okChroma(c),
                h: Hydrogen_Schema_Color_Hue.hue(h)
            };
        };
    };
};

// | Create from record
var oklchFromRecord = function (v) {
    return oklch(v.l)(v.c)(v.h);
};

// | Increase chroma (more vivid)
var increaseChroma = function (amount) {
    return function (v) {
        return {
            l: v.l,
            h: v.h,
            c: okChroma(unwrapChroma(v.c) + amount)
        };
    };
};

// | Extract hue
var hue = function (v) {
    return v.h;
};
var eqOkChroma = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var eq3 = /* #__PURE__ */ Data_Eq.eq(eqOkChroma);
var ordOkChroma = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqOkChroma;
    }
};
var compare3 = /* #__PURE__ */ Data_Ord.compare(ordOkChroma);
var eqOKLCH = {
    eq: function (x) {
        return function (y) {
            return eq3(x.c)(y.c) && eq1(x.h)(y.h) && eq2(x.l)(y.l);
        };
    }
};
var ordOKLCH = {
    compare: function (x) {
        return function (y) {
            var v = compare3(x.c)(y.c);
            if (v instanceof Data_Ordering.LT) {
                return Data_Ordering.LT.value;
            };
            if (v instanceof Data_Ordering.GT) {
                return Data_Ordering.GT.value;
            };
            var v1 = compare1(x.h)(y.h);
            if (v1 instanceof Data_Ordering.LT) {
                return Data_Ordering.LT.value;
            };
            if (v1 instanceof Data_Ordering.GT) {
                return Data_Ordering.GT.value;
            };
            return compare2(x.l)(y.l);
        };
    },
    Eq0: function () {
        return eqOKLCH;
    }
};

// | Decrease chroma (more muted)
var decreaseChroma = function (amount) {
    return function (v) {
        return {
            l: v.l,
            h: v.h,
            c: okChroma(unwrapChroma(v.c) - amount)
        };
    };
};

// | Extract chroma
var chroma = function (v) {
    return v.c;
};
export {
    oklch,
    oklchFromRecord,
    okChroma,
    oklchL,
    chroma,
    hue,
    unwrapChroma,
    oklchToRecord,
    toRecord,
    rotateHue,
    increaseChroma,
    decreaseChroma,
    eqOkChroma,
    ordOkChroma,
    showOkChroma,
    eqOKLCH,
    ordOKLCH,
    showOKLCH
};
