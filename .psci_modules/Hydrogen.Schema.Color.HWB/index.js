// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                         // hydrogen // schema // color // hwb
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | HWB - Hue, Whiteness, Blackness (CSS Color Level 4).
// |
// | **MORE INTUITIVE THAN HSL:**
// | Instead of saturation and lightness, HWB uses:
// | - How much white is mixed in (whiteness)
// | - How much black is mixed in (blackness)
// |
// | **Components:**
// | - **H**: Hue, 0-360 degrees (color wheel position)
// | - **W**: Whiteness, 0-100% (amount of white mixed in)
// | - **B**: Blackness, 0-100% (amount of black mixed in)
// |
// | **Use cases:**
// | - CSS4 hwb() function
// | - More intuitive color picking for designers
// | - "Make it lighter" = increase whiteness
// | - "Make it darker" = increase blackness
// |
// | **CSS Example:**
// | hwb(120deg 20% 10%) - green with 20% white, 10% black
import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Ordering from "../Data.Ordering/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Hydrogen_Schema_Bounded from "../Hydrogen.Schema.Bounded/index.js";
import * as Hydrogen_Schema_Color_Hue from "../Hydrogen.Schema.Color.Hue/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);
var compare = /* #__PURE__ */ Data_Ord.compare(Data_Ord.ordInt);
var eq1 = /* #__PURE__ */ Data_Eq.eq(Hydrogen_Schema_Color_Hue.eqHue);
var compare1 = /* #__PURE__ */ Data_Ord.compare(Hydrogen_Schema_Color_Hue.ordHue);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // atoms
// ═══════════════════════════════════════════════════════════════════════════════
// | Whiteness component: 0-100%
var Whiteness = function (x) {
    return x;
};

// | Blackness component: 0-100%
var Blackness = function (x) {
    return x;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // molecule
// ═══════════════════════════════════════════════════════════════════════════════
// | HWB color - composition of Hue, Whiteness, Blackness
var HWB = function (x) {
    return x;
};

// | Create whiteness value (clamped 0-100)
var whiteness = function (n) {
    return Hydrogen_Schema_Bounded.clampInt(0)(100)(n);
};
var unwrapWhiteness = function (v) {
    return v;
};
var unwrapBlackness = function (v) {
    return v;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // css output
// ═══════════════════════════════════════════════════════════════════════════════
// | Convert to CSS hwb() function
var toCss = function (v) {
    return "hwb(" + (show(Hydrogen_Schema_Color_Hue.unwrap(v.h)) + ("deg " + (show(unwrapWhiteness(v.w)) + ("% " + (show(unwrapBlackness(v.b)) + "%)")))));
};
var showWhiteness = {
    show: function (v) {
        return show(v) + "%";
    }
};
var showHWB = {
    show: toCss
};
var showBlackness = {
    show: function (v) {
        return show(v) + "%";
    }
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // operations
// ═══════════════════════════════════════════════════════════════════════════════
// | Rotate hue by degrees
var rotateHue = function (degrees) {
    return function (v) {
        return {
            w: v.w,
            b: v.b,
            h: Hydrogen_Schema_Color_Hue.rotate(degrees)(v.h)
        };
    };
};

// | Increase whiteness (make lighter)
var increaseWhiteness = function (amount) {
    return function (v) {
        return {
            h: v.h,
            b: v.b,
            w: whiteness(unwrapWhiteness(v.w) + amount | 0)
        };
    };
};

// | Convert to record
var hwbToRecord = function (v) {
    return {
        h: Hydrogen_Schema_Color_Hue.unwrap(v.h),
        w: unwrapWhiteness(v.w),
        b: unwrapBlackness(v.b)
    };
};

// | Alias for hwbToRecord
var toRecord = hwbToRecord;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // accessors
// ═══════════════════════════════════════════════════════════════════════════════
// | Extract hue
var hue = function (v) {
    return v.h;
};

// | Extract whiteness
var getWhiteness = function (v) {
    return v.w;
};

// | Extract blackness
var getBlackness = function (v) {
    return v.b;
};
var eqWhiteness = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var eq2 = /* #__PURE__ */ Data_Eq.eq(eqWhiteness);
var ordWhiteness = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqWhiteness;
    }
};
var compare2 = /* #__PURE__ */ Data_Ord.compare(ordWhiteness);
var eqBlackness = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var eq3 = /* #__PURE__ */ Data_Eq.eq(eqBlackness);
var eqHWB = {
    eq: function (x) {
        return function (y) {
            return eq3(x.b)(y.b) && eq1(x.h)(y.h) && eq2(x.w)(y.w);
        };
    }
};
var ordBlackness = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqBlackness;
    }
};
var compare3 = /* #__PURE__ */ Data_Ord.compare(ordBlackness);
var ordHWB = {
    compare: function (x) {
        return function (y) {
            var v = compare3(x.b)(y.b);
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
            return compare2(x.w)(y.w);
        };
    },
    Eq0: function () {
        return eqHWB;
    }
};

// | Create blackness value (clamped 0-100)
var blackness = function (n) {
    return Hydrogen_Schema_Bounded.clampInt(0)(100)(n);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // constructors
// ═══════════════════════════════════════════════════════════════════════════════
// | Create HWB color
var hwb = function (h) {
    return function (w) {
        return function (b) {
            return {
                h: Hydrogen_Schema_Color_Hue.hue(h),
                w: whiteness(w),
                b: blackness(b)
            };
        };
    };
};

// | Create from record
var hwbFromRecord = function (v) {
    return hwb(v.h)(v.w)(v.b);
};

// | Increase blackness (make darker)
var increaseBlackness = function (amount) {
    return function (v) {
        return {
            h: v.h,
            w: v.w,
            b: blackness(unwrapBlackness(v.b) + amount | 0)
        };
    };
};
export {
    hwb,
    hwbFromRecord,
    whiteness,
    blackness,
    hue,
    getWhiteness,
    getBlackness,
    unwrapWhiteness,
    unwrapBlackness,
    hwbToRecord,
    toRecord,
    rotateHue,
    increaseWhiteness,
    increaseBlackness,
    toCss,
    eqWhiteness,
    ordWhiteness,
    showWhiteness,
    eqBlackness,
    ordBlackness,
    showBlackness,
    eqHWB,
    ordHWB,
    showHWB
};
