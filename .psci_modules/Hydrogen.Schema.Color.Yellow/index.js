// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                       // hydrogen // schema // color // yellow
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Yellow - yellow ink percentage for CMYK printing.
// |
// | Measured as a percentage from 0 to 100:
// | - **0%**: No yellow ink
// | - **50%**: Half coverage
// | - **100%**: Full yellow ink coverage
// |
// | Part of the CMYK subtractive color model used in printing.
// | Yellow absorbs blue light, allowing red and green to reflect.
import * as Data_Int from "../Data.Int/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Hydrogen_Schema_Bounded from "../Hydrogen.Schema.Bounded/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);
var compare = /* #__PURE__ */ Data_Ord.compare(Data_Ord.ordInt);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                      // yellow
// ═══════════════════════════════════════════════════════════════════════════════
// | Yellow ink percentage (0-100)
// |
// | Represents yellow ink coverage in CMYK printing. 0% = no yellow, 100% = full coverage.
var Yellow = function (x) {
    return x;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // constructors
// ═══════════════════════════════════════════════════════════════════════════════
// | Create a yellow value, clamping to 0-100
var yellow = function (n) {
    return Hydrogen_Schema_Bounded.clampInt(0)(100)(n);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // accessors
// ═══════════════════════════════════════════════════════════════════════════════
// | Extract the raw Int value
var unwrap = function (v) {
    return v;
};

// | Create a yellow value without clamping
// |
// | Use only when you know the value is valid.
var unsafeYellow = Yellow;

// | Convert to unit interval (0.0-1.0)
var toUnitInterval = function (v) {
    return Data_Int.toNumber(v) / 100.0;
};

// | Convert to Number for calculations
var toNumber = function (v) {
    return Data_Int.toNumber(v);
};
var showYellow = {
    show: function (v) {
        return show(v) + "%";
    }
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // operations
// ═══════════════════════════════════════════════════════════════════════════════
// | Scale yellow by a factor (0.0 to 2.0 typical)
var scale = function (factor) {
    return function (v) {
        return yellow(Data_Int.round(Data_Int.toNumber(v) * factor));
    };
};

// | Increase yellow by percentage points
var increase = function (amount) {
    return function (v) {
        return yellow(v + amount | 0);
    };
};
var eqYellow = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordYellow = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqYellow;
    }
};

// | Decrease yellow by percentage points
var decrease = function (amount) {
    return function (v) {
        return yellow(v - amount | 0);
    };
};

// | Bounds documentation for this type
var bounds = /* #__PURE__ */ Hydrogen_Schema_Bounded.intBounds(0)(100)("yellow")("Yellow ink percentage");
export {
    yellow,
    unsafeYellow,
    unwrap,
    scale,
    increase,
    decrease,
    bounds,
    toNumber,
    toUnitInterval,
    eqYellow,
    ordYellow,
    showYellow
};
