// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                         // hydrogen // schema // color // cyan
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Cyan - cyan ink percentage for CMYK printing.
// |
// | Measured as a percentage from 0 to 100:
// | - **0%**: No cyan ink
// | - **50%**: Half coverage
// | - **100%**: Full cyan ink coverage
// |
// | Part of the CMYK subtractive color model used in printing.
// | Cyan absorbs red light, allowing green and blue to reflect.
import * as Data_Int from "../Data.Int/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Hydrogen_Schema_Bounded from "../Hydrogen.Schema.Bounded/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);
var compare = /* #__PURE__ */ Data_Ord.compare(Data_Ord.ordInt);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                        // cyan
// ═══════════════════════════════════════════════════════════════════════════════
// | Cyan ink percentage (0-100)
// |
// | Represents cyan ink coverage in CMYK printing. 0% = no cyan, 100% = full coverage.
var Cyan = function (x) {
    return x;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // accessors
// ═══════════════════════════════════════════════════════════════════════════════
// | Extract the raw Int value
var unwrap = function (v) {
    return v;
};

// | Create a cyan value without clamping
// |
// | Use only when you know the value is valid.
var unsafeCyan = Cyan;

// | Convert to unit interval (0.0-1.0)
var toUnitInterval = function (v) {
    return Data_Int.toNumber(v) / 100.0;
};

// | Convert to Number for calculations
var toNumber = function (v) {
    return Data_Int.toNumber(v);
};
var showCyan = {
    show: function (v) {
        return show(v) + "%";
    }
};
var eqCyan = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordCyan = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqCyan;
    }
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // constructors
// ═══════════════════════════════════════════════════════════════════════════════
// | Create a cyan value, clamping to 0-100
var cyan = function (n) {
    return Hydrogen_Schema_Bounded.clampInt(0)(100)(n);
};

// | Decrease cyan by percentage points
var decrease = function (amount) {
    return function (v) {
        return cyan(v - amount | 0);
    };
};

// | Increase cyan by percentage points
var increase = function (amount) {
    return function (v) {
        return cyan(v + amount | 0);
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // operations
// ═══════════════════════════════════════════════════════════════════════════════
// | Scale cyan by a factor (0.0 to 2.0 typical)
var scale = function (factor) {
    return function (v) {
        return cyan(Data_Int.round(Data_Int.toNumber(v) * factor));
    };
};

// | Bounds documentation for this type
var bounds = /* #__PURE__ */ Hydrogen_Schema_Bounded.intBounds(0)(100)("cyan")("Cyan ink percentage");
export {
    cyan,
    unsafeCyan,
    unwrap,
    scale,
    increase,
    decrease,
    bounds,
    toNumber,
    toUnitInterval,
    eqCyan,
    ordCyan,
    showCyan
};
