// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                      // hydrogen // schema // color // magenta
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Magenta - magenta ink percentage for CMYK printing.
// |
// | Measured as a percentage from 0 to 100:
// | - **0%**: No magenta ink
// | - **50%**: Half coverage
// | - **100%**: Full magenta ink coverage
// |
// | Part of the CMYK subtractive color model used in printing.
// | Magenta absorbs green light, allowing red and blue to reflect.
import * as Data_Int from "../Data.Int/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Hydrogen_Schema_Bounded from "../Hydrogen.Schema.Bounded/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);
var compare = /* #__PURE__ */ Data_Ord.compare(Data_Ord.ordInt);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // magenta
// ═══════════════════════════════════════════════════════════════════════════════
// | Magenta ink percentage (0-100)
// |
// | Represents magenta ink coverage in CMYK printing. 0% = no magenta, 100% = full coverage.
var Magenta = function (x) {
    return x;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // accessors
// ═══════════════════════════════════════════════════════════════════════════════
// | Extract the raw Int value
var unwrap = function (v) {
    return v;
};

// | Create a magenta value without clamping
// |
// | Use only when you know the value is valid.
var unsafeMagenta = Magenta;

// | Convert to unit interval (0.0-1.0)
var toUnitInterval = function (v) {
    return Data_Int.toNumber(v) / 100.0;
};

// | Convert to Number for calculations
var toNumber = function (v) {
    return Data_Int.toNumber(v);
};
var showMagenta = {
    show: function (v) {
        return show(v) + "%";
    }
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // constructors
// ═══════════════════════════════════════════════════════════════════════════════
// | Create a magenta value, clamping to 0-100
var magenta = function (n) {
    return Hydrogen_Schema_Bounded.clampInt(0)(100)(n);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // operations
// ═══════════════════════════════════════════════════════════════════════════════
// | Scale magenta by a factor (0.0 to 2.0 typical)
var scale = function (factor) {
    return function (v) {
        return magenta(Data_Int.round(Data_Int.toNumber(v) * factor));
    };
};

// | Increase magenta by percentage points
var increase = function (amount) {
    return function (v) {
        return magenta(v + amount | 0);
    };
};
var eqMagenta = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordMagenta = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqMagenta;
    }
};

// | Decrease magenta by percentage points
var decrease = function (amount) {
    return function (v) {
        return magenta(v - amount | 0);
    };
};

// | Bounds documentation for this type
var bounds = /* #__PURE__ */ Hydrogen_Schema_Bounded.intBounds(0)(100)("magenta")("Magenta ink percentage");
export {
    magenta,
    unsafeMagenta,
    unwrap,
    scale,
    increase,
    decrease,
    bounds,
    toNumber,
    toUnitInterval,
    eqMagenta,
    ordMagenta,
    showMagenta
};
