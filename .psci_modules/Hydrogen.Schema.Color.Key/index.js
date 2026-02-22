// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                          // hydrogen // schema // color // key
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Key (Black) - black ink percentage for CMYK printing.
// |
// | Measured as a percentage from 0 to 100:
// | - **0%**: No black ink (color built from CMY only)
// | - **50%**: Half black coverage
// | - **100%**: Full black ink coverage (rich black)
// |
// | The "K" in CMYK. Black ink is used because:
// | 1. Pure black (100% CMY) wastes ink and doesn't look truly black
// | 2. Black ink is cheaper than mixing three colors
// | 3. Text and fine details need true black, not composite
// |
// | Named "Key" historically from printing plates where the black plate
// | was the "key plate" that other colors were registered to.
import * as Data_Int from "../Data.Int/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Hydrogen_Schema_Bounded from "../Hydrogen.Schema.Bounded/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);
var compare = /* #__PURE__ */ Data_Ord.compare(Data_Ord.ordInt);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                         // key
// ═══════════════════════════════════════════════════════════════════════════════
// | Key (black) ink percentage (0-100)
// |
// | Represents black ink coverage in CMYK printing. 0% = no black, 100% = full coverage.
// | The fourth channel in CMYK, added to improve print quality and reduce ink costs.
var Key = function (x) {
    return x;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // accessors
// ═══════════════════════════════════════════════════════════════════════════════
// | Extract the raw Int value
var unwrap = function (v) {
    return v;
};

// | Create a key value without clamping
// |
// | Use only when you know the value is valid.
var unsafeKey = Key;

// | Convert to unit interval (0.0-1.0)
var toUnitInterval = function (v) {
    return Data_Int.toNumber(v) / 100.0;
};

// | Convert to Number for calculations
var toNumber = function (v) {
    return Data_Int.toNumber(v);
};
var showKey = {
    show: function (v) {
        return show(v) + "%";
    }
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // constructors
// ═══════════════════════════════════════════════════════════════════════════════
// | Create a key (black) value, clamping to 0-100
var key = function (n) {
    return Hydrogen_Schema_Bounded.clampInt(0)(100)(n);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // operations
// ═══════════════════════════════════════════════════════════════════════════════
// | Scale key by a factor (0.0 to 2.0 typical)
var scale = function (factor) {
    return function (v) {
        return key(Data_Int.round(Data_Int.toNumber(v) * factor));
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // predicates
// ═══════════════════════════════════════════════════════════════════════════════
// | Check if this is "rich black" (K > 80%)
// |
// | Rich blacks combine high K with some CMY for deeper, richer blacks.
// | Common in print for backgrounds and large black areas.
var isRichBlack = function (v) {
    return v > 80;
};

// | Increase key by percentage points
var increase = function (amount) {
    return function (v) {
        return key(v + amount | 0);
    };
};
var eqKey = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordKey = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqKey;
    }
};

// | Decrease key by percentage points
var decrease = function (amount) {
    return function (v) {
        return key(v - amount | 0);
    };
};

// | Bounds documentation for this type
var bounds = /* #__PURE__ */ Hydrogen_Schema_Bounded.intBounds(0)(100)("key")("Black (Key) ink percentage");
export {
    key,
    unsafeKey,
    unwrap,
    scale,
    increase,
    decrease,
    bounds,
    toNumber,
    toUnitInterval,
    isRichBlack,
    eqKey,
    ordKey,
    showKey
};
