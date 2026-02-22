// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                           // hydrogen // schema // color // hue
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Hue - position on the color wheel.
// |
// | Measured in degrees from 0 to 359:
// | - **0°/360°**: Red
// | - **60°**: Yellow  
// | - **120°**: Green
// | - **180°**: Cyan
// | - **240°**: Blue
// | - **300°**: Magenta
// |
// | Hue is cyclic - values outside 0-359 wrap around.
import * as Data_EuclideanRing from "../Data.EuclideanRing/index.js";
import * as Data_Int from "../Data.Int/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Hydrogen_Schema_Bounded from "../Hydrogen.Schema.Bounded/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);
var mod = /* #__PURE__ */ Data_EuclideanRing.mod(Data_EuclideanRing.euclideanRingInt);
var compare = /* #__PURE__ */ Data_Ord.compare(Data_Ord.ordInt);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                         // hue
// ═══════════════════════════════════════════════════════════════════════════════
// | Hue value in degrees (0-359)
// |
// | Represents position on the color wheel. Red at 0°, cycling through
// | yellow, green, cyan, blue, magenta, and back to red at 360°.
var Hue = function (x) {
    return x;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // accessors
// ═══════════════════════════════════════════════════════════════════════════════
// | Extract the raw Int value
var unwrap = function (v) {
    return v;
};

// | Convert to Number for calculations
var toNumber = function (v) {
    return Data_Int.toNumber(v);
};
var showHue = {
    show: function (v) {
        return show(v) + "\xb0";
    }
};

// | Create a hue, wrapping values outside 0-359
// |
// | This is often what you want for rotations:
// | - `hueWrap 370` = `hue 10`
// | - `hueWrap (-30)` = `hue 330`
var hueWrap = function (n) {
    var mod$prime = function (a) {
        return function (b) {
            return mod(mod(a)(b) + b | 0)(b);
        };
    };
    return mod$prime(n)(360);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // operations
// ═══════════════════════════════════════════════════════════════════════════════
// | Rotate hue by degrees (wraps around)
var rotate = function (degrees$prime) {
    return function (v) {
        return hueWrap(v + degrees$prime | 0);
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // constructors
// ═══════════════════════════════════════════════════════════════════════════════
// | Create a hue, clamping to 0-359
var hue = function (n) {
    return Hydrogen_Schema_Bounded.clampInt(0)(359)(n);
};
var eqHue = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordHue = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqHue;
    }
};

// | Get complementary hue (opposite on color wheel)
var complement = /* #__PURE__ */ rotate(180);

// | Bounds documentation for this type
var bounds = /* #__PURE__ */ Hydrogen_Schema_Bounded.intBounds(0)(359)("hue")("Color wheel position in degrees");
export {
    hue,
    hueWrap,
    unwrap,
    rotate,
    complement,
    bounds,
    toNumber,
    eqHue,
    ordHue,
    showHue
};
