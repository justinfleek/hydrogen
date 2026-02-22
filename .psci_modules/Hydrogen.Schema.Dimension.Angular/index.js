// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                  // hydrogen // schema // dimension // angular
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Angular units - measurements of rotation and direction.
// |
// | Used for:
// | - Rotation in 2D/3D transforms
// | - Camera field of view
// | - Hue in color wheels (0-360)
// | - Latitude/longitude
// | - Circular gradients
// |
// | ## Base Unit
// |
// | The base unit is **Radians** (mathematically natural, used by trig functions).
// | All other units convert through radians.
// |
// | ## Full Circle
// |
// | - 2π radians = 360 degrees = 1 turn = 400 gradians
import * as Control_Category from "../Control.Category/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Hydrogen_Math_Core from "../Hydrogen.Math.Core/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showNumber);
var compare = /* #__PURE__ */ Data_Ord.compare(Data_Ord.ordNumber);
var identity = /* #__PURE__ */ Control_Category.identity(Control_Category.categoryFn);

// | Turns - intuitive unit for rotations
// | Full circle = 1 turn
// | Half rotation = 0.5 turns
var Turns = function (x) {
    return x;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // core types
// ═══════════════════════════════════════════════════════════════════════════════
// | Radians - natural unit for trigonometry
// | Full circle = 2π radians ≈ 6.283185...
// | Used directly by sin, cos, tan, etc.
var Radians = function (x) {
    return x;
};

// | Gradians (gon) - used in surveying
// | Full circle = 400 gradians
// | Right angle = 100 gradians
var Gradians = function (x) {
    return x;
};

// | Degrees - common unit for human-readable angles
// | Full circle = 360 degrees
// | Right angle = 90 degrees
var Degrees = function (x) {
    return x;
};

// | Extract the raw Number from Turns
var unwrapTurns = function (v) {
    return v;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // accessors
// ═══════════════════════════════════════════════════════════════════════════════
// | Extract the raw Number from Radians
var unwrapRadians = function (v) {
    return v;
};

// | Extract the raw Number from Gradians
var unwrapGradians = function (v) {
    return v;
};

// | Extract the raw Number from Degrees
var unwrapDegrees = function (v) {
    return v;
};

// | Create a Turns value
var turns = Turns;

// | Alias for turns (singular)
var turn = Turns;
var toRadians = function (dict) {
    return dict.toRadians;
};

// | Subtract two Radians values
var subtractRadians = function (v) {
    return function (v1) {
        return v - v1;
    };
};

// | 180 degrees (π radians)
var straightAngle = Hydrogen_Math_Core.pi;
var showTurns = {
    show: function (v) {
        return show(v) + " turn";
    }
};
var showRadians = {
    show: function (v) {
        return show(v) + " rad";
    }
};
var showGradians = {
    show: function (v) {
        return show(v) + " grad";
    }
};
var showDegrees = {
    show: function (v) {
        return show(v) + "\xb0";
    }
};
var semiringRadians = {
    add: function (v) {
        return function (v1) {
            return v + v1;
        };
    },
    zero: 0.0,
    mul: function (v) {
        return function (v1) {
            return v * v1;
        };
    },
    one: 1.0
};
var semiringDegrees = {
    add: function (v) {
        return function (v1) {
            return v + v1;
        };
    },
    zero: 0.0,
    mul: function (v) {
        return function (v1) {
            return v * v1;
        };
    },
    one: 1.0
};

// | Scale a Radians value by a dimensionless factor
var scaleRadians = function (factor) {
    return function (v) {
        return v * factor;
    };
};
var ringRadians = {
    sub: function (v) {
        return function (v1) {
            return v - v1;
        };
    },
    Semiring0: function () {
        return semiringRadians;
    }
};
var ringDegrees = {
    sub: function (v) {
        return function (v1) {
            return v - v1;
        };
    },
    Semiring0: function () {
        return semiringDegrees;
    }
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // common angles
// ═══════════════════════════════════════════════════════════════════════════════
// | 90 degrees (π/2 radians)
var rightAngle = /* #__PURE__ */ (function () {
    return Hydrogen_Math_Core.pi / 2.0;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // constructors
// ═══════════════════════════════════════════════════════════════════════════════
// | Create a Radians value
var radians = Radians;

// | Alias for radians
var rad = Radians;

// | 0.25 turns (90 degrees)
var quarterTurn = 0.25;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // normalization
// ═══════════════════════════════════════════════════════════════════════════════
// | Normalize radians to [0, 2π)
var normalizeRadians = function (v) {
    var modded = v - Hydrogen_Math_Core.floor(v / Hydrogen_Math_Core.tau) * Hydrogen_Math_Core.tau;
    var $109 = modded < 0.0;
    if ($109) {
        return modded + Hydrogen_Math_Core.tau;
    };
    return modded;
};

// | Normalize degrees to [0, 360)
var normalizeDegrees = function (v) {
    var modded = v - Hydrogen_Math_Core.floor(v / 360.0) * 360.0;
    var $111 = modded < 0.0;
    if ($111) {
        return modded + 360.0;
    };
    return modded;
};

// | Negate a Radians value
var negateRadians = function (v) {
    return -v;
};

// | 0.5 turns (180 degrees)
var halfTurn = 0.5;

// | Create a Gradians value
var gradians = Gradians;

// | Alias for gradians
var grad = Gradians;

// | 360 degrees (2π radians)
var fullRotation = Hydrogen_Math_Core.tau;
var fromRadians = function (dict) {
    return dict.fromRadians;
};
var eqTurns = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordTurns = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqTurns;
    }
};
var eqRadians = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordRadians = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqRadians;
    }
};
var eqGradians = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordGradians = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqGradians;
    }
};
var eqDegrees = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordDegrees = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqDegrees;
    }
};

// | Create a Degrees value
var degrees = Degrees;

// | Alias for degrees
var deg = Degrees;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // conversions
// ═══════════════════════════════════════════════════════════════════════════════
// | Convert between any two angular units
var convertAngle = function (dictAngularUnit) {
    var toRadians1 = toRadians(dictAngularUnit);
    return function (dictAngularUnit1) {
        var $139 = fromRadians(dictAngularUnit1);
        return function ($140) {
            return $139(toRadians1($140));
        };
    };
};

// 1 turn = 2π radians
var angularUnitTurns = {
    toRadians: function (v) {
        return v * Hydrogen_Math_Core.tau;
    },
    fromRadians: function (v) {
        return v / Hydrogen_Math_Core.tau;
    }
};
var angularUnitRadians = {
    toRadians: identity,
    fromRadians: identity
};

// 400 gradians = 2π radians
// 1 gradian = π/200 radians
var angularUnitGradians = {
    toRadians: function (v) {
        return (v * Hydrogen_Math_Core.pi) / 200.0;
    },
    fromRadians: function (v) {
        return (v * 200.0) / Hydrogen_Math_Core.pi;
    }
};

// 360 degrees = 2π radians
// 1 degree = π/180 radians
var angularUnitDegrees = {
    toRadians: function (v) {
        return (v * Hydrogen_Math_Core.pi) / 180.0;
    },
    fromRadians: function (v) {
        return (v * 180.0) / Hydrogen_Math_Core.pi;
    }
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // operations
// ═══════════════════════════════════════════════════════════════════════════════
// | Add two Radians values
var addRadians = function (v) {
    return function (v1) {
        return v + v1;
    };
};

// | Absolute value of Radians
var absRadians = function (v) {
    return Hydrogen_Math_Core.abs(v);
};
export {
    Radians,
    Degrees,
    Turns,
    Gradians,
    toRadians,
    fromRadians,
    radians,
    rad,
    degrees,
    deg,
    turns,
    turn,
    gradians,
    grad,
    convertAngle,
    addRadians,
    subtractRadians,
    scaleRadians,
    negateRadians,
    absRadians,
    normalizeRadians,
    normalizeDegrees,
    rightAngle,
    straightAngle,
    fullRotation,
    halfTurn,
    quarterTurn,
    unwrapRadians,
    unwrapDegrees,
    unwrapTurns,
    unwrapGradians,
    eqRadians,
    ordRadians,
    showRadians,
    semiringRadians,
    ringRadians,
    eqDegrees,
    ordDegrees,
    showDegrees,
    semiringDegrees,
    ringDegrees,
    eqTurns,
    ordTurns,
    showTurns,
    eqGradians,
    ordGradians,
    showGradians,
    angularUnitRadians,
    angularUnitDegrees,
    angularUnitTurns,
    angularUnitGradians
};
