// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                              // hydrogen // schema // dimension // vector // 2d
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | 2D vector type parameterized by component type.
import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Ring from "../Data.Ring/index.js";
import * as Data_Semiring from "../Data.Semiring/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Hydrogen_Math_Core from "../Hydrogen.Math.Core/index.js";

// | 2D vector parameterized by component type
var Vec2 = /* #__PURE__ */ (function () {
    function Vec2(value0, value1) {
        this.value0 = value0;
        this.value1 = value1;
    };
    Vec2.create = function (value0) {
        return function (value1) {
            return new Vec2(value0, value1);
        };
    };
    return Vec2;
})();

// | Zero vector
var vec2Zero = function (dictSemiring) {
    var zero = Data_Semiring.zero(dictSemiring);
    return new Vec2(zero, zero);
};

// | Unit vector along Y axis
var vec2UnitY = function (dictSemiring) {
    return new Vec2(Data_Semiring.zero(dictSemiring), Data_Semiring.one(dictSemiring));
};

// | Unit vector along X axis
var vec2UnitX = function (dictSemiring) {
    return new Vec2(Data_Semiring.one(dictSemiring), Data_Semiring.zero(dictSemiring));
};

// | Unit vector (1,1)
var vec2One = function (dictSemiring) {
    var one = Data_Semiring.one(dictSemiring);
    return new Vec2(one, one);
};

// | Create a 2D vector
var vec2 = /* #__PURE__ */ (function () {
    return Vec2.create;
})();

// | Subtract two 2D vectors
var subtractVec2 = function (dictRing) {
    var sub = Data_Ring.sub(dictRing);
    return function (v) {
        return function (v1) {
            return new Vec2(sub(v.value0)(v1.value0), sub(v.value1)(v1.value1));
        };
    };
};
var subtractVec21 = /* #__PURE__ */ subtractVec2(Data_Ring.ringNumber);
var showVec2 = function (dictShow) {
    var show = Data_Show.show(dictShow);
    return {
        show: function (v) {
            return "Vec2(" + (show(v.value0) + (", " + (show(v.value1) + ")")));
        }
    };
};

// | Set Y component
var setY2 = function (y$prime) {
    return function (v) {
        return new Vec2(v.value0, y$prime);
    };
};

// | Set X component
var setX2 = function (x$prime) {
    return function (v) {
        return new Vec2(x$prime, v.value1);
    };
};

// | Scale a 2D vector by a scalar
var scaleVec2 = function (dictSemiring) {
    var mul = Data_Semiring.mul(dictSemiring);
    return function (s) {
        return function (v) {
            return new Vec2(mul(s)(v.value0), mul(s)(v.value1));
        };
    };
};
var scaleVec21 = /* #__PURE__ */ scaleVec2(Data_Semiring.semiringNumber);

// | Perpendicular vector (rotated 90 degrees counter-clockwise)
var perpendicularVec2 = function (dictRing) {
    var negate = Data_Ring.negate(dictRing);
    return function (v) {
        return new Vec2(negate(v.value1), v.value0);
    };
};

// | Negate a 2D vector
var negateVec2 = function (dictRing) {
    var negate = Data_Ring.negate(dictRing);
    return function (v) {
        return new Vec2(negate(v.value0), negate(v.value1));
    };
};

// | Linear interpolation between two 2D vectors
var lerpVec2 = function (t) {
    return function (v) {
        return function (v1) {
            return new Vec2(Hydrogen_Math_Core.lerp(v.value0)(v1.value0)(t), Hydrogen_Math_Core.lerp(v.value1)(v1.value1)(t));
        };
    };
};

// | Get Y component
var getY2 = function (v) {
    return v.value1;
};

// | Get X component
var getX2 = function (v) {
    return v.value0;
};
var functorVec2 = {
    map: function (f) {
        return function (v) {
            return new Vec2(f(v.value0), f(v.value1));
        };
    }
};
var eqVec2 = function (dictEq) {
    var eq1 = Data_Eq.eq(dictEq);
    return {
        eq: function (x) {
            return function (y) {
                return eq1(x.value0)(y.value0) && eq1(x.value1)(y.value1);
            };
        }
    };
};

// | Dot product of two 2D vectors
var dotVec2 = function (dictSemiring) {
    var add = Data_Semiring.add(dictSemiring);
    var mul = Data_Semiring.mul(dictSemiring);
    return function (v) {
        return function (v1) {
            return add(mul(v.value0)(v1.value0))(mul(v.value1)(v1.value1));
        };
    };
};
var dotVec21 = /* #__PURE__ */ dotVec2(Data_Semiring.semiringNumber);

// | Squared length of a 2D Number vector
var lengthSquaredVec2 = function (v) {
    return dotVec21(v)(v);
};

// | Length of a 2D Number vector
var lengthVec2 = function (v) {
    return Hydrogen_Math_Core.sqrt(lengthSquaredVec2(v));
};

// | Normalize a 2D Number vector to unit length
var normalizeVec2 = function (v) {
    var len = lengthVec2(v);
    var $114 = len === 0.0;
    if ($114) {
        return v;
    };
    return scaleVec21(1.0 / len)(v);
};

// | Distance between two 2D points
var distanceVec2 = function (a) {
    return function (b) {
        return lengthVec2(subtractVec21(b)(a));
    };
};

// | Angle of a 2D vector in radians
var angleVec2 = function (v) {
    return Hydrogen_Math_Core.atan2(v.value1)(v.value0);
};

// | Add two 2D vectors
var addVec2 = function (dictSemiring) {
    var add = Data_Semiring.add(dictSemiring);
    return function (v) {
        return function (v1) {
            return new Vec2(add(v.value0)(v1.value0), add(v.value1)(v1.value1));
        };
    };
};
export {
    Vec2,
    vec2,
    vec2Zero,
    vec2One,
    vec2UnitX,
    vec2UnitY,
    addVec2,
    subtractVec2,
    scaleVec2,
    negateVec2,
    dotVec2,
    lengthSquaredVec2,
    lengthVec2,
    normalizeVec2,
    distanceVec2,
    lerpVec2,
    perpendicularVec2,
    angleVec2,
    getX2,
    getY2,
    setX2,
    setY2,
    eqVec2,
    showVec2,
    functorVec2
};
