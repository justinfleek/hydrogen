// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                              // hydrogen // schema // dimension // vector // 4d
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | 4D vector type parameterized by component type.
// | Used for homogeneous coordinates and quaternions.
import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Ring from "../Data.Ring/index.js";
import * as Data_Semiring from "../Data.Semiring/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Hydrogen_Math_Core from "../Hydrogen.Math.Core/index.js";

// | 4D vector parameterized by component type
var Vec4 = /* #__PURE__ */ (function () {
    function Vec4(value0, value1, value2, value3) {
        this.value0 = value0;
        this.value1 = value1;
        this.value2 = value2;
        this.value3 = value3;
    };
    Vec4.create = function (value0) {
        return function (value1) {
            return function (value2) {
                return function (value3) {
                    return new Vec4(value0, value1, value2, value3);
                };
            };
        };
    };
    return Vec4;
})();

// | Zero vector
var vec4Zero = function (dictSemiring) {
    var zero = Data_Semiring.zero(dictSemiring);
    return new Vec4(zero, zero, zero, zero);
};

// | Unit vector (1,1,1,1)
var vec4One = function (dictSemiring) {
    var one = Data_Semiring.one(dictSemiring);
    return new Vec4(one, one, one, one);
};

// | Create a 4D vector
var vec4 = /* #__PURE__ */ (function () {
    return Vec4.create;
})();

// | Subtract two 4D vectors
var subtractVec4 = function (dictRing) {
    var sub = Data_Ring.sub(dictRing);
    return function (v) {
        return function (v1) {
            return new Vec4(sub(v.value0)(v1.value0), sub(v.value1)(v1.value1), sub(v.value2)(v1.value2), sub(v.value3)(v1.value3));
        };
    };
};
var showVec4 = function (dictShow) {
    var show = Data_Show.show(dictShow);
    return {
        show: function (v) {
            return "Vec4(" + (show(v.value0) + (", " + (show(v.value1) + (", " + (show(v.value2) + (", " + (show(v.value3) + ")")))))));
        }
    };
};

// | Set Z component
var setZ4 = function (z$prime) {
    return function (v) {
        return new Vec4(v.value0, v.value1, z$prime, v.value3);
    };
};

// | Set Y component
var setY4 = function (y$prime) {
    return function (v) {
        return new Vec4(v.value0, y$prime, v.value2, v.value3);
    };
};

// | Set X component
var setX4 = function (x$prime) {
    return function (v) {
        return new Vec4(x$prime, v.value1, v.value2, v.value3);
    };
};

// | Set W component
var setW4 = function (w$prime) {
    return function (v) {
        return new Vec4(v.value0, v.value1, v.value2, w$prime);
    };
};

// | Scale a 4D vector by a scalar
var scaleVec4 = function (dictSemiring) {
    var mul = Data_Semiring.mul(dictSemiring);
    return function (s) {
        return function (v) {
            return new Vec4(mul(s)(v.value0), mul(s)(v.value1), mul(s)(v.value2), mul(s)(v.value3));
        };
    };
};
var scaleVec41 = /* #__PURE__ */ scaleVec4(Data_Semiring.semiringNumber);

// | Negate a 4D vector
var negateVec4 = function (dictRing) {
    var negate = Data_Ring.negate(dictRing);
    return function (v) {
        return new Vec4(negate(v.value0), negate(v.value1), negate(v.value2), negate(v.value3));
    };
};

// | Linear interpolation between two 4D vectors
var lerpVec4 = function (t) {
    return function (v) {
        return function (v1) {
            return new Vec4(Hydrogen_Math_Core.lerp(v.value0)(v1.value0)(t), Hydrogen_Math_Core.lerp(v.value1)(v1.value1)(t), Hydrogen_Math_Core.lerp(v.value2)(v1.value2)(t), Hydrogen_Math_Core.lerp(v.value3)(v1.value3)(t));
        };
    };
};

// | Get Z component
var getZ4 = function (v) {
    return v.value2;
};

// | Get Y component
var getY4 = function (v) {
    return v.value1;
};

// | Get X component
var getX4 = function (v) {
    return v.value0;
};

// | Get W component
var getW4 = function (v) {
    return v.value3;
};
var functorVec4 = {
    map: function (f) {
        return function (v) {
            return new Vec4(f(v.value0), f(v.value1), f(v.value2), f(v.value3));
        };
    }
};
var eqVec4 = function (dictEq) {
    var eq1 = Data_Eq.eq(dictEq);
    return {
        eq: function (x) {
            return function (y) {
                return eq1(x.value0)(y.value0) && eq1(x.value1)(y.value1) && eq1(x.value2)(y.value2) && eq1(x.value3)(y.value3);
            };
        }
    };
};

// | Dot product of two 4D vectors
var dotVec4 = function (dictSemiring) {
    var add = Data_Semiring.add(dictSemiring);
    var mul = Data_Semiring.mul(dictSemiring);
    return function (v) {
        return function (v1) {
            return add(add(add(mul(v.value0)(v1.value0))(mul(v.value1)(v1.value1)))(mul(v.value2)(v1.value2)))(mul(v.value3)(v1.value3));
        };
    };
};
var dotVec41 = /* #__PURE__ */ dotVec4(Data_Semiring.semiringNumber);

// | Squared length of a 4D Number vector
var lengthSquaredVec4 = function (v) {
    return dotVec41(v)(v);
};

// | Length of a 4D Number vector
var lengthVec4 = function (v) {
    return Hydrogen_Math_Core.sqrt(lengthSquaredVec4(v));
};

// | Normalize a 4D Number vector to unit length
var normalizeVec4 = function (v) {
    var len = lengthVec4(v);
    var $162 = len === 0.0;
    if ($162) {
        return v;
    };
    return scaleVec41(1.0 / len)(v);
};

// | Add two 4D vectors
var addVec4 = function (dictSemiring) {
    var add = Data_Semiring.add(dictSemiring);
    return function (v) {
        return function (v1) {
            return new Vec4(add(v.value0)(v1.value0), add(v.value1)(v1.value1), add(v.value2)(v1.value2), add(v.value3)(v1.value3));
        };
    };
};
export {
    Vec4,
    vec4,
    vec4Zero,
    vec4One,
    addVec4,
    subtractVec4,
    scaleVec4,
    negateVec4,
    dotVec4,
    lengthSquaredVec4,
    lengthVec4,
    normalizeVec4,
    lerpVec4,
    getX4,
    getY4,
    getZ4,
    getW4,
    setX4,
    setY4,
    setZ4,
    setW4,
    eqVec4,
    showVec4,
    functorVec4
};
