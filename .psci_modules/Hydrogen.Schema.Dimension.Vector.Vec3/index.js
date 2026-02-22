// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                              // hydrogen // schema // dimension // vector // 3d
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | 3D vector type parameterized by component type.
import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Ring from "../Data.Ring/index.js";
import * as Data_Semiring from "../Data.Semiring/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Hydrogen_Math_Core from "../Hydrogen.Math.Core/index.js";

// | 3D vector parameterized by component type
var Vec3 = /* #__PURE__ */ (function () {
    function Vec3(value0, value1, value2) {
        this.value0 = value0;
        this.value1 = value1;
        this.value2 = value2;
    };
    Vec3.create = function (value0) {
        return function (value1) {
            return function (value2) {
                return new Vec3(value0, value1, value2);
            };
        };
    };
    return Vec3;
})();

// | Zero vector
var vec3Zero = function (dictSemiring) {
    var zero = Data_Semiring.zero(dictSemiring);
    return new Vec3(zero, zero, zero);
};

// | Unit vector along Z axis
var vec3UnitZ = function (dictSemiring) {
    var zero = Data_Semiring.zero(dictSemiring);
    return new Vec3(zero, zero, Data_Semiring.one(dictSemiring));
};

// | Unit vector along Y axis
var vec3UnitY = function (dictSemiring) {
    var zero = Data_Semiring.zero(dictSemiring);
    return new Vec3(zero, Data_Semiring.one(dictSemiring), zero);
};

// | Unit vector along X axis
var vec3UnitX = function (dictSemiring) {
    var zero = Data_Semiring.zero(dictSemiring);
    return new Vec3(Data_Semiring.one(dictSemiring), zero, zero);
};

// | Unit vector (1,1,1)
var vec3One = function (dictSemiring) {
    var one = Data_Semiring.one(dictSemiring);
    return new Vec3(one, one, one);
};

// | Create a 3D vector
var vec3 = /* #__PURE__ */ (function () {
    return Vec3.create;
})();

// | Subtract two 3D vectors
var subtractVec3 = function (dictRing) {
    var sub = Data_Ring.sub(dictRing);
    return function (v) {
        return function (v1) {
            return new Vec3(sub(v.value0)(v1.value0), sub(v.value1)(v1.value1), sub(v.value2)(v1.value2));
        };
    };
};
var subtractVec31 = /* #__PURE__ */ subtractVec3(Data_Ring.ringNumber);
var showVec3 = function (dictShow) {
    var show = Data_Show.show(dictShow);
    return {
        show: function (v) {
            return "Vec3(" + (show(v.value0) + (", " + (show(v.value1) + (", " + (show(v.value2) + ")")))));
        }
    };
};

// | Set Z component
var setZ3 = function (z$prime) {
    return function (v) {
        return new Vec3(v.value0, v.value1, z$prime);
    };
};

// | Set Y component
var setY3 = function (y$prime) {
    return function (v) {
        return new Vec3(v.value0, y$prime, v.value2);
    };
};

// | Set X component
var setX3 = function (x$prime) {
    return function (v) {
        return new Vec3(x$prime, v.value1, v.value2);
    };
};

// | Scale a 3D vector by a scalar
var scaleVec3 = function (dictSemiring) {
    var mul1 = Data_Semiring.mul(dictSemiring);
    return function (s) {
        return function (v) {
            return new Vec3(mul1(s)(v.value0), mul1(s)(v.value1), mul1(s)(v.value2));
        };
    };
};
var scaleVec31 = /* #__PURE__ */ scaleVec3(Data_Semiring.semiringNumber);

// | Negate a 3D vector
var negateVec3 = function (dictRing) {
    var negate = Data_Ring.negate(dictRing);
    return function (v) {
        return new Vec3(negate(v.value0), negate(v.value1), negate(v.value2));
    };
};

// | Linear interpolation between two 3D vectors
var lerpVec3 = function (t) {
    return function (v) {
        return function (v1) {
            return new Vec3(Hydrogen_Math_Core.lerp(v.value0)(v1.value0)(t), Hydrogen_Math_Core.lerp(v.value1)(v1.value1)(t), Hydrogen_Math_Core.lerp(v.value2)(v1.value2)(t));
        };
    };
};

// | Get Z component
var getZ3 = function (v) {
    return v.value2;
};

// | Get Y component
var getY3 = function (v) {
    return v.value1;
};

// | Get X component
var getX3 = function (v) {
    return v.value0;
};
var functorVec3 = {
    map: function (f) {
        return function (v) {
            return new Vec3(f(v.value0), f(v.value1), f(v.value2));
        };
    }
};
var eqVec3 = function (dictEq) {
    var eq1 = Data_Eq.eq(dictEq);
    return {
        eq: function (x) {
            return function (y) {
                return eq1(x.value0)(y.value0) && eq1(x.value1)(y.value1) && eq1(x.value2)(y.value2);
            };
        }
    };
};

// | Dot product of two 3D vectors
var dotVec3 = function (dictSemiring) {
    var add = Data_Semiring.add(dictSemiring);
    var mul1 = Data_Semiring.mul(dictSemiring);
    return function (v) {
        return function (v1) {
            return add(add(mul1(v.value0)(v1.value0))(mul1(v.value1)(v1.value1)))(mul1(v.value2)(v1.value2));
        };
    };
};
var dotVec31 = /* #__PURE__ */ dotVec3(Data_Semiring.semiringNumber);

// | Squared length of a 3D Number vector
var lengthSquaredVec3 = function (v) {
    return dotVec31(v)(v);
};

// | Length of a 3D Number vector
var lengthVec3 = function (v) {
    return Hydrogen_Math_Core.sqrt(lengthSquaredVec3(v));
};

// | Normalize a 3D Number vector to unit length
var normalizeVec3 = function (v) {
    var len = lengthVec3(v);
    var $146 = len === 0.0;
    if ($146) {
        return v;
    };
    return scaleVec31(1.0 / len)(v);
};

// | Reflect a vector around a normal
var reflectVec3 = function (incident) {
    return function (normal) {
        var d = 2.0 * dotVec31(incident)(normal);
        return subtractVec31(incident)(scaleVec31(d)(normal));
    };
};

// | Distance between two 3D points
var distanceVec3 = function (a) {
    return function (b) {
        return lengthVec3(subtractVec31(b)(a));
    };
};

// | Cross product of two 3D vectors
var crossVec3 = function (dictRing) {
    var sub = Data_Ring.sub(dictRing);
    var mul1 = Data_Semiring.mul(dictRing.Semiring0());
    return function (v) {
        return function (v1) {
            return new Vec3(sub(mul1(v.value1)(v1.value2))(mul1(v.value2)(v1.value1)), sub(mul1(v.value2)(v1.value0))(mul1(v.value0)(v1.value2)), sub(mul1(v.value0)(v1.value1))(mul1(v.value1)(v1.value0)));
        };
    };
};

// | Add two 3D vectors
var addVec3 = function (dictSemiring) {
    var add = Data_Semiring.add(dictSemiring);
    return function (v) {
        return function (v1) {
            return new Vec3(add(v.value0)(v1.value0), add(v.value1)(v1.value1), add(v.value2)(v1.value2));
        };
    };
};
export {
    Vec3,
    vec3,
    vec3Zero,
    vec3One,
    vec3UnitX,
    vec3UnitY,
    vec3UnitZ,
    addVec3,
    subtractVec3,
    scaleVec3,
    negateVec3,
    dotVec3,
    crossVec3,
    lengthSquaredVec3,
    lengthVec3,
    normalizeVec3,
    distanceVec3,
    lerpVec3,
    reflectVec3,
    getX3,
    getY3,
    getZ3,
    setX3,
    setY3,
    setZ3,
    eqVec3,
    showVec3,
    functorVec3
};
