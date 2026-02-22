// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                              // hydrogen // schema // dimension // vector // nd
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | N-dimensional vector for arbitrary dimensions.
// |
// | Used for:
// | - Latent space embeddings (512, 768, 1024+ dimensions)
// | - Neural network activations
// | - High-dimensional optimization
// | - Color lookup tables
// |
// | Dimension is tracked at runtime.
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Foldable from "../Data.Foldable/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Ring from "../Data.Ring/index.js";
import * as Data_Semiring from "../Data.Semiring/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Hydrogen_Math_Core from "../Hydrogen.Math.Core/index.js";
var sub = /* #__PURE__ */ Data_Ring.sub(Data_Ring.ringNumber);
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);
var map = /* #__PURE__ */ Data_Functor.map(Data_Functor.functorArray);
var mul = /* #__PURE__ */ Data_Semiring.mul(Data_Semiring.semiringNumber);
var negate = /* #__PURE__ */ Data_Ring.negate(Data_Ring.ringNumber);
var sum = /* #__PURE__ */ Data_Foldable.sum(Data_Foldable.foldableArray)(Data_Semiring.semiringNumber);
var add = /* #__PURE__ */ Data_Semiring.add(Data_Semiring.semiringNumber);

// | N-dimensional vector
var VecN = function (x) {
    return x;
};

// | Create a zero vector of given dimension
var vecNZero = function (dim) {
    return Data_Array.replicate(dim)(0.0);
};

// | Convert to array
var vecNToArray = function (v) {
    return v;
};

// | Create from array
var vecNFromArray = VecN;

// | Create an N-dimensional vector from components
var vecN = VecN;

// | Subtract two N-dimensional vectors
var subtractVecN = function (v) {
    return function (v1) {
        return Data_Array.zipWith(sub)(v)(v1);
    };
};
var showVecN = function (dictShow) {
    return {
        show: function (v) {
            return "VecN[" + (show(Data_Array.length(v)) + "]");
        }
    };
};

// | Set component at index (0-based)
var setComponentN = function (idx) {
    return function (val) {
        return function (v) {
            return Data_Maybe.fromMaybe(v)(Data_Array.updateAt(idx)(val)(v));
        };
    };
};

// | Scale an N-dimensional vector
var scaleVecN = function (s) {
    return function (v) {
        return map(function (v1) {
            return v1 * s;
        })(v);
    };
};

// | Negate an N-dimensional vector
var negateVecN = function (v) {
    return map(negate)(v);
};

// | Linear interpolation between two N-dimensional vectors
var lerpVecN = function (t) {
    return function (v) {
        return function (v1) {
            return Data_Array.zipWith(function (x) {
                return function (y) {
                    return Hydrogen_Math_Core.lerp(x)(y)(t);
                };
            })(v)(v1);
        };
    };
};

// | Get component at index (0-based)
var getComponentN = function (idx) {
    return function (v) {
        return Data_Array.index(v)(idx);
    };
};
var functorVecN = {
    map: function (f) {
        return function (v) {
            return map(f)(v);
        };
    }
};
var eqVecN = function (dictEq) {
    var eq1 = Data_Eq.eq(Data_Eq.eqArray(dictEq));
    return {
        eq: function (x) {
            return function (y) {
                return eq1(x)(y);
            };
        }
    };
};

// | Dot product of two N-dimensional vectors
var dotVecN = function (v) {
    return function (v1) {
        return sum(Data_Array.zipWith(mul)(v)(v1));
    };
};

// | Squared length of an N-dimensional vector
var lengthSquaredVecN = function (v) {
    return dotVecN(v)(v);
};

// | Length of an N-dimensional vector
var lengthVecN = function (v) {
    return Hydrogen_Math_Core.sqrt(lengthSquaredVecN(v));
};

// | Normalize an N-dimensional vector
var normalizeVecN = function (v) {
    var len = lengthVecN(v);
    var $57 = len === 0.0;
    if ($57) {
        return v;
    };
    return scaleVecN(1.0 / len)(v);
};

// | Distance between two N-dimensional points
var distanceVecN = function (a) {
    return function (b) {
        return lengthVecN(subtractVecN(b)(a));
    };
};

// | Get dimension of vector
var dimVecN = function (v) {
    return Data_Array.length(v);
};

// | Add two N-dimensional vectors
var addVecN = function (v) {
    return function (v1) {
        return Data_Array.zipWith(add)(v)(v1);
    };
};
export {
    VecN,
    vecN,
    vecNZero,
    vecNFromArray,
    vecNToArray,
    dimVecN,
    addVecN,
    subtractVecN,
    scaleVecN,
    negateVecN,
    dotVecN,
    lengthSquaredVecN,
    lengthVecN,
    normalizeVecN,
    distanceVecN,
    lerpVecN,
    getComponentN,
    setComponentN,
    eqVecN,
    showVecN,
    functorVecN
};
