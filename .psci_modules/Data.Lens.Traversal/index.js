// | `Traversal` is an optic that focuses on zero or more values. An
// | `Array` would be a typical example:
// |
// | ```purescript
// | over    traversed negate [1, 2, 3] == [-1, -2, -3]
// | preview traversed [1, 2, 3] == Just 1
// | firstOf traversed [1, 2, 3] == Just 1  -- same as `preview`
// | lastOf  traversed [1, 2, 3] == Just 3
// | ```
// |
// | `view` might surprise you. It assumes that the wrapped values
// | are a monoid, and `append`s them together:
// |
// | ```purescript
// | view traversed ["D", "a", "w", "n"] == "Dawn"
// | ```
// |
// | Many of the functions you'll use are documented in `Data.Lens.Fold`.
import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Control_Bind from "../Control.Bind/index.js";
import * as Control_Category from "../Control.Category/index.js";
import * as Control_Plus from "../Control.Plus/index.js";
import * as Data_Bitraversable from "../Data.Bitraversable/index.js";
import * as Data_Function from "../Data.Function/index.js";
import * as Data_Lens_Indexed from "../Data.Lens.Indexed/index.js";
import * as Data_Lens_Internal_Bazaar from "../Data.Lens.Internal.Bazaar/index.js";
import * as Data_Lens_Internal_Indexed from "../Data.Lens.Internal.Indexed/index.js";
import * as Data_Lens_Internal_Wander from "../Data.Lens.Internal.Wander/index.js";
import * as Data_Lens_Types from "../Data.Lens.Types/index.js";
import * as Data_Newtype from "../Data.Newtype/index.js";
import * as Data_Profunctor_Star from "../Data.Profunctor.Star/index.js";
import * as Data_Traversable from "../Data.Traversable/index.js";
import * as Data_Tuple from "../Data.Tuple/index.js";
var under = /* #__PURE__ */ Data_Newtype.under()();
var identity = /* #__PURE__ */ Control_Category.identity(Control_Category.categoryFn);
var unwrap = /* #__PURE__ */ Data_Newtype.unwrap();
var join = /* #__PURE__ */ Control_Bind.join(Control_Bind.bindFn);

// | A `Traversal` for the elements of a `Traversable` functor.
// |
// | ```purescript
// | over traversed negate [1, 2, 3] == [-1,-2,-3]
// | over traversed negate (Just 3) == Just -3
// | ```
var traversed = function (dictTraversable) {
    var traverse = Data_Traversable.traverse(dictTraversable);
    return function (dictWander) {
        return Data_Lens_Internal_Wander.wander(dictWander)(function (dictApplicative) {
            return traverse(dictApplicative);
        });
    };
};

// | Turn a pure profunctor `Traversal` into a `lens`-like `Traversal`.
var traverseOf = /* #__PURE__ */ under(Data_Profunctor_Star.Star);

// | Sequence the foci of an optic, pulling out an "effect".
// | If you do not need the result, see `sequenceOf_` for `Fold`s.
// |
// | `sequenceOf traversed` has the same result as `Data.Traversable.sequence`:
// |
// | ```purescript
// | sequenceOf traversed (Just [1, 2]) == [Just 1, Just 2]
// | sequence             (Just [1, 2]) == [Just 1, Just 2]
// | ```
// |
// | An example with effects:
// | ```purescript
// | > array = [random, random]
// | > :t array
// | Array (Eff ... Number)
// |
// | > effect = sequenceOf traversed array
// | > :t effect
// | Eff ... (Array Number)
// |
// | > effect >>= logShow
// | [0.15556037108154985,0.28500369615270515]
// | unit
// | ```
var sequenceOf = function (t) {
    return traverseOf(t)(identity);
};

// | Turn a pure profunctor `IndexedTraversal` into a `lens`-like `IndexedTraversal`.
var itraverseOf = function (t) {
    var $53 = under(Data_Profunctor_Star.Star)(function ($55) {
        return t(Data_Lens_Internal_Indexed.Indexed($55));
    });
    return function ($54) {
        return $53(Data_Tuple.uncurry($54));
    };
};

// | Flipped version of `itraverseOf`.
var iforOf = function ($56) {
    return Data_Function.flip(itraverseOf($56));
};

// | Tries to map over a `Traversal`; returns `empty` if the traversal did
// | not have any new focus.
var failover = function (dictAlternative) {
    var pure = Control_Applicative.pure(dictAlternative.Applicative0());
    var empty = Control_Plus.empty(dictAlternative.Plus1());
    return function (t) {
        return function (f) {
            return function (s) {
                var v = unwrap(t((function () {
                    var $57 = Data_Tuple.Tuple.create(true);
                    return function ($58) {
                        return $57(f($58));
                    };
                })()))(s);
                if (v.value0) {
                    return pure(v.value1);
                };
                if (!v.value0) {
                    return empty;
                };
                throw new Error("Failed pattern match at Data.Lens.Traversal (line 98, column 18 - line 100, column 32): " + [ v.constructor.name ]);
            };
        };
    };
};

// | Traverse elements of an `IndexedTraversal` whose index satisfy a predicate.
var elementsOf = function (dictWander) {
    return function (tr) {
        return function (pr) {
            return Data_Lens_Indexed.iwander(function (dictApplicative) {
                var tr1 = tr(Data_Lens_Internal_Wander.wanderStar(dictApplicative));
                var pure = Control_Applicative.pure(dictApplicative);
                return function (f) {
                    return unwrap(tr1(function (v) {
                        var $50 = pr(v.value0);
                        if ($50) {
                            return f(v.value0)(v.value1);
                        };
                        return pure(v.value1);
                    }));
                };
            })(dictWander);
        };
    };
};

// | Combine an index and a traversal to narrow the focus to a single
// | element. Compare to `Data.Lens.Index`.
// |
// | ```purescript
// | set     (element 2 traversed) 8888 [0, 0, 3] == [0, 0, 8888]
// | preview (element 2 traversed)      [0, 0, 3] == Just 3
// | ```
// | The resulting traversal is called an *affine traversal*, which
// | means that the traversal focuses on one or zero (if the index is out of range)
// | results.
var element = function (dictWander) {
    var unIndex = Data_Lens_Indexed.unIndex((dictWander.Choice1()).Profunctor0());
    var elementsOf1 = elementsOf(dictWander);
    return function (n) {
        return function (tr) {
            return unIndex(elementsOf1(function (dictWander1) {
                return Data_Lens_Indexed.positions(function (dictWander2) {
                    return tr(dictWander2);
                })(dictWander1);
            })(function (v) {
                return v === n;
            }));
        };
    };
};
var cloneTraversal = function (l) {
    return function (dictWander) {
        return Data_Lens_Internal_Wander.wander(dictWander)(function (dictApplicative) {
            return Data_Lens_Internal_Bazaar.runBazaar(l(function (dictApplicative1) {
                return identity;
            }))(dictApplicative);
        });
    };
};
var both = function (dictBitraversable) {
    var bitraverse = Data_Bitraversable.bitraverse(dictBitraversable);
    return function (dictWander) {
        return Data_Lens_Internal_Wander.wander(dictWander)(function (dictApplicative) {
            return join(bitraverse(dictApplicative));
        });
    };
};
export {
    traversed,
    element,
    traverseOf,
    sequenceOf,
    failover,
    elementsOf,
    itraverseOf,
    iforOf,
    cloneTraversal,
    both
};
