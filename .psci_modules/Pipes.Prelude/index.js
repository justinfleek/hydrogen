import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Control_Bind from "../Control.Bind/index.js";
import * as Control_Category from "../Control.Category/index.js";
import * as Control_Monad from "../Control.Monad/index.js";
import * as Control_Monad_Trans_Class from "../Control.Monad.Trans.Class/index.js";
import * as Data_Boolean from "../Data.Boolean/index.js";
import * as Data_Either from "../Data.Either/index.js";
import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_HeytingAlgebra from "../Data.HeytingAlgebra/index.js";
import * as Data_List_Types from "../Data.List.Types/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Newtype from "../Data.Newtype/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Data_Tuple from "../Data.Tuple/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
import * as Pipes from "../Pipes/index.js";
import * as Pipes_Internal from "../Pipes.Internal/index.js";
var $runtime_lazy = function (name, moduleName, init) {
    var state = 0;
    var val;
    return function (lineNumber) {
        if (state === 2) return val;
        if (state === 1) throw new ReferenceError(name + " was needed before it finished initializing (module " + moduleName + ", line " + lineNumber + ")", moduleName, lineNumber);
        state = 1;
        val = init();
        state = 2;
        return val;
    };
};
var unwrap = /* #__PURE__ */ Data_Newtype.unwrap();
var discard = /* #__PURE__ */ Control_Bind.discard(Control_Bind.discardUnit);
var lift = /* #__PURE__ */ Control_Monad_Trans_Class.lift(Pipes_Internal.monadTransProxy);
var identity = /* #__PURE__ */ Control_Category.identity(Control_Category.categoryFn);
var not = /* #__PURE__ */ Data_HeytingAlgebra.not(Data_HeytingAlgebra.heytingAlgebraBoolean);

// | Convert a pure `Producer` into a list
var toList = function (prod0) {
    var go = function (prod) {
        return function (v) {
            return function (nil) {
                if (prod instanceof Pipes_Internal.Request) {
                    return Pipes_Internal.closed(prod.value0);
                };
                if (prod instanceof Pipes_Internal.Respond) {
                    return new Data_List_Types.Cons(prod.value0, go(prod.value1(Data_Unit.unit))(Data_List_Types.Cons.create)(nil));
                };
                if (prod instanceof Pipes_Internal.M) {
                    return go(unwrap(prod.value0))(Data_List_Types.Cons.create)(nil);
                };
                if (prod instanceof Pipes_Internal.Pure) {
                    return nil;
                };
                throw new Error("Failed pattern match at Pipes.Prelude (line 354, column 7 - line 358, column 28): " + [ prod.constructor.name ]);
            };
        };
    };
    return go(prod0)(Data_List_Types.Cons.create)(Data_List_Types.Nil.value);
};

/**
 * | `takeWhile'` is a version of `takeWhile` that returns the value failing
 *     the predicate.
 */
var takeWhile$prime = function (dictMonad) {
    var bindProxy = Pipes_Internal.bindProxy(dictMonad);
    var bind = Control_Bind.bind(bindProxy);
    var $$await = Pipes["await"](dictMonad);
    var discard1 = discard(bindProxy);
    var $$yield = Pipes["yield"](dictMonad);
    var pure = Control_Applicative.pure(Pipes_Internal.applicativeProxy(dictMonad));
    return function (predicate) {
        var $lazy_go = $runtime_lazy("go", "Pipes.Prelude", function () {
            return bind($$await)(function (a) {
                var $233 = predicate(a);
                if ($233) {
                    return discard1($$yield(a))(function () {
                        return $lazy_go(112);
                    });
                };
                return pure(a);
            });
        });
        var go = $lazy_go(107);
        return go;
    };
};

/**
 * | `takeWhile` allows values to pass downstream so long as they satisfy
 *     the predicate `p`.
 */
var takeWhile = function (dictMonad) {
    var bindProxy = Pipes_Internal.bindProxy(dictMonad);
    var bind = Control_Bind.bind(bindProxy);
    var $$await = Pipes["await"](dictMonad);
    var discard1 = discard(bindProxy);
    var $$yield = Pipes["yield"](dictMonad);
    var pure = Control_Applicative.pure(Pipes_Internal.applicativeProxy(dictMonad));
    return function (predicate) {
        var $lazy_go = $runtime_lazy("go", "Pipes.Prelude", function () {
            return bind($$await)(function (a) {
                var $234 = predicate(a);
                if ($234) {
                    return discard1($$yield(a))(function () {
                        return $lazy_go(98);
                    });
                };
                return pure(Data_Unit.unit);
            });
        });
        var go = $lazy_go(93);
        return go;
    };
};

// | `take n` only allows n values to pass through
var take = function (dictMonad) {
    var pure = Control_Applicative.pure(Pipes_Internal.applicativeProxy(dictMonad));
    var bindProxy = Pipes_Internal.bindProxy(dictMonad);
    var bind = Control_Bind.bind(bindProxy);
    var $$await = Pipes["await"](dictMonad);
    var discard1 = discard(bindProxy);
    var $$yield = Pipes["yield"](dictMonad);
    var loop = function (v) {
        if (v === 0) {
            return pure(Data_Unit.unit);
        };
        return bind($$await)(function (a) {
            return discard1($$yield(a))(function () {
                return loop(v - 1 | 0);
            });
        });
    };
    return loop;
};

// | Evaluate all values flowing downstream to WHNF
// | XXX: Is this needed in purescript?
var seq = function (dictMonad) {
    var $$yield = Pipes["yield"](dictMonad);
    return Pipes["for"](dictMonad)(Pipes.cat(dictMonad))(function (a) {
        return $$yield(a);
    });
};

// | Monadic left scan
var scanM = function (dictMonad) {
    var bindProxy = Pipes_Internal.bindProxy(dictMonad);
    var bind = Control_Bind.bind(bindProxy);
    var lift1 = lift(dictMonad);
    var discard1 = discard(bindProxy);
    var $$yield = Pipes["yield"](dictMonad);
    var $$await = Pipes["await"](dictMonad);
    return function (step) {
        return function (begin) {
            return function (done) {
                var go = function (x) {
                    return bind(lift1(done(x)))(function (b) {
                        return discard1($$yield(b))(function () {
                            return bind($$await)(function (a) {
                                return bind(lift1(step(x)(a)))(function (x$prime) {
                                    return go(x$prime);
                                });
                            });
                        });
                    });
                };
                return bind(lift1(begin))(function (x) {
                    return go(x);
                });
            };
        };
    };
};

// | Left scan
var scan = function (dictMonad) {
    var bindProxy = Pipes_Internal.bindProxy(dictMonad);
    var discard1 = discard(bindProxy);
    var $$yield = Pipes["yield"](dictMonad);
    var bind = Control_Bind.bind(bindProxy);
    var $$await = Pipes["await"](dictMonad);
    return function (step) {
        return function (begin) {
            return function (done) {
                var go = function (x) {
                    return discard1($$yield(done(x)))(function () {
                        return bind($$await)(function (a) {
                            var x$prime = step(x)(a);
                            return go(x$prime);
                        });
                    });
                };
                return go(begin);
            };
        };
    };
};

// | Repeat a monadic action a fixed number of times, `yield`ing each result
var replicateM = function (dictMonad) {
    var replaceAwait = Pipes.replaceAwait(dictMonad);
    var lift1 = lift(dictMonad);
    var take1 = take(dictMonad);
    return function (n) {
        return function (m) {
            return replaceAwait(lift1(m))(take1(n));
        };
    };
};

// | Repeat a monadic action indefinitely, `yield`ing each result
var repeatM = function (dictMonad) {
    var replaceAwait = Pipes.replaceAwait(dictMonad);
    var lift1 = lift(dictMonad);
    var cat = Pipes.cat(dictMonad);
    return function (m) {
        return replaceAwait(lift1(m))(cat);
    };
};

// | Determine if a `Producer` is empty
var $$null = function (dictMonad) {
    var bind = Control_Bind.bind(dictMonad.Bind1());
    var next = Pipes.next(dictMonad);
    var pure = Control_Applicative.pure(dictMonad.Applicative0());
    return function (p) {
        return bind(next(p))(function (x) {
            return pure((function () {
                if (x instanceof Data_Either.Left) {
                    return true;
                };
                if (x instanceof Data_Either.Right) {
                    return false;
                };
                throw new Error("Failed pattern match at Pipes.Prelude (line 345, column 12 - line 347, column 25): " + [ x.constructor.name ]);
            })());
        });
    };
};

// | Consume all values using a monadic function
var mapM_ = function (dictMonad) {
    var $$for = Pipes["for"](dictMonad);
    var cat = Pipes.cat(dictMonad);
    var lift1 = lift(dictMonad);
    return function (f) {
        return $$for(cat)(function (a) {
            return lift1(f(a));
        });
    };
};

// | Apply a monadic function to all values flowing downstream
var mapM = function (dictMonad) {
    var $$for = Pipes["for"](dictMonad);
    var cat = Pipes.cat(dictMonad);
    var bind = Control_Bind.bind(Pipes_Internal.bindProxy(dictMonad));
    var lift1 = lift(dictMonad);
    var $$yield = Pipes["yield"](dictMonad);
    return function (f) {
        return $$for(cat)(function (a) {
            return bind(lift1(f(a)))(function (b) {
                return $$yield(b);
            });
        });
    };
};

// | Convert a stream of actions to a stream of values
var sequence = function (dictMonad) {
    return mapM(dictMonad)(identity);
};

/**
 *  | Apply a function to all values flowing downstream, and
 *      forward each element of the result.
 */
var mapFoldable = function (dictMonad) {
    var $$for = Pipes["for"](dictMonad);
    var cat = Pipes.cat(dictMonad);
    var each = Pipes.each(dictMonad);
    return function (dictFoldable) {
        var each1 = each(dictFoldable);
        return function (f) {
            return $$for(cat)(function (a) {
                return each1(f(a));
            });
        };
    };
};

// | Apply a function to all values flowing downstream
var map = function (dictMonad) {
    var $$for = Pipes["for"](dictMonad);
    var cat = Pipes.cat(dictMonad);
    var $$yield = Pipes["yield"](dictMonad);
    return function (f) {
        return $$for(cat)(function (a) {
            return $$yield(f(a));
        });
    };
};

// | Convert `Show`able values to `String`s
var show = function (dictMonad) {
    var map1 = map(dictMonad);
    return function (dictShow) {
        return map1(Data_Show.show(dictShow));
    };
};

// | Retrieve the last element from a `Producer`
var last = function (dictMonad) {
    var bind = Control_Bind.bind(dictMonad.Bind1());
    var next = Pipes.next(dictMonad);
    var pure = Control_Applicative.pure(dictMonad.Applicative0());
    return function (p0) {
        var go = function (a) {
            return function (p) {
                return bind(next(p))(function (x) {
                    if (x instanceof Data_Either.Left) {
                        return pure(new Data_Maybe.Just(a));
                    };
                    if (x instanceof Data_Either.Right) {
                        return go(x.value0.value0)(x.value0.value1);
                    };
                    throw new Error("Failed pattern match at Pipes.Prelude (line 313, column 9 - line 315, column 44): " + [ x.constructor.name ]);
                });
            };
        };
        return bind(next(p0))(function (x) {
            if (x instanceof Data_Either.Left) {
                return pure(Data_Maybe.Nothing.value);
            };
            if (x instanceof Data_Either.Right) {
                return go(x.value0.value0)(x.value0.value1);
            };
            throw new Error("Failed pattern match at Pipes.Prelude (line 307, column 5 - line 309, column 38): " + [ x.constructor.name ]);
        });
    };
};

// | Retrieve the first element from a `Producer`
var head = function (dictMonad) {
    var bind = Control_Bind.bind(dictMonad.Bind1());
    var next = Pipes.next(dictMonad);
    var pure = Control_Applicative.pure(dictMonad.Applicative0());
    return function (p) {
        return bind(next(p))(function (x) {
            return pure((function () {
                if (x instanceof Data_Either.Left) {
                    return Data_Maybe.Nothing.value;
                };
                if (x instanceof Data_Either.Right) {
                    return new Data_Maybe.Just(x.value0.value0);
                };
                throw new Error("Failed pattern match at Pipes.Prelude (line 295, column 12 - line 297, column 36): " + [ x.constructor.name ]);
            })());
        });
    };
};

// | Monadic fold of the elements of a `Producer`
var foldM$prime = function (dictMonad) {
    var bind = Control_Bind.bind(dictMonad.Bind1());
    var pure = Control_Applicative.pure(dictMonad.Applicative0());
    return function (step) {
        return function (begin) {
            return function (done) {
                return function (p0) {
                    var go = function (p) {
                        return function (x) {
                            if (p instanceof Pipes_Internal.Request) {
                                return Pipes_Internal.closed(p.value0);
                            };
                            if (p instanceof Pipes_Internal.Respond) {
                                return bind(step(x)(p.value0))(function (x$prime) {
                                    return go(p.value1(Data_Unit.unit))(x$prime);
                                });
                            };
                            if (p instanceof Pipes_Internal.M) {
                                return bind(p.value0)(function (p$prime) {
                                    return go(p$prime)(x);
                                });
                            };
                            if (p instanceof Pipes_Internal.Pure) {
                                return bind(done(x))(function (b) {
                                    return pure(new Data_Tuple.Tuple(b, p.value0));
                                });
                            };
                            throw new Error("Failed pattern match at Pipes.Prelude (line 247, column 14 - line 255, column 29): " + [ p.constructor.name ]);
                        };
                    };
                    return bind(begin)(function (x0) {
                        return go(p0)(x0);
                    });
                };
            };
        };
    };
};

// | Monadic fold of the elements of a `Producer`
var foldM = function (dictMonad) {
    var bind = Control_Bind.bind(dictMonad.Bind1());
    return function (step) {
        return function (begin) {
            return function (done) {
                return function (p0) {
                    var go = function (p) {
                        return function (x) {
                            if (p instanceof Pipes_Internal.Request) {
                                return Pipes_Internal.closed(p.value0);
                            };
                            if (p instanceof Pipes_Internal.Respond) {
                                return bind(step(x)(p.value0))(function (x$prime) {
                                    return go(p.value1(Data_Unit.unit))(x$prime);
                                });
                            };
                            if (p instanceof Pipes_Internal.M) {
                                return bind(p.value0)(function (p$prime) {
                                    return go(p$prime)(x);
                                });
                            };
                            if (p instanceof Pipes_Internal.Pure) {
                                return done(x);
                            };
                            throw new Error("Failed pattern match at Pipes.Prelude (line 230, column 14 - line 236, column 32): " + [ p.constructor.name ]);
                        };
                    };
                    return bind(begin)(function (x0) {
                        return go(p0)(x0);
                    });
                };
            };
        };
    };
};

// | Fold of the elements of a `Producer` that preserves the return value
var fold$prime = function (dictMonad) {
    var bind = Control_Bind.bind(dictMonad.Bind1());
    var pure = Control_Applicative.pure(dictMonad.Applicative0());
    return function (step) {
        return function (begin) {
            return function (done) {
                return function (p0) {
                    var go = function (p) {
                        return function (x) {
                            if (p instanceof Pipes_Internal.Request) {
                                return Pipes_Internal.closed(p.value0);
                            };
                            if (p instanceof Pipes_Internal.Respond) {
                                return go(p.value1(Data_Unit.unit))(step(x)(p.value0));
                            };
                            if (p instanceof Pipes_Internal.M) {
                                return bind(p.value0)(function (p$prime) {
                                    return go(p$prime)(x);
                                });
                            };
                            if (p instanceof Pipes_Internal.Pure) {
                                return pure(new Data_Tuple.Tuple(done(x), p.value0));
                            };
                            throw new Error("Failed pattern match at Pipes.Prelude (line 215, column 14 - line 219, column 49): " + [ p.constructor.name ]);
                        };
                    };
                    return go(p0)(begin);
                };
            };
        };
    };
};

// | Fold of the elements of a `Producer`
var fold = function (dictMonad) {
    var bind = Control_Bind.bind(dictMonad.Bind1());
    var pure = Control_Applicative.pure(dictMonad.Applicative0());
    return function (step) {
        return function (begin) {
            return function (done) {
                return function (p0) {
                    var go = function (p) {
                        return function (x) {
                            if (p instanceof Pipes_Internal.Request) {
                                return Pipes_Internal.closed(p.value0);
                            };
                            if (p instanceof Pipes_Internal.Respond) {
                                return go(p.value1(Data_Unit.unit))(step(x)(p.value0));
                            };
                            if (p instanceof Pipes_Internal.M) {
                                return bind(p.value0)(function (p$prime) {
                                    return go(p$prime)(x);
                                });
                            };
                            if (p instanceof Pipes_Internal.Pure) {
                                return pure(done(x));
                            };
                            throw new Error("Failed pattern match at Pipes.Prelude (line 202, column 14 - line 206, column 39): " + [ p.constructor.name ]);
                        };
                    };
                    return go(p0)(begin);
                };
            };
        };
    };
};

// | Count the number of elements in a `Producer`
var length = function (dictMonad) {
    return fold(dictMonad)(function (n) {
        return function (v) {
            return n + 1 | 0;
        };
    })(0)(identity);
};

// | Find the maximum element of a `Producer`
var maximum = function (dictMonad) {
    var fold1 = fold(dictMonad);
    return function (dictOrd) {
        var greaterThanOrEq = Data_Ord.greaterThanOrEq(dictOrd);
        var max = function (x) {
            return function (y) {
                if (greaterThanOrEq(x)(y)) {
                    return x;
                };
                if (Data_Boolean.otherwise) {
                    return y;
                };
                throw new Error("Failed pattern match at Pipes.Prelude (line 328, column 5 - line 329, column 28): " + [ x.constructor.name, y.constructor.name ]);
            };
        };
        var step = function (x) {
            return function (a) {
                return new Data_Maybe.Just((function () {
                    if (x instanceof Data_Maybe.Nothing) {
                        return a;
                    };
                    if (x instanceof Data_Maybe.Just) {
                        return max(a)(x.value0);
                    };
                    throw new Error("Failed pattern match at Pipes.Prelude (line 325, column 23 - line 327, column 28): " + [ x.constructor.name ]);
                })());
            };
        };
        return fold1(step)(Data_Maybe.Nothing.value)(identity);
    };
};

// | Find the minimum element of a `Producer`
var minimum = function (dictMonad) {
    var fold1 = fold(dictMonad);
    return function (dictOrd) {
        var lessThan = Data_Ord.lessThan(dictOrd);
        var min = function (x) {
            return function (y) {
                if (lessThan(x)(y)) {
                    return x;
                };
                if (Data_Boolean.otherwise) {
                    return y;
                };
                throw new Error("Failed pattern match at Pipes.Prelude (line 338, column 5 - line 339, column 28): " + [ x.constructor.name, y.constructor.name ]);
            };
        };
        var step = function (x) {
            return function (a) {
                return new Data_Maybe.Just((function () {
                    if (x instanceof Data_Maybe.Nothing) {
                        return a;
                    };
                    if (x instanceof Data_Maybe.Just) {
                        return min(a)(x.value0);
                    };
                    throw new Error("Failed pattern match at Pipes.Prelude (line 335, column 23 - line 337, column 28): " + [ x.constructor.name ]);
                })());
            };
        };
        return fold1(step)(Data_Maybe.Nothing.value)(identity);
    };
};
var toListM = function (dictMonad) {
    var step = function (x) {
        return function (a) {
            return function ($292) {
                return x((function (v) {
                    return new Data_List_Types.Cons(a, v);
                })($292));
            };
        };
    };
    var done = function (x) {
        return x(Data_List_Types.Nil.value);
    };
    return fold(dictMonad)(step)(Control_Category.identity(Control_Category.categoryFn))(done);
};

// | Outputs the indices of all elements that satisfied the predicate
var findIndices = function (dictMonad) {
    var bindProxy = Pipes_Internal.bindProxy(dictMonad);
    var bind = Control_Bind.bind(bindProxy);
    var $$await = Pipes["await"](dictMonad);
    var discard1 = discard(bindProxy);
    var when = Control_Applicative.when(Pipes_Internal.applicativeProxy(dictMonad));
    var $$yield = Pipes["yield"](dictMonad);
    return function (predicate) {
        var go = function (n) {
            return bind($$await)(function (a) {
                return discard1(when(predicate(a))($$yield(n)))(function () {
                    return go(n + 1 | 0);
                });
            });
        };
        return go(0);
    };
};

/**
 * | Find the index of the first element of a `Producer` that satisfies the
 *     predicate
 */
var findIndex = function (dictMonad) {
    var head1 = head(dictMonad);
    var composePipes = Pipes.composePipes(dictMonad);
    var findIndices1 = findIndices(dictMonad);
    return function (predicate) {
        return function (p) {
            return head1(composePipes(p)(findIndices1(predicate)));
        };
    };
};

// |`filterM` only forwards values that satisfy the monadic predicate
var filterM = function (dictMonad) {
    var $$for = Pipes["for"](dictMonad);
    var cat = Pipes.cat(dictMonad);
    var bind = Control_Bind.bind(Pipes_Internal.bindProxy(dictMonad));
    var lift1 = lift(dictMonad);
    var when = Control_Applicative.when(Pipes_Internal.applicativeProxy(dictMonad));
    var $$yield = Pipes["yield"](dictMonad);
    return function (predicate) {
        return $$for(cat)(function (a) {
            return bind(lift1(predicate(a)))(function (b) {
                return when(b)($$yield(a));
            });
        });
    };
};

// | `filter` only forwards values that satisfy the predicate.
var filter = function (dictMonad) {
    var $$for = Pipes["for"](dictMonad);
    var cat = Pipes.cat(dictMonad);
    var when = Control_Applicative.when(Pipes_Internal.applicativeProxy(dictMonad));
    var $$yield = Pipes["yield"](dictMonad);
    return function (predicate) {
        return $$for(cat)(function (a) {
            return when(predicate(a))($$yield(a));
        });
    };
};

// | Find the first element of a `Producer` that satisfies the predicate
var find = function (dictMonad) {
    var head1 = head(dictMonad);
    var composePipes = Pipes.composePipes(dictMonad);
    var filter1 = filter(dictMonad);
    return function (predicate) {
        return function (p) {
            return head1(composePipes(p)(filter1(predicate)));
        };
    };
};

/**
 * | dropWhile discards values going downstream until one violates the
 *     predicate p.
 */
var dropWhile = function (dictMonad) {
    var bindProxy = Pipes_Internal.bindProxy(dictMonad);
    var bind = Control_Bind.bind(bindProxy);
    var $$await = Pipes["await"](dictMonad);
    var discard1 = discard(bindProxy);
    var $$yield = Pipes["yield"](dictMonad);
    var cat = Pipes.cat(dictMonad);
    return function (predicate) {
        var $lazy_go = $runtime_lazy("go", "Pipes.Prelude", function () {
            return bind($$await)(function (a) {
                var $290 = predicate(a);
                if ($290) {
                    return $lazy_go(133);
                };
                return discard1($$yield(a))(function () {
                    return cat;
                });
            });
        });
        var go = $lazy_go(130);
        return go;
    };
};

// | drop discards n values going downstream
var drop = function (dictMonad) {
    var cat = Pipes.cat(dictMonad);
    var bind = Control_Bind.bind(Pipes_Internal.bindProxy(dictMonad));
    var $$await = Pipes["await"](dictMonad);
    var loop = function (v) {
        if (v === 0) {
            return cat;
        };
        return bind($$await)(function () {
            return loop(v - 1 | 0);
        });
    };
    return loop;
};

// | Index into a `Producer`
var index = function (dictMonad) {
    var head1 = head(dictMonad);
    var composePipes = Pipes.composePipes(dictMonad);
    var drop1 = drop(dictMonad);
    return function (n) {
        return function (p) {
            return head1(composePipes(p)(drop1(n)));
        };
    };
};

// | `discard` all incoming values
var drain = function (dictMonad) {
    return Pipes["for"](dictMonad)(Pipes.cat(dictMonad))(Pipes.discard(Pipes_Internal.monadProxy(dictMonad)));
};

// | Flatten all 'Foldable' elements flowing downstream
var concat = function (dictMonad) {
    var $$for = Pipes["for"](dictMonad);
    var cat = Pipes.cat(dictMonad);
    var each = Pipes.each(dictMonad);
    return function (dictFoldable) {
        return $$for(cat)(each(dictFoldable));
    };
};

// | Apply an action to all values flowing downstream
var chain = function (dictMonad) {
    var $$for = Pipes["for"](dictMonad);
    var cat = Pipes.cat(dictMonad);
    var discard1 = discard(Pipes_Internal.bindProxy(dictMonad));
    var lift1 = lift(dictMonad);
    var $$yield = Pipes["yield"](dictMonad);
    return function (f) {
        return $$for(cat)(function (a) {
            return discard1(lift1(f(a)))(function () {
                return $$yield(a);
            });
        });
    };
};

// | any determines whether any element of p satisfies the predicate.
var any = function (dictMonad) {
    var liftM1 = Control_Monad.liftM1(dictMonad);
    var null1 = $$null(dictMonad);
    var composePipes = Pipes.composePipes(dictMonad);
    var filter1 = filter(dictMonad);
    return function (predicate) {
        return function (p) {
            return liftM1(not)(null1(composePipes(p)(filter1(predicate))));
        };
    };
};

// | elem returns `True` if p has an element equal to a, `False` otherwise
var elem = function (dictMonad) {
    var any1 = any(dictMonad);
    return function (dictEq) {
        var eq = Data_Eq.eq(dictEq);
        return function (a) {
            return any1(function (v) {
                return eq(a)(v);
            });
        };
    };
};

// | Determines whether any element is `True`
var or = function (dictMonad) {
    return any(dictMonad)(identity);
};

// | all determines whether all the elements of p satisfy the predicate.
var all = function (dictMonad) {
    var null1 = $$null(dictMonad);
    var composePipes = Pipes.composePipes(dictMonad);
    var filter1 = filter(dictMonad);
    return function (predicate) {
        return function (p) {
            return null1(composePipes(p)(filter1(function (a) {
                return !predicate(a);
            })));
        };
    };
};

// | Determines whether all elements are `True`
var and = function (dictMonad) {
    return all(dictMonad)(identity);
};

// | notElem returns `False` if p has an element equal to a, `True` otherwise
var notElem = function (dictMonad) {
    var all1 = all(dictMonad);
    return function (dictEq) {
        var notEq = Data_Eq.notEq(dictEq);
        return function (a) {
            return all1(function (v) {
                return notEq(a)(v);
            });
        };
    };
};
export {
    repeatM,
    replicateM,
    mapM_,
    drain,
    map,
    mapM,
    sequence,
    mapFoldable,
    filter,
    filterM,
    take,
    takeWhile,
    takeWhile$prime,
    drop,
    dropWhile,
    concat,
    findIndices,
    scan,
    scanM,
    chain,
    show,
    seq,
    fold,
    fold$prime,
    foldM,
    foldM$prime,
    all,
    any,
    and,
    or,
    elem,
    notElem,
    find,
    findIndex,
    head,
    index,
    last,
    length,
    maximum,
    minimum,
    $$null as null,
    toList,
    toListM
};
