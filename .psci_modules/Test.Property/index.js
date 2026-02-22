// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                 // hydrogen // property tests
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Exhaustive property-based tests with realistic distributions.
// |
// | This module tests:
// | - Algebraic laws (Functor, Applicative, Monad, Semigroup, Monoid, Alt, Plus)
// | - Metamorphic properties (relationships between operations)
// | - Invariants (properties that must always hold)
// | - Edge cases (boundaries, special values, adversarial inputs)
import * as Control_Alt from "../Control.Alt/index.js";
import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Control_Apply from "../Control.Apply/index.js";
import * as Control_Bind from "../Control.Bind/index.js";
import * as Control_Category from "../Control.Category/index.js";
import * as Control_Plus from "../Control.Plus/index.js";
import * as Control_Semigroupoid from "../Control.Semigroupoid/index.js";
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Array_NonEmpty from "../Data.Array.NonEmpty/index.js";
import * as Data_Either from "../Data.Either/index.js";
import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_EuclideanRing from "../Data.EuclideanRing/index.js";
import * as Data_Foldable from "../Data.Foldable/index.js";
import * as Data_Function from "../Data.Function/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Data_Identity from "../Data.Identity/index.js";
import * as Data_Int from "../Data.Int/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Monoid from "../Data.Monoid/index.js";
import * as Data_Semigroup from "../Data.Semigroup/index.js";
import * as Data_Semiring from "../Data.Semiring/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Data_String_CodePoints from "../Data.String.CodePoints/index.js";
import * as Data_String_CodeUnits from "../Data.String.CodeUnits/index.js";
import * as Data_String_Common from "../Data.String.Common/index.js";
import * as Data_Traversable from "../Data.Traversable/index.js";
import * as Data_Tuple from "../Data.Tuple/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
import * as Effect_Aff from "../Effect.Aff/index.js";
import * as Hydrogen_Data_Format from "../Hydrogen.Data.Format/index.js";
import * as Hydrogen_Data_RemoteData from "../Hydrogen.Data.RemoteData/index.js";
import * as Hydrogen_Form_Validation from "../Hydrogen.Form.Validation/index.js";
import * as Hydrogen_Style_Color from "../Hydrogen.Style.Color/index.js";
import * as Test_QuickCheck from "../Test.QuickCheck/index.js";
import * as Test_QuickCheck_Arbitrary from "../Test.QuickCheck.Arbitrary/index.js";
import * as Test_QuickCheck_Gen from "../Test.QuickCheck.Gen/index.js";
import * as Test_Spec from "../Test.Spec/index.js";
import * as Test_Spec_Assertions from "../Test.Spec.Assertions/index.js";
import * as Test_Spec_QuickCheck from "../Test.Spec.QuickCheck/index.js";
var pure = /* #__PURE__ */ Control_Applicative.pure(Test_QuickCheck_Gen.applicativeGen);
var arbitrary = /* #__PURE__ */ Test_QuickCheck_Arbitrary.arbitrary(Test_QuickCheck_Arbitrary.arbString);
var describe = /* #__PURE__ */ Test_Spec.describe(Data_Identity.monadIdentity);
var discard = /* #__PURE__ */ Control_Bind.discard(Control_Bind.discardUnit);
var discard1 = /* #__PURE__ */ discard(/* #__PURE__ */ Test_Spec.bindSpecT(Data_Identity.bindIdentity));
var it = /* #__PURE__ */ Test_Spec.it(Data_Identity.monadIdentity)(Test_Spec.exampleMUnit);
var testableFunction = /* #__PURE__ */ Test_QuickCheck.testableFunction(/* #__PURE__ */ Test_QuickCheck_Arbitrary.arbArray(Test_QuickCheck_Arbitrary.arbString));
var testableFunction1 = /* #__PURE__ */ testableFunction(Test_QuickCheck.testableResult);
var quickCheck = /* #__PURE__ */ Test_Spec_QuickCheck.quickCheck(testableFunction1);
var assertEquals = /* #__PURE__ */ Test_QuickCheck.assertEquals(Hydrogen_Form_Validation.eqValidationResult)(Hydrogen_Form_Validation.showValidationResult);
var append = /* #__PURE__ */ Data_Semigroup.append(Hydrogen_Form_Validation.semigroupValidationResult);
var quickCheck1 = /* #__PURE__ */ Test_Spec_QuickCheck.quickCheck(/* #__PURE__ */ testableFunction(/* #__PURE__ */ testableFunction(testableFunction1)));
var testableFunction2 = /* #__PURE__ */ Test_QuickCheck.testableFunction(Test_QuickCheck_Arbitrary.arbString);
var quickCheck2 = /* #__PURE__ */ Test_Spec_QuickCheck.quickCheck(/* #__PURE__ */ testableFunction2(Test_QuickCheck.testableBoolean));
var mempty = /* #__PURE__ */ Data_Monoid.mempty(Hydrogen_Form_Validation.monoidValidator);
var append1 = /* #__PURE__ */ Data_Semigroup.append(Hydrogen_Form_Validation.semigroupValidator);
var discard2 = /* #__PURE__ */ discard(Effect_Aff.bindAff);
var shouldEqual = /* #__PURE__ */ Test_Spec_Assertions.shouldEqual(Effect_Aff.monadThrowAff);
var shouldEqual1 = /* #__PURE__ */ shouldEqual(/* #__PURE__ */ Data_Show.showArray(Data_Show.showString))(/* #__PURE__ */ Data_Eq.eqArray(Data_Eq.eqString));
var shouldEqual2 = /* #__PURE__ */ shouldEqual(Data_Show.showBoolean)(Data_Eq.eqBoolean);
var quickCheck3 = /* #__PURE__ */ Test_Spec_QuickCheck.quickCheck(/* #__PURE__ */ Test_QuickCheck.testableGen(Test_QuickCheck.testableResult));
var bind = /* #__PURE__ */ Control_Bind.bind(Test_QuickCheck_Gen.bindGen);
var assertEquals1 = /* #__PURE__ */ Test_QuickCheck.assertEquals(Data_Eq.eqBoolean)(Data_Show.showBoolean);
var quickCheck4 = /* #__PURE__ */ Test_Spec_QuickCheck.quickCheck(/* #__PURE__ */ Test_QuickCheck.testableGen(Test_QuickCheck.testableBoolean));
var shouldEqual3 = /* #__PURE__ */ shouldEqual(Data_Show.showString)(Data_Eq.eqString);
var pure1 = /* #__PURE__ */ Control_Applicative.pure(Effect_Aff.applicativeAff);
var map = /* #__PURE__ */ Data_Functor.map(Test_QuickCheck_Gen.functorGen);
var compose = /* #__PURE__ */ Control_Semigroupoid.compose(Control_Semigroupoid.semigroupoidFn);
var add = /* #__PURE__ */ Data_Semiring.add(Data_Semiring.semiringInt);
var identity = /* #__PURE__ */ Control_Category.identity(Control_Category.categoryFn);
var mod = /* #__PURE__ */ Data_EuclideanRing.mod(Data_EuclideanRing.euclideanRingInt);
var arbitrary1 = /* #__PURE__ */ Test_QuickCheck_Arbitrary.arbitrary(Test_QuickCheck_Arbitrary.arbInt);
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);
var testableFunction3 = /* #__PURE__ */ Test_QuickCheck.testableFunction(Test_QuickCheck_Arbitrary.arbInt);
var quickCheck5 = /* #__PURE__ */ Test_Spec_QuickCheck.quickCheck(/* #__PURE__ */ testableFunction3(Test_QuickCheck.testableResult));
var eqRemoteData = /* #__PURE__ */ Hydrogen_Data_RemoteData.eqRemoteData(Data_Eq.eqString);
var eqRemoteData1 = /* #__PURE__ */ eqRemoteData(Data_Eq.eqInt);
var showRemoteData = /* #__PURE__ */ Hydrogen_Data_RemoteData.showRemoteData(Data_Show.showString);
var showRemoteData1 = /* #__PURE__ */ showRemoteData(Data_Show.showInt);
var assertEquals2 = /* #__PURE__ */ Test_QuickCheck.assertEquals(eqRemoteData1)(showRemoteData1);
var apply = /* #__PURE__ */ Control_Apply.apply(Hydrogen_Data_RemoteData.applyRemoteData);
var quickCheck6 = /* #__PURE__ */ Test_Spec_QuickCheck.quickCheck(/* #__PURE__ */ Test_QuickCheck.testableFunction(Test_QuickCheck_Arbitrary.arbUnit)(Test_QuickCheck.testableBoolean));
var quickCheck7 = /* #__PURE__ */ Test_Spec_QuickCheck.quickCheck(/* #__PURE__ */ testableFunction3(/* #__PURE__ */ testableFunction3(Test_QuickCheck.testableBoolean)));
var map1 = /* #__PURE__ */ Data_Functor.map(Hydrogen_Data_RemoteData.functorRemoteData);
var append3 = /* #__PURE__ */ Data_Semigroup.append(/* #__PURE__ */ Hydrogen_Data_RemoteData.semigroupRemoteData(Data_Semigroup.semigroupString));
var assertEquals3 = /* #__PURE__ */ Test_QuickCheck.assertEquals(Data_Eq.eqInt)(Data_Show.showInt);
var foldr = /* #__PURE__ */ Data_Foldable.foldr(Hydrogen_Data_RemoteData.foldableRemoteData);
var map2 = /* #__PURE__ */ Data_Functor.map(Data_Functor.functorArray);
var sequence = /* #__PURE__ */ Data_Traversable.sequence(Data_Traversable.traversableArray)(Hydrogen_Data_RemoteData.applicativeRemoteData);
var quickCheck8 = /* #__PURE__ */ Test_Spec_QuickCheck.quickCheck(/* #__PURE__ */ testableFunction2(/* #__PURE__ */ Test_QuickCheck.testableFunction(/* #__PURE__ */ Test_QuickCheck_Arbitrary.arbArray(Test_QuickCheck_Arbitrary.arbInt))(Test_QuickCheck.testableResult)));
var pure2 = /* #__PURE__ */ Control_Applicative.pure(Hydrogen_Data_RemoteData.applicativeRemoteData);
var bind1 = /* #__PURE__ */ Control_Bind.bind(Hydrogen_Data_RemoteData.bindRemoteData);
var assertEquals4 = /* #__PURE__ */ Test_QuickCheck.assertEquals(/* #__PURE__ */ eqRemoteData(Data_Eq.eqString))(/* #__PURE__ */ showRemoteData(Data_Show.showString));
var mempty1 = /* #__PURE__ */ Data_Monoid.mempty(/* #__PURE__ */ Hydrogen_Data_RemoteData.monoidRemoteData(Data_Semigroup.semigroupString));
var alt = /* #__PURE__ */ Control_Alt.alt(Hydrogen_Data_RemoteData.altRemoteData);
var empty = /* #__PURE__ */ Control_Plus.empty(Hydrogen_Data_RemoteData.plusRemoteData);
var shouldEqual4 = /* #__PURE__ */ shouldEqual(showRemoteData1)(eqRemoteData1);
var foldl = /* #__PURE__ */ Data_Foldable.foldl(Data_Foldable.foldableArray);
var shouldEqual5 = /* #__PURE__ */ shouldEqual(Data_Show.showInt)(Data_Eq.eqInt);
var show1 = /* #__PURE__ */ Data_Show.show(Data_Show.showNumber);
var assertEquals5 = /* #__PURE__ */ Test_QuickCheck.assertEquals(Data_Eq.eqString)(Data_Show.showString);
var quickCheck9 = /* #__PURE__ */ Test_Spec_QuickCheck.quickCheck(/* #__PURE__ */ Test_QuickCheck.testableFunction(Test_QuickCheck_Arbitrary.arbNumber)(Test_QuickCheck.testableBoolean));
var shouldEqual6 = /* #__PURE__ */ shouldEqual(Data_Show.showNumber)(Data_Eq.eqNumber);
var assertEquals6 = /* #__PURE__ */ Test_QuickCheck.assertEquals(Data_Eq.eqNumber)(Data_Show.showNumber);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                             // arbitrary instances
// ═══════════════════════════════════════════════════════════════════════════════
// We need Arbitrary instances for quickcheck to work with our types
// Using newtype wrappers to avoid orphan instances
var ArbRemoteData = function (x) {
    return x;
};

// | Validation strings - realistic inputs including adversarial cases
var genValidationString = /* #__PURE__ */ (function () {
    return Test_QuickCheck_Gen.frequency(Data_Array_NonEmpty["cons$prime"](new Data_Tuple.Tuple(10.0, pure("")))([ new Data_Tuple.Tuple(10.0, pure("   ")), new Data_Tuple.Tuple(10.0, pure("a")), new Data_Tuple.Tuple(15.0, pure("valid@email.com")), new Data_Tuple.Tuple(10.0, pure("https://example.com")), new Data_Tuple.Tuple(10.0, pure("not an email")), new Data_Tuple.Tuple(10.0, pure("12345")), new Data_Tuple.Tuple(5.0, pure("\u65e5\u672c\u8a9e\u30c6\u30b9\u30c8")), new Data_Tuple.Tuple(5.0, pure(Data_String_Common.joinWith("")(Data_Array.replicate(10000)("x")))), new Data_Tuple.Tuple(15.0, arbitrary) ]));
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                    // Validation property tests
// ═══════════════════════════════════════════════════════════════════════════════
var validationProperties = /* #__PURE__ */ describe("Validation Properties")(/* #__PURE__ */ discard1(/* #__PURE__ */ describe("ValidationResult Monoid Laws")(/* #__PURE__ */ discard1(/* #__PURE__ */ it("left identity: Valid <> x = x")(/* #__PURE__ */ quickCheck(function (v) {
    var x = (function () {
        var $168 = Data_Array["null"](v);
        if ($168) {
            return Hydrogen_Form_Validation.Valid.value;
        };
        return new Hydrogen_Form_Validation.Invalid(v);
    })();
    return assertEquals(append(Hydrogen_Form_Validation.Valid.value)(x))(x);
})))(function () {
    return discard1(it("right identity: x <> Valid = x")(quickCheck(function (v) {
        var x = (function () {
            var $170 = Data_Array["null"](v);
            if ($170) {
                return Hydrogen_Form_Validation.Valid.value;
            };
            return new Hydrogen_Form_Validation.Invalid(v);
        })();
        return assertEquals(append(x)(Hydrogen_Form_Validation.Valid.value))(x);
    })))(function () {
        return it("associativity")(quickCheck1(function (v) {
            return function (v1) {
                return function (v2) {
                    var z = (function () {
                        var $174 = Data_Array["null"](v2);
                        if ($174) {
                            return Hydrogen_Form_Validation.Valid.value;
                        };
                        return new Hydrogen_Form_Validation.Invalid(v2);
                    })();
                    var y = (function () {
                        var $175 = Data_Array["null"](v1);
                        if ($175) {
                            return Hydrogen_Form_Validation.Valid.value;
                        };
                        return new Hydrogen_Form_Validation.Invalid(v1);
                    })();
                    var x = (function () {
                        var $176 = Data_Array["null"](v);
                        if ($176) {
                            return Hydrogen_Form_Validation.Valid.value;
                        };
                        return new Hydrogen_Form_Validation.Invalid(v);
                    })();
                    return assertEquals(append(append(x)(y))(z))(append(x)(append(y)(z)));
                };
            };
        }));
    });
})))(function () {
    return discard1(describe("Validator Monoid Laws")(discard1(it("mempty validator always passes")(quickCheck2(function (v) {
        return Hydrogen_Form_Validation.isValid(Hydrogen_Form_Validation.validate(mempty)(v));
    })))(function () {
        return it("composed validators accumulate errors")((function () {
            var v1 = Hydrogen_Form_Validation.required("required");
            var v2 = Hydrogen_Form_Validation.minLength(5)("min5");
            var composed = append1(v1)(v2);
            return discard2(shouldEqual1(Hydrogen_Form_Validation.getErrors(Hydrogen_Form_Validation.validate(composed)("")))([ "required", "min5" ]))(function () {
                return discard2(shouldEqual1(Hydrogen_Form_Validation.getErrors(Hydrogen_Form_Validation.validate(composed)("a")))([ "min5" ]))(function () {
                    return shouldEqual2(Hydrogen_Form_Validation.isValid(Hydrogen_Form_Validation.validate(composed)("hello")))(true);
                });
            });
        })());
    })))(function () {
        return describe("Validator semantics")(discard1(it("required fails on empty and whitespace")((function () {
            var v = Hydrogen_Form_Validation.required("err");
            return discard2(shouldEqual2(Hydrogen_Form_Validation.isInvalid(Hydrogen_Form_Validation.validate(v)("")))(true))(function () {
                return discard2(shouldEqual2(Hydrogen_Form_Validation.isInvalid(Hydrogen_Form_Validation.validate(v)("   ")))(true))(function () {
                    return discard2(shouldEqual2(Hydrogen_Form_Validation.isInvalid(Hydrogen_Form_Validation.validate(v)("\x09\x0a")))(true))(function () {
                        return shouldEqual2(Hydrogen_Form_Validation.isValid(Hydrogen_Form_Validation.validate(v)("a")))(true);
                    });
                });
            });
        })()))(function () {
            return discard1(it("minLength counts correctly")(quickCheck3(bind(Test_QuickCheck_Gen.chooseInt(1)(20))(function (len) {
                return bind(genValidationString)(function (s) {
                    var v = Hydrogen_Form_Validation.minLength(len)("err");
                    var result = Hydrogen_Form_Validation.validate(v)(s);
                    var expected = Data_String_CodePoints.length(s) >= len;
                    return pure(assertEquals1(Hydrogen_Form_Validation.isValid(result))(expected));
                });
            }))))(function () {
                return discard1(it("maxLength counts correctly")(quickCheck3(bind(Test_QuickCheck_Gen.chooseInt(1)(50))(function (len) {
                    return bind(genValidationString)(function (s) {
                        var v = Hydrogen_Form_Validation.maxLength(len)("err");
                        var result = Hydrogen_Form_Validation.validate(v)(s);
                        var expected = Data_String_CodePoints.length(s) <= len;
                        return pure(assertEquals1(Hydrogen_Form_Validation.isValid(result))(expected));
                    });
                }))))(function () {
                    return discard1(it("optional passes empty strings")(quickCheck4(bind(Test_QuickCheck_Gen.chooseInt(1)(20))(function (len) {
                        var v = Hydrogen_Form_Validation.optional(Hydrogen_Form_Validation.minLength(len)("err"));
                        return pure(Hydrogen_Form_Validation.isValid(Hydrogen_Form_Validation.validate(v)("")) && Hydrogen_Form_Validation.isValid(Hydrogen_Form_Validation.validate(v)("   ")));
                    }))))(function () {
                        return discard1(it("email validates basic format")((function () {
                            var v = Hydrogen_Form_Validation.email("err");
                            return discard2(shouldEqual2(Hydrogen_Form_Validation.isValid(Hydrogen_Form_Validation.validate(v)("test@example.com")))(true))(function () {
                                return discard2(shouldEqual2(Hydrogen_Form_Validation.isValid(Hydrogen_Form_Validation.validate(v)("user.name+tag@domain.co.uk")))(true))(function () {
                                    return discard2(shouldEqual2(Hydrogen_Form_Validation.isInvalid(Hydrogen_Form_Validation.validate(v)("notanemail")))(true))(function () {
                                        return discard2(shouldEqual2(Hydrogen_Form_Validation.isInvalid(Hydrogen_Form_Validation.validate(v)("@nodomain")))(true))(function () {
                                            return shouldEqual2(Hydrogen_Form_Validation.isInvalid(Hydrogen_Form_Validation.validate(v)("no@")))(true);
                                        });
                                    });
                                });
                            });
                        })()))(function () {
                            return discard1(it("numeric validates number strings")((function () {
                                var v = Hydrogen_Form_Validation.numeric("err");
                                return discard2(shouldEqual2(Hydrogen_Form_Validation.isValid(Hydrogen_Form_Validation.validate(v)("123")))(true))(function () {
                                    return discard2(shouldEqual2(Hydrogen_Form_Validation.isValid(Hydrogen_Form_Validation.validate(v)("3.14")))(true))(function () {
                                        return discard2(shouldEqual2(Hydrogen_Form_Validation.isValid(Hydrogen_Form_Validation.validate(v)("-42")))(true))(function () {
                                            return discard2(shouldEqual2(Hydrogen_Form_Validation.isInvalid(Hydrogen_Form_Validation.validate(v)("abc")))(true))(function () {
                                                return shouldEqual2(Hydrogen_Form_Validation.isInvalid(Hydrogen_Form_Validation.validate(v)("")))(true);
                                            });
                                        });
                                    });
                                });
                            })()))(function () {
                                return discard1(it("when/unless conditional application")((function () {
                                    var v = Hydrogen_Form_Validation.when(false)(Hydrogen_Form_Validation.required("err"));
                                    return discard2(shouldEqual2(Hydrogen_Form_Validation.isValid(Hydrogen_Form_Validation.validate(v)("")))(true))(function () {
                                        var v2 = Hydrogen_Form_Validation.unless(true)(Hydrogen_Form_Validation.required("err"));
                                        return shouldEqual2(Hydrogen_Form_Validation.isValid(Hydrogen_Form_Validation.validate(v2)("")))(true);
                                    });
                                })()))(function () {
                                    return it("validateM returns correct Either")((function () {
                                        var v = Hydrogen_Form_Validation.required("err");
                                        return discard2((function () {
                                            var v1 = Hydrogen_Form_Validation.validateM(v)("hello");
                                            if (v1 instanceof Data_Either.Right) {
                                                return shouldEqual3(v1.value0)("hello");
                                            };
                                            if (v1 instanceof Data_Either.Left) {
                                                return pure1(Data_Unit.unit);
                                            };
                                            throw new Error("Failed pattern match at Test.Property (line 741, column 7 - line 743, column 28): " + [ v1.constructor.name ]);
                                        })())(function () {
                                            var v1 = Hydrogen_Form_Validation.validateM(v)("");
                                            if (v1 instanceof Data_Either.Left) {
                                                return shouldEqual1(v1.value0)([ "err" ]);
                                            };
                                            if (v1 instanceof Data_Either.Right) {
                                                return pure1(Data_Unit.unit);
                                            };
                                            throw new Error("Failed pattern match at Test.Property (line 744, column 7 - line 746, column 29): " + [ v1.constructor.name ]);
                                        });
                                    })());
                                });
                            });
                        });
                    });
                });
            });
        }));
    });
}));

// | Adversarial RemoteData - biased toward edge cases
var genRemoteDataAdversarial = function (genE) {
    return function (genA) {
        return Test_QuickCheck_Gen.frequency(Data_Array_NonEmpty["cons$prime"](new Data_Tuple.Tuple(25.0, pure(Hydrogen_Data_RemoteData.NotAsked.value)))([ new Data_Tuple.Tuple(25.0, pure(Hydrogen_Data_RemoteData.Loading.value)), new Data_Tuple.Tuple(25.0, map(Hydrogen_Data_RemoteData.Failure.create)(genE)), new Data_Tuple.Tuple(25.0, map(Hydrogen_Data_RemoteData.Success.create)(genA)) ]));
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // generators
// ═══════════════════════════════════════════════════════════════════════════════
// | RemoteData generator with realistic distribution:
// | - 10% NotAsked (uncommon in real apps after initialization)
// | - 15% Loading (transient state)
// | - 20% Failure (errors happen but not majority)
// | - 55% Success (most common steady state)
var genRemoteData = function (genE) {
    return function (genA) {
        return Test_QuickCheck_Gen.frequency(Data_Array_NonEmpty["cons$prime"](new Data_Tuple.Tuple(10.0, pure(Hydrogen_Data_RemoteData.NotAsked.value)))([ new Data_Tuple.Tuple(15.0, pure(Hydrogen_Data_RemoteData.Loading.value)), new Data_Tuple.Tuple(20.0, map(Hydrogen_Data_RemoteData.Failure.create)(genE)), new Data_Tuple.Tuple(55.0, map(Hydrogen_Data_RemoteData.Success.create)(genA)) ]));
    };
};

// | Generate kleisli arrows for Monad law testing
var genKleisli = /* #__PURE__ */ (function () {
    return Test_QuickCheck_Gen.elements(Data_Array_NonEmpty["cons$prime"](function ($203) {
        return Hydrogen_Data_RemoteData.Success.create((function (v) {
            return v + 1 | 0;
        })($203));
    })([ function ($204) {
        return Hydrogen_Data_RemoteData.Success.create((function (v) {
            return v * 2 | 0;
        })($204));
    }, Data_Function["const"](new Hydrogen_Data_RemoteData.Failure("kleisli error")), Data_Function["const"](Hydrogen_Data_RemoteData.Loading.value), Data_Function["const"](Hydrogen_Data_RemoteData.NotAsked.value), function (x) {
        var $184 = x > 0;
        if ($184) {
            return new Hydrogen_Data_RemoteData.Success(x);
        };
        return new Hydrogen_Data_RemoteData.Failure("negative");
    }, function (x) {
        var $185 = x === 0;
        if ($185) {
            return Hydrogen_Data_RemoteData.Loading.value;
        };
        return new Hydrogen_Data_RemoteData.Success(x + 1 | 0);
    } ]));
})();

// | Generate functions for testing Functor/Monad laws
// | These must produce deterministic results for the same input
var genIntFunction = /* #__PURE__ */ Test_QuickCheck_Gen.elements(/* #__PURE__ */ Data_Array_NonEmpty["cons$prime"](identity)([ function (v) {
    return v + 1 | 0;
}, function (v) {
    return v - 1 | 0;
}, function (v) {
    return v * 2 | 0;
}, function (v) {
    return v * (-1 | 0) | 0;
}, /* #__PURE__ */ Data_Function["const"](0), /* #__PURE__ */ Data_Function["const"](42), function (x) {
    return x * x | 0;
}, function (x) {
    var $186 = x > 0;
    if ($186) {
        return x;
    };
    return -x | 0;
}, function (x) {
    return mod(x)(10);
} ]));

// | Adversarial HSL - edge cases and boundaries
var genHSLAdversarial = /* #__PURE__ */ (function () {
    return bind(Test_QuickCheck_Gen.elements(Data_Array_NonEmpty["cons$prime"](0.0)([ 360.0, -1.0, 361.0, 180.0 ])))(function (h) {
        return bind(Test_QuickCheck_Gen.elements(Data_Array_NonEmpty["cons$prime"](0.0)([ 100.0, -1.0, 101.0, 50.0 ])))(function (s) {
            return bind(Test_QuickCheck_Gen.elements(Data_Array_NonEmpty["cons$prime"](0.0)([ 100.0, -1.0, 101.0, 50.0 ])))(function (l) {
                return bind(Test_QuickCheck_Gen.elements(Data_Array_NonEmpty["cons$prime"](0.0)([ 100.0, -1.0, 101.0, 50.0 ])))(function (a) {
                    return pure({
                        h: h,
                        s: s,
                        l: l,
                        a: a
                    });
                });
            });
        });
    });
})();

// | HSL color generator with realistic distribution
var genHSL = /* #__PURE__ */ (function () {
    return bind(Test_QuickCheck_Gen.frequency(Data_Array_NonEmpty["cons$prime"](new Data_Tuple.Tuple(20.0, pure(0.0)))([ new Data_Tuple.Tuple(10.0, pure(60.0)), new Data_Tuple.Tuple(10.0, pure(120.0)), new Data_Tuple.Tuple(10.0, pure(180.0)), new Data_Tuple.Tuple(10.0, pure(240.0)), new Data_Tuple.Tuple(10.0, pure(300.0)), new Data_Tuple.Tuple(30.0, map(Data_Int.toNumber)(Test_QuickCheck_Gen.chooseInt(0)(360))) ])))(function (h) {
        return bind(Test_QuickCheck_Gen.frequency(Data_Array_NonEmpty["cons$prime"](new Data_Tuple.Tuple(15.0, pure(0.0)))([ new Data_Tuple.Tuple(15.0, pure(50.0)), new Data_Tuple.Tuple(15.0, pure(100.0)), new Data_Tuple.Tuple(55.0, map(Data_Int.toNumber)(Test_QuickCheck_Gen.chooseInt(0)(100))) ])))(function (s) {
            return bind(Test_QuickCheck_Gen.frequency(Data_Array_NonEmpty["cons$prime"](new Data_Tuple.Tuple(10.0, pure(0.0)))([ new Data_Tuple.Tuple(10.0, pure(100.0)), new Data_Tuple.Tuple(10.0, pure(50.0)), new Data_Tuple.Tuple(70.0, map(Data_Int.toNumber)(Test_QuickCheck_Gen.chooseInt(0)(100))) ])))(function (l) {
                return bind(Test_QuickCheck_Gen.frequency(Data_Array_NonEmpty["cons$prime"](new Data_Tuple.Tuple(70.0, pure(100.0)))([ new Data_Tuple.Tuple(10.0, pure(0.0)), new Data_Tuple.Tuple(20.0, map(Data_Int.toNumber)(Test_QuickCheck_Gen.chooseInt(0)(100))) ])))(function (a) {
                    return pure({
                        h: h,
                        s: s,
                        l: l,
                        a: a
                    });
                });
            });
        });
    });
})();

// | Realistic error strings - not just random garbage
var genErrorString = /* #__PURE__ */ Test_QuickCheck_Gen.elements(/* #__PURE__ */ Data_Array_NonEmpty["cons$prime"]("Network error")([ "Timeout", "404 Not Found", "500 Internal Server Error", "Connection refused", "Invalid JSON", "Unauthorized", "Rate limited", "", "Error with unicode: \u65e5\u672c\u8a9e", /* #__PURE__ */ Data_String_Common.joinWith("")(/* #__PURE__ */ Data_Array.replicate(1000)("x")) ]));

// | Generate RemoteData with String errors and Int values (common case)
var genRemoteDataStringInt = /* #__PURE__ */ genRemoteData(genErrorString)(arbitrary1);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                // RemoteData invariant tests
// ═══════════════════════════════════════════════════════════════════════════════
var remoteDataInvariants = /* #__PURE__ */ describe("RemoteData Invariants")(/* #__PURE__ */ discard1(/* #__PURE__ */ describe("Constructor predicates")(/* #__PURE__ */ discard1(/* #__PURE__ */ it("exactly one predicate is true for any value")(/* #__PURE__ */ quickCheck3(/* #__PURE__ */ bind(genRemoteDataStringInt)(function (rd) {
    var count = Data_Array.length(Data_Array.filter(identity)([ Hydrogen_Data_RemoteData.isNotAsked(rd), Hydrogen_Data_RemoteData.isLoading(rd), Hydrogen_Data_RemoteData.isFailure(rd), Hydrogen_Data_RemoteData.isSuccess(rd) ]));
    return pure(Test_QuickCheck.withHelp(count === 1)("Expected exactly one predicate true, got " + show(count)));
}))))(function () {
    return discard1(it("isSuccess implies toMaybe is Just")(quickCheck3(bind(genRemoteDataStringInt)(function (rd) {
        return pure(assertEquals1(Hydrogen_Data_RemoteData.isSuccess(rd))(Data_Maybe.isJust(Hydrogen_Data_RemoteData.toMaybe(rd))));
    }))))(function () {
        return it("fromEither . toEither preserves Success")(quickCheck5(function (v) {
            var rd = new Hydrogen_Data_RemoteData.Success(v);
            var roundtrip = Hydrogen_Data_RemoteData.fromEither(Hydrogen_Data_RemoteData.toEither("pending")(rd));
            return assertEquals2(roundtrip)(rd);
        }));
    });
})))(function () {
    return discard1(describe("Applicative priority")(discard1(it("Failure dominates over Loading")(quickCheck2(function (v) {
        var f = new Hydrogen_Data_RemoteData.Failure(v);
        return Hydrogen_Data_RemoteData.isFailure(apply(f)(Hydrogen_Data_RemoteData.Loading.value));
    })))(function () {
        return discard1(it("Failure dominates over NotAsked")(quickCheck2(function (v) {
            var f = new Hydrogen_Data_RemoteData.Failure(v);
            return Hydrogen_Data_RemoteData.isFailure(apply(f)(Hydrogen_Data_RemoteData.NotAsked.value));
        })))(function () {
            return discard1(it("Loading dominates over NotAsked")(quickCheck6(function (v) {
                return Hydrogen_Data_RemoteData.isLoading(apply(Hydrogen_Data_RemoteData.Loading.value)(Hydrogen_Data_RemoteData.NotAsked.value));
            })))(function () {
                return it("Success requires all Success")(quickCheck7(function (v) {
                    return function (v1) {
                        var sb = new Hydrogen_Data_RemoteData.Success(v1);
                        var sa = new Hydrogen_Data_RemoteData.Success(v);
                        var result = apply(map1(add)(sa))(sb);
                        return Hydrogen_Data_RemoteData.isSuccess(result);
                    };
                }));
            });
        });
    })))(function () {
        return discard1(describe("Semigroup semantics")(discard1(it("Success wins over non-Success")(quickCheck2(function (v) {
            var s = new Hydrogen_Data_RemoteData.Success(v);
            var f = new Hydrogen_Data_RemoteData.Failure("err");
            return Hydrogen_Data_RemoteData.isSuccess(append3(s)(Hydrogen_Data_RemoteData.Loading.value)) && (Hydrogen_Data_RemoteData.isSuccess(append3(Hydrogen_Data_RemoteData.Loading.value)(s)) && (Hydrogen_Data_RemoteData.isSuccess(append3(s)(f)) && (Hydrogen_Data_RemoteData.isSuccess(append3(f)(s)) && (Hydrogen_Data_RemoteData.isSuccess(append3(s)(Hydrogen_Data_RemoteData.NotAsked.value)) && Hydrogen_Data_RemoteData.isSuccess(append3(Hydrogen_Data_RemoteData.NotAsked.value)(s))))));
        })))(function () {
            return it("Failure beats Loading and NotAsked")(quickCheck2(function (v) {
                var f = new Hydrogen_Data_RemoteData.Failure(v);
                return Hydrogen_Data_RemoteData.isFailure(append3(f)(Hydrogen_Data_RemoteData.Loading.value)) && (Hydrogen_Data_RemoteData.isFailure(append3(Hydrogen_Data_RemoteData.Loading.value)(f)) && (Hydrogen_Data_RemoteData.isFailure(append3(f)(Hydrogen_Data_RemoteData.NotAsked.value)) && Hydrogen_Data_RemoteData.isFailure(append3(Hydrogen_Data_RemoteData.NotAsked.value)(f))));
            }));
        })))(function () {
            return describe("Foldable/Traversable")(discard1(it("foldr over Success yields 1 element")(quickCheck5(function (v) {
                return assertEquals3(foldr(function (v1) {
                    return function (acc) {
                        return acc + 1 | 0;
                    };
                })(0)(new Hydrogen_Data_RemoteData.Success(v)))(1);
            })))(function () {
                return discard1(it("foldr over non-Success yields 0 elements")(quickCheck3(bind(Test_QuickCheck_Gen.elements(Data_Array_NonEmpty["cons$prime"](Hydrogen_Data_RemoteData.NotAsked.value)([ Hydrogen_Data_RemoteData.Loading.value, new Hydrogen_Data_RemoteData.Failure("err") ])))(function (rd) {
                    return pure(assertEquals3(foldr(function (v) {
                        return function (acc) {
                            return acc + 1 | 0;
                        };
                    })(0)(rd))(0));
                }))))(function () {
                    return discard1(it("sequence with all Success is Success")(quickCheck3(bind(Test_QuickCheck_Gen.vectorOf(5)(arbitrary1))(function (vals) {
                        var rds = map2(Hydrogen_Data_RemoteData.Success.create)(vals);
                        var sequenced = sequence(rds);
                        return pure(Test_QuickCheck.withHelp(Hydrogen_Data_RemoteData.isSuccess(sequenced))("Expected Success from all-Success array"));
                    }))))(function () {
                        return it("sequence with any Failure is Failure")(quickCheck8(function (v) {
                            return function (v1) {
                                var rds = Data_Array.snoc(map2(Hydrogen_Data_RemoteData.Success.create)(v1))(new Hydrogen_Data_RemoteData.Failure(v));
                                var sequenced = sequence(rds);
                                return Test_QuickCheck.withHelp(Hydrogen_Data_RemoteData.isFailure(sequenced))("Expected Failure when array contains Failure");
                            };
                        }));
                    });
                });
            }));
        });
    });
}));

// ═══════════════════════════════════════════════════════════════════════════════
//                                               // RemoteData algebraic law tests
// ═══════════════════════════════════════════════════════════════════════════════
// Note: We test laws manually rather than using quickcheck-laws because we need
// custom generators and want more control over the error messages.
var remoteDataLaws = /* #__PURE__ */ describe("RemoteData Laws")(/* #__PURE__ */ discard1(/* #__PURE__ */ describe("Functor Laws")(/* #__PURE__ */ discard1(/* #__PURE__ */ it("identity: map id = id")(/* #__PURE__ */ quickCheck3(/* #__PURE__ */ bind(genRemoteDataStringInt)(function (rd) {
    return pure(assertEquals2(map1(identity)(rd))(rd));
}))))(function () {
    return it("composition: map (f . g) = map f . map g")(quickCheck3(bind(genRemoteDataStringInt)(function (rd) {
        return bind(genIntFunction)(function (f) {
            return bind(genIntFunction)(function (g) {
                return pure(assertEquals2(map1(function ($205) {
                    return f(g($205));
                })(rd))(map1(f)(map1(g)(rd))));
            });
        });
    })));
})))(function () {
    return discard1(describe("Applicative Laws")(discard1(it("identity: pure id <*> v = v")(quickCheck3(bind(genRemoteDataStringInt)(function (v) {
        return pure(assertEquals2(apply(pure2(identity))(v))(v));
    }))))(function () {
        return discard1(it("homomorphism: pure f <*> pure x = pure (f x)")(quickCheck3(bind(genIntFunction)(function (f) {
            return bind(arbitrary1)(function (x) {
                var lhs = apply(pure2(f))(pure2(x));
                var rhs = pure2(f(x));
                return pure(assertEquals2(lhs)(rhs));
            });
        }))))(function () {
            return discard1(it("interchange: u <*> pure y = pure ($ y) <*> u")(quickCheck3(bind(genRemoteData(genErrorString)(genIntFunction))(function (u) {
                return bind(arbitrary1)(function (y) {
                    var lhs = apply(u)(pure2(y));
                    var rhs = apply(pure2(function (v) {
                        return v(y);
                    }))(u);
                    return pure(assertEquals2(lhs)(rhs));
                });
            }))))(function () {
                return it("composition: pure (.) <*> u <*> v <*> w = u <*> (v <*> w)")(quickCheck3(bind(genRemoteData(genErrorString)(genIntFunction))(function (u) {
                    return bind(genRemoteData(genErrorString)(genIntFunction))(function (v) {
                        return bind(genRemoteDataStringInt)(function (w) {
                            var lhs = apply(apply(apply(pure2(compose))(u))(v))(w);
                            var rhs = apply(u)(apply(v)(w));
                            return pure(assertEquals2(lhs)(rhs));
                        });
                    });
                })));
            });
        });
    })))(function () {
        return discard1(describe("Monad Laws")(discard1(it("left identity: pure a >>= f = f a")(quickCheck3(bind(arbitrary1)(function (a) {
            return bind(genKleisli)(function (f) {
                var lhs = bind1(pure2(a))(f);
                var rhs = f(a);
                return pure(assertEquals2(lhs)(rhs));
            });
        }))))(function () {
            return discard1(it("right identity: m >>= pure = m")(quickCheck3(bind(genRemoteDataStringInt)(function (m) {
                return pure(assertEquals2(bind1(m)(pure2))(m));
            }))))(function () {
                return it("associativity: (m >>= f) >>= g = m >>= (\\x -> f x >>= g)")(quickCheck3(bind(genRemoteDataStringInt)(function (m) {
                    return bind(genKleisli)(function (f) {
                        return bind(genKleisli)(function (g) {
                            var lhs = bind1(bind1(m)(f))(g);
                            var rhs = bind1(m)(function (x) {
                                return bind1(f(x))(g);
                            });
                            return pure(assertEquals2(lhs)(rhs));
                        });
                    });
                })));
            });
        })))(function () {
            return discard1(describe("Semigroup Laws")(it("associativity: (x <> y) <> z = x <> (y <> z)")(quickCheck3(bind(genRemoteData(genErrorString)(arbitrary))(function (x) {
                return bind(genRemoteData(genErrorString)(arbitrary))(function (y) {
                    return bind(genRemoteData(genErrorString)(arbitrary))(function (z) {
                        var lhs = append3(append3(x)(y))(z);
                        var rhs = append3(x)(append3(y)(z));
                        return pure(assertEquals4(lhs)(rhs));
                    });
                });
            })))))(function () {
                return discard1(describe("Monoid Laws")(discard1(it("left identity: mempty <> x = x")(quickCheck3(bind(genRemoteData(genErrorString)(arbitrary))(function (x) {
                    return pure(assertEquals4(append3(mempty1)(x))(x));
                }))))(function () {
                    return it("right identity: x <> mempty = x")(quickCheck3(bind(genRemoteData(genErrorString)(arbitrary))(function (x) {
                        return pure(assertEquals4(append3(x)(mempty1))(x));
                    })));
                })))(function () {
                    return discard1(describe("Alt Laws")(discard1(it("associativity: (x <|> y) <|> z = x <|> (y <|> z)")(quickCheck3(bind(genRemoteDataStringInt)(function (x) {
                        return bind(genRemoteDataStringInt)(function (y) {
                            return bind(genRemoteDataStringInt)(function (z) {
                                var lhs = alt(alt(x)(y))(z);
                                var rhs = alt(x)(alt(y)(z));
                                return pure(assertEquals2(lhs)(rhs));
                            });
                        });
                    }))))(function () {
                        return it("distributivity: f <$> (x <|> y) = (f <$> x) <|> (f <$> y)")(quickCheck3(bind(genIntFunction)(function (f) {
                            return bind(genRemoteDataStringInt)(function (x) {
                                return bind(genRemoteDataStringInt)(function (y) {
                                    var lhs = map1(f)(alt(x)(y));
                                    var rhs = alt(map1(f)(x))(map1(f)(y));
                                    return pure(assertEquals2(lhs)(rhs));
                                });
                            });
                        })));
                    })))(function () {
                        return describe("Plus Laws")(discard1(it("left identity: empty <|> x = x")(quickCheck3(bind(genRemoteDataStringInt)(function (x) {
                            return pure(assertEquals2(alt(empty)(x))(x));
                        }))))(function () {
                            return discard1(it("right identity: x <|> empty = x")(quickCheck3(bind(genRemoteDataStringInt)(function (x) {
                                return pure(assertEquals2(alt(x)(empty))(x));
                            }))))(function () {
                                return it("annihilation: empty <*> x = empty")((function () {
                                    var lhs = apply(empty)(new Hydrogen_Data_RemoteData.Success(42));
                                    return shouldEqual4(lhs)(empty);
                                })());
                            });
                        }));
                    });
                });
            });
        });
    });
}));

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // stress tests
// ═══════════════════════════════════════════════════════════════════════════════
var stressTests = /* #__PURE__ */ describe("Stress Tests")(/* #__PURE__ */ discard1(/* #__PURE__ */ describe("Large data structures")(/* #__PURE__ */ discard1(/* #__PURE__ */ it("sequence handles large arrays")(/* #__PURE__ */ quickCheck3(/* #__PURE__ */ bind(/* #__PURE__ */ Test_QuickCheck_Gen.vectorOf(100)(genRemoteDataStringInt))(function (rds) {
    var v = sequence(rds);
    return pure(assertEquals1(true)(true));
}))))(function () {
    return discard1(it("deeply nested bind doesn't stack overflow")((function () {
        var nested = foldl(function (acc) {
            return function (v) {
                return bind1(acc)(function (x) {
                    return new Hydrogen_Data_RemoteData.Success(x + 1 | 0);
                });
            };
        })(new Hydrogen_Data_RemoteData.Success(0))(Data_Array.replicate(1000)(Data_Unit.unit));
        if (nested instanceof Hydrogen_Data_RemoteData.Success) {
            return shouldEqual5(nested.value0)(1000);
        };
        return pure1(Data_Unit.unit);
    })()))(function () {
        return it("many validators composed")((function () {
            var validators = foldl(append1)(mempty)(Data_Array.replicate(100)(Hydrogen_Form_Validation.minLength(1)("err")));
            return shouldEqual2(Hydrogen_Form_Validation.isValid(Hydrogen_Form_Validation.validate(validators)("hello")))(true);
        })());
    });
})))(function () {
    return describe("Adversarial inputs")(discard1(it("RemoteData with adversarial distribution")(quickCheck3(bind(genRemoteDataAdversarial(genErrorString)(arbitrary1))(function (rd) {
        return pure(assertEquals2(bind1(rd)(pure2))(rd));
    }))))(function () {
        return it("HSL with adversarial values")(quickCheck3(bind(genHSLAdversarial)(function (c) {
            var v = Hydrogen_Style_Color.lighten(10.0)(c);
            var v1 = Hydrogen_Style_Color.darken(10.0)(c);
            var v2 = Hydrogen_Style_Color.contrastColor(c);
            return pure(assertEquals1(true)(true));
        })));
    }));
}));

// | Duration in seconds with realistic distribution
var genDurationSecs = /* #__PURE__ */ (function () {
    return Test_QuickCheck_Gen.frequency(Data_Array_NonEmpty["cons$prime"](new Data_Tuple.Tuple(10.0, pure(0)))([ new Data_Tuple.Tuple(5.0, pure(-1 | 0)), new Data_Tuple.Tuple(20.0, Test_QuickCheck_Gen.chooseInt(1)(59)), new Data_Tuple.Tuple(25.0, Test_QuickCheck_Gen.chooseInt(60)(3599)), new Data_Tuple.Tuple(25.0, Test_QuickCheck_Gen.chooseInt(3600)(86399)), new Data_Tuple.Tuple(10.0, Test_QuickCheck_Gen.chooseInt(86400)(604800)), new Data_Tuple.Tuple(5.0, arbitrary1) ]));
})();

// | Byte values with realistic distribution
var genBytes = /* #__PURE__ */ (function () {
    return Test_QuickCheck_Gen.frequency(Data_Array_NonEmpty["cons$prime"](new Data_Tuple.Tuple(5.0, pure(0.0)))([ new Data_Tuple.Tuple(5.0, pure(-1.0)), new Data_Tuple.Tuple(5.0, pure(0.5)), new Data_Tuple.Tuple(5.0, pure(1023.9)), new Data_Tuple.Tuple(10.0, map(Data_Int.toNumber)(Test_QuickCheck_Gen.chooseInt(0)(1023))), new Data_Tuple.Tuple(15.0, map(function (n) {
        return Data_Int.toNumber(n) * Hydrogen_Data_Format.kb;
    })(Test_QuickCheck_Gen.chooseInt(1)(1023))), new Data_Tuple.Tuple(20.0, map(function (n) {
        return Data_Int.toNumber(n) * Hydrogen_Data_Format.mb;
    })(Test_QuickCheck_Gen.chooseInt(1)(1023))), new Data_Tuple.Tuple(20.0, map(function (n) {
        return Data_Int.toNumber(n) * Hydrogen_Data_Format.gb;
    })(Test_QuickCheck_Gen.chooseInt(1)(100))), new Data_Tuple.Tuple(10.0, map(function (n) {
        return Data_Int.toNumber(n) * Hydrogen_Data_Format.tb;
    })(Test_QuickCheck_Gen.chooseInt(1)(10))), new Data_Tuple.Tuple(5.0, map(Data_Int.toNumber)(Test_QuickCheck_Gen.chooseInt(-1000000 | 0)(1000000000))) ]));
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                        // Format property tests
// ═══════════════════════════════════════════════════════════════════════════════
var formatProperties = /* #__PURE__ */ describe("Format Properties")(/* #__PURE__ */ discard1(/* #__PURE__ */ describe("Byte formatting")(/* #__PURE__ */ discard1(/* #__PURE__ */ it("formatBytes always produces valid output")(/* #__PURE__ */ quickCheck3(/* #__PURE__ */ bind(genBytes)(function (bytes) {
    var result = Hydrogen_Data_Format.formatBytes(bytes);
    return pure(Test_QuickCheck.withHelp(Data_String_CodePoints.length(result) > 0)("Empty output for " + show1(bytes)));
}))))(function () {
    return discard1(it("formatBytes handles negative by prepending -")(quickCheck3(bind(map(Data_Int.toNumber)(Test_QuickCheck_Gen.chooseInt(1)(1000000)))(function (n) {
        var negative = Hydrogen_Data_Format.formatBytes(-n);
        return pure(assertEquals5(Data_String_CodePoints.take(1)(negative))("-"));
    }))))(function () {
        return discard1(it("formatBytes for 0 is '0 B'")(shouldEqual3(Hydrogen_Data_Format.formatBytes(0.0))("0 B")))(function () {
            return discard1(it("formatBytes boundary: 1023 bytes is still bytes")(shouldEqual2(Data_String_CodeUnits.contains(" B")(Hydrogen_Data_Format.formatBytes(1023.0)))(true)))(function () {
                return discard1(it("formatBytes boundary: 1024 bytes is 1 KB")(shouldEqual3(Hydrogen_Data_Format.formatBytes(1024.0))("1.0 KB")))(function () {
                    return discard1(it("formatBytes unit thresholds are correct")(discard2(shouldEqual2(Data_String_CodeUnits.contains("KB")(Hydrogen_Data_Format.formatBytes(Hydrogen_Data_Format.kb - 1.0)))(false))(function () {
                        return shouldEqual2(Data_String_CodeUnits.contains("KB")(Hydrogen_Data_Format.formatBytes(Hydrogen_Data_Format.kb)))(true);
                    })))(function () {
                        return it("formatBytesCompact has no spaces")(quickCheck3(bind(genBytes)(function (bytes) {
                            var result = Hydrogen_Data_Format.formatBytesCompact(bytes);
                            return pure(Test_QuickCheck.withHelp(!Data_String_CodeUnits.contains(" ")(result))("Found space in compact format: " + result));
                        })));
                    });
                });
            });
        });
    });
})))(function () {
    return discard1(describe("Number formatting")(discard1(it("formatNum always produces valid output")(quickCheck9(function (v) {
        return Data_String_CodePoints.length(Hydrogen_Data_Format.formatNum(v)) > 0;
    })))(function () {
        return discard1(it("formatNumCompact thresholds")(discard2(shouldEqual2(Data_String_CodeUnits.contains("k")(Hydrogen_Data_Format.formatNumCompact(999.0)))(false))(function () {
            return discard2(shouldEqual2(Data_String_CodeUnits.contains("k")(Hydrogen_Data_Format.formatNumCompact(1000.0)))(true))(function () {
                return discard2(shouldEqual2(Data_String_CodeUnits.contains("M")(Hydrogen_Data_Format.formatNumCompact(999999.0)))(false))(function () {
                    return shouldEqual2(Data_String_CodeUnits.contains("M")(Hydrogen_Data_Format.formatNumCompact(1000000.0)))(true);
                });
            });
        })))(function () {
            return it("formatPercent is in range 0-100+ for valid input")(quickCheck3(bind(map(Data_Int.toNumber)(Test_QuickCheck_Gen.chooseInt(0)(100)))(function (r) {
                var rate = r / 100.0;
                var result = Hydrogen_Data_Format.formatPercent(rate);
                return pure(Test_QuickCheck.withHelp(Data_String_CodeUnits.contains("%")(result))("Missing % in " + result));
            })));
        });
    })))(function () {
        return discard1(describe("Duration formatting")(discard1(it("formatDuration 0 is '-'")(shouldEqual3(Hydrogen_Data_Format.formatDuration(0))("-")))(function () {
            return discard1(it("formatDuration negative is '-'")(quickCheck3(bind(Test_QuickCheck_Gen.chooseInt(-1000 | 0)(-1 | 0))(function (n) {
                return pure(assertEquals5(Hydrogen_Data_Format.formatDuration(n))("-"));
            }))))(function () {
                return discard1(it("formatDuration includes 's' for seconds")(quickCheck3(bind(Test_QuickCheck_Gen.chooseInt(1)(59))(function (secs) {
                    var result = Hydrogen_Data_Format.formatDuration(secs);
                    return pure(Test_QuickCheck.withHelp(Data_String_CodeUnits.contains("s")(result))("Missing 's' in " + result));
                }))))(function () {
                    return discard1(it("formatDuration includes 'm' for minutes")(quickCheck3(bind(Test_QuickCheck_Gen.chooseInt(60)(3599))(function (secs) {
                        var result = Hydrogen_Data_Format.formatDuration(secs);
                        return pure(Test_QuickCheck.withHelp(Data_String_CodeUnits.contains("m")(result))("Missing 'm' in " + result));
                    }))))(function () {
                        return discard1(it("formatDuration includes 'h' for hours")(quickCheck3(bind(Test_QuickCheck_Gen.chooseInt(3600)(86399))(function (secs) {
                            var result = Hydrogen_Data_Format.formatDuration(secs);
                            return pure(Test_QuickCheck.withHelp(Data_String_CodeUnits.contains("h")(result))("Missing 'h' in " + result));
                        }))))(function () {
                            return it("formatDurationMs is formatDuration / 1000")(quickCheck3(bind(Test_QuickCheck_Gen.chooseInt(0)(10000))(function (secs) {
                                var ms = secs * 1000 | 0;
                                return pure(assertEquals5(Hydrogen_Data_Format.formatDurationMs(ms))(Hydrogen_Data_Format.formatDuration(secs)));
                            })));
                        });
                    });
                });
            });
        })))(function () {
            return describe("Calculation safety")(discard1(it("percentage handles zero denominator")(shouldEqual5(Hydrogen_Data_Format.percentage(1.0)(0.0))(0)))(function () {
                return discard1(it("percentage with current > limit gives > 100")(shouldEqual5(Hydrogen_Data_Format.percentage(150.0)(100.0))(150)))(function () {
                    return discard1(it("rate handles zero total")(shouldEqual6(Hydrogen_Data_Format.rate(1)(0))(0.0)))(function () {
                        return discard1(it("rate returns value in 0-1 range for valid inputs")(quickCheck3(bind(Test_QuickCheck_Gen.chooseInt(0)(100))(function (success) {
                            return bind(Test_QuickCheck_Gen.chooseInt(1)(100))(function (total) {
                                var r = Hydrogen_Data_Format.rate(success)(total);
                                return pure(Test_QuickCheck.withHelp(r >= 0.0 && r <= 1.0 || success > total)("Rate out of expected range: " + show1(r)));
                            });
                        }))))(function () {
                            return discard1(it("ratio handles zero denominator")(shouldEqual6(Hydrogen_Data_Format.ratio(1.0)(0.0))(0.0)))(function () {
                                return discard1(it("ratio computes correctly")(discard2(shouldEqual6(Hydrogen_Data_Format.ratio(3.0)(4.0))(0.75))(function () {
                                    return shouldEqual6(Hydrogen_Data_Format.ratio(1.0)(3.0))(1.0 / 3.0);
                                })))(function () {
                                    return it("percentage is between 0 and 100 for valid inputs")(quickCheck3(bind(map(Data_Int.toNumber)(Test_QuickCheck_Gen.chooseInt(0)(1000)))(function (current) {
                                        return bind(map(Data_Int.toNumber)(Test_QuickCheck_Gen.chooseInt(1)(1000)))(function (limit) {
                                            var pct = Hydrogen_Data_Format.percentage(current)(limit);
                                            return pure(Test_QuickCheck.withHelp(pct >= 0)("Percentage below 0: " + show(pct)));
                                        });
                                    })));
                                });
                            });
                        });
                    });
                });
            }));
        });
    });
}));
var eqArbRemoteData = function (dictEq) {
    var eqRemoteData2 = Hydrogen_Data_RemoteData.eqRemoteData(dictEq);
    return function (dictEq1) {
        var eq2 = Data_Eq.eq(eqRemoteData2(dictEq1));
        return {
            eq: function (x) {
                return function (y) {
                    return eq2(x)(y);
                };
            }
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                         // Color property tests
// ═══════════════════════════════════════════════════════════════════════════════
var colorProperties = /* #__PURE__ */ describe("Color Properties")(/* #__PURE__ */ discard1(/* #__PURE__ */ describe("HSL manipulation bounds")(/* #__PURE__ */ discard1(/* #__PURE__ */ it("lighten never exceeds 100")(/* #__PURE__ */ quickCheck3(/* #__PURE__ */ bind(genHSL)(function (c) {
    return bind(map(Data_Int.toNumber)(Test_QuickCheck_Gen.chooseInt(0)(200)))(function (amount) {
        var result = Hydrogen_Style_Color.lighten(amount)(c);
        return pure(Test_QuickCheck.withHelp(result.l <= 100.0)("Lightness exceeded 100: " + show1(result.l)));
    });
}))))(function () {
    return discard1(it("darken never goes below 0")(quickCheck3(bind(genHSL)(function (c) {
        return bind(map(Data_Int.toNumber)(Test_QuickCheck_Gen.chooseInt(0)(200)))(function (amount) {
            var result = Hydrogen_Style_Color.darken(amount)(c);
            return pure(Test_QuickCheck.withHelp(result.l >= 0.0)("Lightness went below 0: " + show1(result.l)));
        });
    }))))(function () {
        return discard1(it("saturate never exceeds 100")(quickCheck3(bind(genHSL)(function (c) {
            return bind(map(Data_Int.toNumber)(Test_QuickCheck_Gen.chooseInt(0)(200)))(function (amount) {
                var result = Hydrogen_Style_Color.saturate(amount)(c);
                return pure(Test_QuickCheck.withHelp(result.s <= 100.0)("Saturation exceeded 100: " + show1(result.s)));
            });
        }))))(function () {
            return discard1(it("desaturate never goes below 0")(quickCheck3(bind(genHSL)(function (c) {
                return bind(map(Data_Int.toNumber)(Test_QuickCheck_Gen.chooseInt(0)(200)))(function (amount) {
                    var result = Hydrogen_Style_Color.desaturate(amount)(c);
                    return pure(Test_QuickCheck.withHelp(result.s >= 0.0)("Saturation went below 0: " + show1(result.s)));
                });
            }))))(function () {
                return it("opacity is clamped to 0-100")(quickCheck3(bind(genHSL)(function (c) {
                    return bind(Test_QuickCheck_Gen.elements(Data_Array_NonEmpty["cons$prime"](-50.0)([ 0.0, 50.0, 100.0, 150.0, 200.0 ])))(function (a) {
                        var result = Hydrogen_Style_Color.opacity(a)(c);
                        return pure(Test_QuickCheck.withHelp(result.a >= 0.0 && result.a <= 100.0)("Alpha out of bounds: " + show1(result.a)));
                    });
                })));
            });
        });
    });
})))(function () {
    return describe("Metamorphic properties")(discard1(it("lighten then darken by same amount returns original (within bounds)")(quickCheck3(bind(genHSL)(function (c) {
        var c$prime = {
            a: c.a,
            h: c.h,
            s: c.s,
            l: 50.0
        };
        return bind(map(Data_Int.toNumber)(Test_QuickCheck_Gen.chooseInt(0)(40)))(function (amount) {
            var result = Hydrogen_Style_Color.darken(amount)(Hydrogen_Style_Color.lighten(amount)(c$prime));
            return pure(Test_QuickCheck.withHelp(result.l - c$prime.l < 1.0e-3 && result.l - c$prime.l > -1.0e-3)("Expected " + (show1(c$prime.l) + (" got " + show1(result.l)))));
        });
    }))))(function () {
        return discard1(it("contrastColor returns black or white")(quickCheck3(bind(genHSL)(function (c) {
            var contrast = Hydrogen_Style_Color.contrastColor(c);
            return pure(Test_QuickCheck.withHelp(contrast.l === 0.0 || contrast.l === 100.0)("Contrast color should be black or white, got l=" + show1(contrast.l)));
        }))))(function () {
            return it("contrastColor threshold at l=55")(quickCheck3(bind(map(Data_Int.toNumber)(Test_QuickCheck_Gen.chooseInt(0)(100)))(function (l) {
                var c = Hydrogen_Style_Color.hsl(0.0)(0.0)(l);
                var contrast = Hydrogen_Style_Color.contrastColor(c);
                var expected = (function () {
                    var $202 = l > 55.0;
                    if ($202) {
                        return 0.0;
                    };
                    return 100.0;
                })();
                return pure(assertEquals6(contrast.l)(expected));
            })));
        });
    }));
}));

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // exports
// ═══════════════════════════════════════════════════════════════════════════════
var propertyTests = /* #__PURE__ */ discard1(remoteDataLaws)(function () {
    return discard1(remoteDataInvariants)(function () {
        return discard1(colorProperties)(function () {
            return discard1(formatProperties)(function () {
                return discard1(validationProperties)(function () {
                    return stressTests;
                });
            });
        });
    });
});
var arbRemoteDataStringInt = {
    arbitrary: /* #__PURE__ */ map(ArbRemoteData)(genRemoteDataStringInt)
};
export {
    genRemoteData,
    genRemoteDataAdversarial,
    genRemoteDataStringInt,
    genErrorString,
    genIntFunction,
    genKleisli,
    genHSL,
    genHSLAdversarial,
    genBytes,
    genDurationSecs,
    genValidationString,
    remoteDataLaws,
    remoteDataInvariants,
    colorProperties,
    formatProperties,
    validationProperties,
    stressTests,
    propertyTests,
    ArbRemoteData,
    eqArbRemoteData,
    arbRemoteDataStringInt
};
