// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                           // hydrogen // atom
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Atomic state management inspired by Jotai/Recoil
// |
// | Atoms are the smallest unit of state. They can be read, written, and
// | subscribed to. Derived atoms compute values from other atoms.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.State.Atom as Atom
// |
// | -- Create an atom
// | countAtom <- Atom.atom 0
// |
// | -- Read value
// | count <- Atom.get countAtom
// |
// | -- Update value
// | Atom.set countAtom 5
// | Atom.modify countAtom (_ + 1)
// |
// | -- Subscribe to changes
// | unsubscribe <- Atom.subscribe countAtom \newValue ->
// |   Console.log $ "Count changed to: " <> show newValue
// |
// | -- Derived atoms
// | doubledAtom <- Atom.derived countAtom (\n -> n * 2)
// | ```
import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Control_Bind from "../Control.Bind/index.js";
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Data_Map_Internal from "../Data.Map.Internal/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
import * as Effect from "../Effect/index.js";
import * as Effect_Aff from "../Effect.Aff/index.js";
import * as Effect_Class from "../Effect.Class/index.js";
import * as Effect_Ref from "../Effect.Ref/index.js";
var bindFlipped = /* #__PURE__ */ Control_Bind.bindFlipped(Effect.bindEffect);
var pure = /* #__PURE__ */ Control_Applicative.pure(Effect.applicativeEffect);
var insert = /* #__PURE__ */ Data_Map_Internal.insert(Data_Ord.ordString);
var $$void = /* #__PURE__ */ Data_Functor["void"](Effect.functorEffect);
var foldM = /* #__PURE__ */ Data_Array.foldM(Effect.monadEffect);
var lookup = /* #__PURE__ */ Data_Map_Internal.lookup(Data_Ord.ordString);
var bind1 = /* #__PURE__ */ Control_Bind.bind(Effect_Aff.bindAff);
var liftEffect = /* #__PURE__ */ Effect_Class.liftEffect(Effect_Aff.monadEffectAff);

// | A store holds multiple atoms and enables snapshots
var AtomStore = function (x) {
    return x;
};

// | An atom holds a single piece of state
var Atom = function (x) {
    return x;
};

// | A read-only view of an atom (for derived atoms exposed publicly)
var ReadOnlyAtom = function (x) {
    return x;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // utilities
// ═══════════════════════════════════════════════════════════════════════════════
// | Convert an atom to read-only
var toReadOnly = ReadOnlyAtom;

// | Subscribe with access to previous value
var subscribeWithPrevious = function (v) {
    return function (callback) {
        return function __do() {
            var prevRef = bindFlipped(Effect_Ref["new"])(Effect_Ref.read(v.ref))();
            var id = Effect_Ref.read(v.nextId)();
            Effect_Ref.write(id + 1 | 0)(v.nextId)();
            var wrappedCallback = function (newVal) {
                return function __do() {
                    var prev = Effect_Ref.read(prevRef)();
                    Effect_Ref.write(newVal)(prevRef)();
                    return callback(prev)(newVal)();
                };
            };
            var sub = {
                id: id,
                callback: wrappedCallback
            };
            Effect_Ref.modify_(Data_Array.cons(sub))(v.subscribers)();
            return Effect_Ref.modify_(Data_Array.filter(function (s) {
                return s.id !== id;
            }))(v.subscribers);
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // subscriptions
// ═══════════════════════════════════════════════════════════════════════════════
// | Subscribe to atom changes, returns unsubscribe function
var subscribe = function (v) {
    return function (callback) {
        return function __do() {
            var id = Effect_Ref.read(v.nextId)();
            Effect_Ref.write(id + 1 | 0)(v.nextId)();
            var sub = {
                id: id,
                callback: callback
            };
            Effect_Ref.modify_(Data_Array.cons(sub))(v.subscribers)();
            return Effect_Ref.modify_(Data_Array.filter(function (s) {
                return s.id !== id;
            }))(v.subscribers);
        };
    };
};

// | Take a snapshot of an atom's value (requires Show instance)
var snapshot = function (dictShow) {
    var show = Data_Show.show(dictShow);
    return function (v) {
        return function (v1) {
            if (v1.key instanceof Data_Maybe.Nothing) {
                return pure(Data_Unit.unit);
            };
            if (v1.key instanceof Data_Maybe.Just) {
                return function __do() {
                    var val = Effect_Ref.read(v1.ref)();
                    var snapshotRef = Effect_Ref["new"](show(val))();
                    return Effect_Ref.modify_(insert(v1.key.value0)(snapshotRef))(v.atoms)();
                };
            };
            throw new Error("Failed pattern match at Hydrogen.State.Atom (line 311, column 3 - line 316, column 51): " + [ v1.key.constructor.name ]);
        };
    };
};

// | Set the value of an atom
var set = function (v) {
    return function (newValue) {
        var for_ = function (arr) {
            return function (f) {
                return $$void(foldM(function (v1) {
                    return function (x) {
                        return f(x);
                    };
                })(Data_Unit.unit)(arr));
            };
        };
        return function __do() {
            Effect_Ref.write(newValue)(v.ref)();
            var subs = Effect_Ref.read(v.subscribers)();
            return for_(subs)(function (sub) {
                return sub.callback(newValue);
            })();
        };
    };
};

// | Restore atom from snapshot (requires Read instance - simplified here)
var restore = function (v) {
    return function (v1) {
        return function (parse) {
            if (v1.key instanceof Data_Maybe.Nothing) {
                return pure(Data_Unit.unit);
            };
            if (v1.key instanceof Data_Maybe.Just) {
                return function __do() {
                    var atomMap = Effect_Ref.read(v.atoms)();
                    var v2 = lookup(v1.key.value0)(atomMap);
                    if (v2 instanceof Data_Maybe.Nothing) {
                        return Data_Unit.unit;
                    };
                    if (v2 instanceof Data_Maybe.Just) {
                        var serialized = Effect_Ref.read(v2.value0)();
                        var v3 = parse(serialized);
                        if (v3 instanceof Data_Maybe.Nothing) {
                            return Data_Unit.unit;
                        };
                        if (v3 instanceof Data_Maybe.Just) {
                            return set(v1)(v3.value0)();
                        };
                        throw new Error("Failed pattern match at Hydrogen.State.Atom (line 329, column 11 - line 331, column 34): " + [ v3.constructor.name ]);
                    };
                    throw new Error("Failed pattern match at Hydrogen.State.Atom (line 325, column 7 - line 331, column 34): " + [ v2.constructor.name ]);
                };
            };
            throw new Error("Failed pattern match at Hydrogen.State.Atom (line 321, column 3 - line 331, column 34): " + [ v1.key.constructor.name ]);
        };
    };
};

// | Reset an atom to its initial value
var reset = function (v) {
    return set(v)(v.initial);
};

// | Helper to run effect when atom changes (returns cleanup)
var onChange = subscribe;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // store management
// ═══════════════════════════════════════════════════════════════════════════════
// | Create a new atom store
var newStore = function __do() {
    var atoms = Effect_Ref["new"](Data_Map_Internal.empty)();
    return {
        atoms: atoms
    };
};

// | Modify the value of an atom with a function
var modify = function (v) {
    return function (f) {
        return function __do() {
            var current = Effect_Ref.read(v.ref)();
            return set(v)(f(current))();
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                             // atom operations
// ═══════════════════════════════════════════════════════════════════════════════
// | Get the current value of an atom
var get = function (v) {
    return Effect_Ref.read(v.ref);
};

// | Create a derived atom from three source atoms
var derivedFrom3 = function (v) {
    return function (v1) {
        return function (v2) {
            return function (f) {
                var for_ = function (arr) {
                    return function (f$prime) {
                        return $$void(foldM(function (v3) {
                            return function (x) {
                                return f$prime(x);
                            };
                        })(Data_Unit.unit)(arr));
                    };
                };
                return function __do() {
                    var v11 = Effect_Ref.read(v.ref)();
                    var v21 = Effect_Ref.read(v1.ref)();
                    var v3 = Effect_Ref.read(v2.ref)();
                    var initialDerived = f(v11)(v21)(v3);
                    var derivedRef = Effect_Ref["new"](initialDerived)();
                    var derivedSubs = Effect_Ref["new"]([  ])();
                    var derivedNextId = Effect_Ref["new"](0)();
                    var doUpdate = function __do() {
                        var newV1 = Effect_Ref.read(v.ref)();
                        var newV2 = Effect_Ref.read(v1.ref)();
                        var newV3 = Effect_Ref.read(v2.ref)();
                        var newDerived = f(newV1)(newV2)(newV3);
                        Effect_Ref.write(newDerived)(derivedRef)();
                        var subs = Effect_Ref.read(derivedSubs)();
                        return for_(subs)(function (sub) {
                            return sub.callback(newDerived);
                        })();
                    };
                    var id1 = Effect_Ref.read(v.nextId)();
                    Effect_Ref.write(id1 + 1 | 0)(v.nextId)();
                    Effect_Ref.modify_(Data_Array.cons({
                        id: id1,
                        callback: function (v4) {
                            return doUpdate;
                        }
                    }))(v.subscribers)();
                    var id2 = Effect_Ref.read(v1.nextId)();
                    Effect_Ref.write(id2 + 1 | 0)(v1.nextId)();
                    Effect_Ref.modify_(Data_Array.cons({
                        id: id2,
                        callback: function (v4) {
                            return doUpdate;
                        }
                    }))(v1.subscribers)();
                    var id3 = Effect_Ref.read(v2.nextId)();
                    Effect_Ref.write(id3 + 1 | 0)(v2.nextId)();
                    Effect_Ref.modify_(Data_Array.cons({
                        id: id3,
                        callback: function (v4) {
                            return doUpdate;
                        }
                    }))(v2.subscribers)();
                    return {
                        ref: derivedRef,
                        initial: initialDerived,
                        key: Data_Maybe.Nothing.value,
                        subscribers: derivedSubs,
                        nextId: derivedNextId
                    };
                };
            };
        };
    };
};

// | Create a derived atom from two source atoms
var derivedFrom2 = function (v) {
    return function (v1) {
        return function (f) {
            var for_ = function (arr) {
                return function (f$prime) {
                    return $$void(foldM(function (v2) {
                        return function (x) {
                            return f$prime(x);
                        };
                    })(Data_Unit.unit)(arr));
                };
            };
            return function __do() {
                var v11 = Effect_Ref.read(v.ref)();
                var v2 = Effect_Ref.read(v1.ref)();
                var initialDerived = f(v11)(v2);
                var derivedRef = Effect_Ref["new"](initialDerived)();
                var derivedSubs = Effect_Ref["new"]([  ])();
                var derivedNextId = Effect_Ref["new"](0)();
                var doUpdate = function __do() {
                    var newV1 = Effect_Ref.read(v.ref)();
                    var newV2 = Effect_Ref.read(v1.ref)();
                    var newDerived = f(newV1)(newV2);
                    Effect_Ref.write(newDerived)(derivedRef)();
                    var subs = Effect_Ref.read(derivedSubs)();
                    return for_(subs)(function (sub) {
                        return sub.callback(newDerived);
                    })();
                };
                var id1 = Effect_Ref.read(v.nextId)();
                Effect_Ref.write(id1 + 1 | 0)(v.nextId)();
                Effect_Ref.modify_(Data_Array.cons({
                    id: id1,
                    callback: function (v3) {
                        return doUpdate;
                    }
                }))(v.subscribers)();
                var id2 = Effect_Ref.read(v1.nextId)();
                Effect_Ref.write(id2 + 1 | 0)(v1.nextId)();
                Effect_Ref.modify_(Data_Array.cons({
                    id: id2,
                    callback: function (v3) {
                        return doUpdate;
                    }
                }))(v1.subscribers)();
                return {
                    ref: derivedRef,
                    initial: initialDerived,
                    key: Data_Maybe.Nothing.value,
                    subscribers: derivedSubs,
                    nextId: derivedNextId
                };
            };
        };
    };
};

// | Create a derived atom that computes from another atom
var derived = function (v) {
    return function (f) {
        var for_ = function (arr) {
            return function (f$prime) {
                return $$void(foldM(function (v1) {
                    return function (x) {
                        return f$prime(x);
                    };
                })(Data_Unit.unit)(arr));
            };
        };
        return function __do() {
            var sourceVal = Effect_Ref.read(v.ref)();
            var initialDerived = f(sourceVal);
            var derivedRef = Effect_Ref["new"](initialDerived)();
            var derivedSubs = Effect_Ref["new"]([  ])();
            var derivedNextId = Effect_Ref["new"](0)();
            var updateDerived = function (newSource) {
                var newDerived = f(newSource);
                return function __do() {
                    Effect_Ref.write(newDerived)(derivedRef)();
                    var subs = Effect_Ref.read(derivedSubs)();
                    return for_(subs)(function (sub) {
                        return sub.callback(newDerived);
                    })();
                };
            };
            var sourceId = Effect_Ref.read(v.nextId)();
            Effect_Ref.write(sourceId + 1 | 0)(v.nextId)();
            Effect_Ref.modify_(Data_Array.cons({
                id: sourceId,
                callback: updateDerived
            }))(v.subscribers)();
            return {
                ref: derivedRef,
                initial: initialDerived,
                key: Data_Maybe.Nothing.value,
                subscribers: derivedSubs,
                nextId: derivedNextId
            };
        };
    };
};

// | Create an atom with a key for persistence/debugging
var atomWithKey = function (key) {
    return function (initial) {
        return function __do() {
            var ref = Effect_Ref["new"](initial)();
            var subscribers = Effect_Ref["new"]([  ])();
            var nextId = Effect_Ref["new"](0)();
            return {
                ref: ref,
                initial: initial,
                key: new Data_Maybe.Just(key),
                subscribers: subscribers,
                nextId: nextId
            };
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // atom creation
// ═══════════════════════════════════════════════════════════════════════════════
// | Create a new atom with an initial value
var atom = function (initial) {
    return function __do() {
        var ref = Effect_Ref["new"](initial)();
        var subscribers = Effect_Ref["new"]([  ])();
        var nextId = Effect_Ref["new"](0)();
        return {
            ref: ref,
            initial: initial,
            key: Data_Maybe.Nothing.value,
            subscribers: subscribers,
            nextId: nextId
        };
    };
};

// | Create an async atom that fetches data
var asyncAtom = function (initial) {
    return function (fetchFn) {
        return function __do() {
            var atomRef = atom(initial)();
            Effect_Aff.launchAff_(bind1(fetchFn)(function (result) {
                return liftEffect(set(atomRef)(result));
            }))();
            return atomRef;
        };
    };
};
export {
    atom,
    atomWithKey,
    derived,
    derivedFrom2,
    derivedFrom3,
    asyncAtom,
    get,
    set,
    modify,
    reset,
    subscribe,
    subscribeWithPrevious,
    newStore,
    snapshot,
    restore,
    toReadOnly,
    onChange
};
