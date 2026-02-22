// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                          // hydrogen // store
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Redux-style centralized store with actions and reducers
// |
// | For applications that prefer a single source of truth with
// | predictable state updates via actions.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.State.Store as Store
// |
// | -- Define your state
// | type AppState = { count :: Int, user :: Maybe User }
// |
// | -- Define actions
// | data Action = Increment | Decrement | SetUser User | Logout
// |
// | -- Define reducer
// | reducer :: AppState -> Action -> AppState
// | reducer state = case _ of
// |   Increment -> state { count = state.count + 1 }
// |   Decrement -> state { count = state.count - 1 }
// |   SetUser u -> state { user = Just u }
// |   Logout -> state { user = Nothing }
// |
// | -- Create store
// | store <- Store.createStore { count: 0, user: Nothing } reducer
// |
// | -- Dispatch actions
// | Store.dispatch store Increment
// |
// | -- Get state
// | state <- Store.getState store
// |
// | -- Subscribe
// | unsub <- Store.subscribe store \state -> render state
// | ```
import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
import * as Effect from "../Effect/index.js";
import * as Effect_Class from "../Effect.Class/index.js";
import * as Effect_Class_Console from "../Effect.Class.Console/index.js";
import * as Effect_Ref from "../Effect.Ref/index.js";
var log = /* #__PURE__ */ Effect_Class_Console.log(Effect_Class.monadEffectEffect);
var when = /* #__PURE__ */ Control_Applicative.when(Effect.applicativeEffect);
var $$void = /* #__PURE__ */ Data_Functor["void"](Effect.functorEffect);
var foldM = /* #__PURE__ */ Data_Array.foldM(Effect.monadEffect);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | A store holds state and manages updates via a reducer
var Store = function (x) {
    return x;
};

// | Thunk middleware - allows dispatching functions
// | Note: In PureScript, we handle this differently via Aff
var thunkMiddleware = function (_store) {
    return function (next) {
        return function (action) {
            return next(action);
        };
    };
};

// | Subscribe to state changes, returns unsubscribe function
var subscribe = function (v) {
    return function (listener) {
        return function __do() {
            var id = Effect_Ref.read(v.nextListenerId)();
            Effect_Ref.write(id + 1 | 0)(v.nextListenerId)();
            var sub = {
                id: id,
                callback: listener
            };
            Effect_Ref.modify_(Data_Array.cons(sub))(v.listeners)();
            return Effect_Ref.modify_(Data_Array.filter(function (s) {
                return s.id !== id;
            }))(v.listeners);
        };
    };
};

// | Replace the reducer (useful for hot reloading)
var replaceReducer = function (v) {
    return function (newReducer) {
        return Effect_Ref.write(newReducer)(v.reducer);
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // middleware
// ═══════════════════════════════════════════════════════════════════════════════
// | Logger middleware - logs all actions and state changes
var loggerMiddleware = function (dictShow) {
    var show = Data_Show.show(dictShow);
    return function (dictShow1) {
        var show1 = Data_Show.show(dictShow1);
        return function (store) {
            return function (next) {
                return function (action) {
                    return function __do() {
                        var prevState = store.getState();
                        log("Action: " + show(action))();
                        log("Prev State: " + show1(prevState))();
                        next(action)();
                        var newState = store.getState();
                        return log("Next State: " + show1(newState))();
                    };
                };
            };
        };
    };
};

// | Get current state
var getState = function (v) {
    return Effect_Ref.read(v.state);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // selectors
// ═══════════════════════════════════════════════════════════════════════════════
// | Select a slice of state
var select = function (store) {
    return function (selector) {
        return function __do() {
            var state = getState(store)();
            return selector(state);
        };
    };
};

// | Subscribe to a selected slice of state (only fires when slice changes)
var selectWith = function (dictEq) {
    var notEq1 = Data_Eq.notEq(dictEq);
    return function (store) {
        return function (selector) {
            return function (callback) {
                return function __do() {
                    var initialValue = select(store)(selector)();
                    var lastValueRef = Effect_Ref["new"](initialValue)();
                    return subscribe(store)(function (newState) {
                        var newValue = selector(newState);
                        return function __do() {
                            var lastValue = Effect_Ref.read(lastValueRef)();
                            return when(notEq1(newValue)(lastValue))(function __do() {
                                Effect_Ref.write(newValue)(lastValueRef)();
                                return callback(newValue)();
                            })();
                        };
                    })();
                };
            };
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // store operations
// ═══════════════════════════════════════════════════════════════════════════════
// | Dispatch an action to update state
var dispatch = function (v) {
    return function (action) {
        var for_ = function (arr) {
            return function (f) {
                return $$void(foldM(function (v1) {
                    return function (x) {
                        return f(x);
                    };
                })(Data_Unit.unit)(arr));
            };
        };
        var storeApi = {
            getState: Effect_Ref.read(v.state),
            dispatch: dispatch(v)
        };
        var baseDispatch = function (act) {
            return function __do() {
                var currentReducer = Effect_Ref.read(v.reducer)();
                var currentState = Effect_Ref.read(v.state)();
                var newState = currentReducer(currentState)(act);
                Effect_Ref.write(newState)(v.state)();
                var subs = Effect_Ref.read(v.listeners)();
                return for_(subs)(function (listener) {
                    return listener.callback(newState);
                })();
            };
        };
        var chain = Data_Array.foldr(function (mw) {
            return function (next) {
                return mw(storeApi)(next);
            };
        })(baseDispatch)(v.middleware);
        return chain(action);
    };
};

// | Create a store with middleware
var createStoreWithMiddleware = function (initialState) {
    return function (reducer) {
        return function (middleware) {
            return function __do() {
                var stateRef = Effect_Ref["new"](initialState)();
                var reducerRef = Effect_Ref["new"](reducer)();
                var listenersRef = Effect_Ref["new"]([  ])();
                var nextListenerIdRef = Effect_Ref["new"](0)();
                return {
                    state: stateRef,
                    reducer: reducerRef,
                    listeners: listenersRef,
                    middleware: middleware,
                    nextListenerId: nextListenerIdRef
                };
            };
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                             // store creation
// ═══════════════════════════════════════════════════════════════════════════════
// | Create a new store with initial state and reducer
var createStore = function (initialState) {
    return function (reducer) {
        return createStoreWithMiddleware(initialState)(reducer)([  ]);
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // utilities
// ═══════════════════════════════════════════════════════════════════════════════
// | Combine multiple reducers into one
// | Each reducer handles a slice of state
var combineReducers = function (reducers) {
    return function (state) {
        return function (action) {
            return Data_Array.foldl(function (s) {
                return function (r) {
                    return r(s)(action);
                };
            })(state)(reducers);
        };
    };
};
export {
    createStore,
    createStoreWithMiddleware,
    dispatch,
    getState,
    subscribe,
    replaceReducer,
    loggerMiddleware,
    thunkMiddleware,
    select,
    selectWith,
    combineReducers
};
