// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                      // hydrogen // eventbus
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Type-safe event bus for pub/sub communication
// |
// | The event bus provides a decoupled communication mechanism between
// | components. Events are typed and can carry arbitrary payloads.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Event.Bus as Bus
// |
// | -- Define your events
// | data AppEvent
// |   = UserLoggedIn User
// |   | CartUpdated Cart
// |   | ThemeChanged Theme
// |
// | -- Create an event bus
// | bus <- Bus.create
// |
// | -- Subscribe to events
// | unsubscribe <- Bus.subscribe bus \event -> case event of
// |   UserLoggedIn user -> Console.log $ "Welcome " <> user.name
// |   CartUpdated cart -> updateCartUI cart
// |   ThemeChanged theme -> applyTheme theme
// |
// | -- Emit events
// | Bus.emit bus (UserLoggedIn { name: "Alice" })
// |
// | -- Clean up
// | unsubscribe
// | ```
import * as $foreign from "./foreign.js";
import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Control_Bind from "../Control.Bind/index.js";
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Function from "../Data.Function/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
import * as Effect from "../Effect/index.js";
import * as Effect_Aff from "../Effect.Aff/index.js";
import * as Effect_Class from "../Effect.Class/index.js";
import * as Effect_Ref from "../Effect.Ref/index.js";
var pure = /* #__PURE__ */ Control_Applicative.pure(Effect.applicativeEffect);
var discard = /* #__PURE__ */ Control_Bind.discard(Control_Bind.discardUnit);
var map1 = /* #__PURE__ */ Data_Functor.map(Effect.functorEffect);
var $$void = /* #__PURE__ */ Data_Functor["void"](Effect.functorEffect);
var compare = /* #__PURE__ */ Data_Ord.compare(Data_Ord.ordString);
var elem = /* #__PURE__ */ Data_Array.elem(Data_Eq.eqInt);
var liftEffect = /* #__PURE__ */ Effect_Class.liftEffect(Effect_Aff.monadEffectAff);
var discard2 = /* #__PURE__ */ discard(Effect_Aff.bindAff);

// ═══════════════════════════════════════════════════════════════════════════
// Typed Channels (Heterogeneous Events)
// ═══════════════════════════════════════════════════════════════════════════
// | A typed channel that carries a specific event type
// | Used for heterogeneous event buses
var TypedChannel = function (x) {
    return x;
};

// ═══════════════════════════════════════════════════════════════════════════
// Channels (Namespaced Events)
// ═══════════════════════════════════════════════════════════════════════════
// | A named channel for organizing events
var Channel = function (x) {
    return x;
};

// ═══════════════════════════════════════════════════════════════════════════
// Utilities
// ═══════════════════════════════════════════════════════════════════════════
var when = function (v) {
    return function (v1) {
        if (v) {
            return v1;
        };
        if (!v) {
            return pure(Data_Unit.unit);
        };
        throw new Error("Failed pattern match at Hydrogen.Event.Bus (line 387, column 1 - line 387, column 46): " + [ v.constructor.name, v1.constructor.name ]);
    };
};

// | Remove all subscribers
var unsubscribeAll = function (bus) {
    return Effect_Ref.write([  ])(bus.subscribers);
};

// | Internal unsubscribe by ID
var unsubscribe = function (bus) {
    return function (id) {
        return Effect_Ref.modify_(Data_Array.filter(function (s) {
            return s.id !== id;
        }))(bus.subscribers);
    };
};
var unless = function (cond) {
    return when(!cond);
};

// | Create a typed channel
var typedChannel = TypedChannel;

// | Subscribe with a filter predicate
// | Handler only called when filter returns true
var subscribeWithFilter = function (bus) {
    return function (predicate) {
        return function (handler) {
            return function __do() {
                var id = Effect_Ref.read(bus.nextId)();
                Effect_Ref.write(id + 1 | 0)(bus.nextId)();
                var subscriber = {
                    id: id,
                    handler: handler,
                    once: false,
                    filter: new Data_Maybe.Just(predicate)
                };
                Effect_Ref.modify_(Data_Function.flip(Data_Array.snoc)(subscriber))(bus.subscribers)();
                return unsubscribe(bus)(id);
            };
        };
    };
};

// | Subscribe to a typed channel on a heterogeneous bus
var subscribeTyped = function (bus) {
    return function (v) {
        return function (handler) {
            return subscribeWithFilter(bus)(function (v1) {
                return true;
            })(function (anyEvent) {
                var v1 = $foreign.unwrapEvent(v)(anyEvent);
                if (v1 instanceof Data_Maybe.Just) {
                    return handler(v1.value0);
                };
                if (v1 instanceof Data_Maybe.Nothing) {
                    return pure(Data_Unit.unit);
                };
                throw new Error("Failed pattern match at Hydrogen.Event.Bus (line 374, column 19 - line 376, column 27): " + [ v1.constructor.name ]);
            });
        };
    };
};

// | Subscribe to a single event, then automatically unsubscribe
var subscribeOnce = function (bus) {
    return function (handler) {
        return function __do() {
            var id = Effect_Ref.read(bus.nextId)();
            Effect_Ref.write(id + 1 | 0)(bus.nextId)();
            var subscriber = {
                id: id,
                handler: handler,
                once: true,
                filter: Data_Maybe.Nothing.value
            };
            Effect_Ref.modify_(Data_Function.flip(Data_Array.snoc)(subscriber))(bus.subscribers)();
            return unsubscribe(bus)(id);
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════
// Subscriptions
// ═══════════════════════════════════════════════════════════════════════════
// | Subscribe to events on the bus
// | Returns an unsubscribe function
var subscribe = function (bus) {
    return function (handler) {
        return function __do() {
            var id = Effect_Ref.read(bus.nextId)();
            Effect_Ref.write(id + 1 | 0)(bus.nextId)();
            var subscriber = {
                id: id,
                handler: handler,
                once: false,
                filter: Data_Maybe.Nothing.value
            };
            Effect_Ref.modify_(Data_Function.flip(Data_Array.snoc)(subscriber))(bus.subscribers)();
            return unsubscribe(bus)(id);
        };
    };
};
var showChannel = {
    show: function (v) {
        return "Channel(" + (v + ")");
    }
};

// | Record an event in history
var recordEvent = function (history) {
    return function (event) {
        return function __do() {
            var timestamp = $foreign.nowImpl();
            return Effect_Ref.modify_(function (arr) {
                var newArr = Data_Array.snoc(arr)({
                    event: event,
                    timestamp: timestamp
                });
                var $54 = Data_Array.length(newArr) > history.maxSize;
                if ($54) {
                    return Data_Array.drop(1)(newArr);
                };
                return newArr;
            })(history.events)();
        };
    };
};
var map = $foreign.mapImpl;

// | Get the number of active subscribers
var getSubscriberCount = function (bus) {
    return map1(Data_Array.length)(Effect_Ref.read(bus.subscribers));
};

// | Get the event history
var getHistory = function (bus) {
    if (bus.history instanceof Data_Maybe.Just) {
        return Effect_Ref.read(bus.history.value0.events);
    };
    if (bus.history instanceof Data_Maybe.Nothing) {
        return pure([  ]);
    };
    throw new Error("Failed pattern match at Hydrogen.Event.Bus (line 312, column 18 - line 314, column 21): " + [ bus.history.constructor.name ]);
};

// | Replay all events in history to a handler
var replay = function (bus) {
    return function (handler) {
        var for_ = function (arr) {
            return function (f) {
                return $$void($foreign.traverseImpl(f)(arr));
            };
        };
        return function __do() {
            var events = getHistory(bus)();
            return for_(events)(function (v) {
                return handler(v.event);
            })();
        };
    };
};
var eqTypedChannel = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordTypedChannel = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqTypedChannel;
    }
};
var eqChannel = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var eq1 = /* #__PURE__ */ Data_Eq.eq(eqChannel);

// | Subscribe to a specific channel
var onChannel = function (bus) {
    return function (ch) {
        return function (handler) {
            return subscribeWithFilter(bus)(function (e) {
                return eq1(e.channel)(ch);
            })(function (e) {
                return handler(e.payload);
            });
        };
    };
};
var ordChannel = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqChannel;
    }
};

// ═══════════════════════════════════════════════════════════════════════════
// Emitting Events
// ═══════════════════════════════════════════════════════════════════════════
// | Emit an event to all subscribers
var emit = function (bus) {
    return function (event) {
        var shouldHandle = function (e) {
            return function (sub) {
                if (sub.filter instanceof Data_Maybe.Nothing) {
                    return true;
                };
                if (sub.filter instanceof Data_Maybe.Just) {
                    return sub.filter.value0(e);
                };
                throw new Error("Failed pattern match at Hydrogen.Event.Bus (line 213, column 24 - line 215, column 18): " + [ sub.filter.constructor.name ]);
            };
        };
        var for_ = function (arr) {
            return function (f) {
                return $$void($foreign.traverseImpl(f)(arr));
            };
        };
        return function __do() {
            (function () {
                if (bus.history instanceof Data_Maybe.Just) {
                    return recordEvent(bus.history.value0)(event)();
                };
                if (bus.history instanceof Data_Maybe.Nothing) {
                    return Data_Unit.unit;
                };
                throw new Error("Failed pattern match at Hydrogen.Event.Bus (line 188, column 3 - line 190, column 25): " + [ bus.history.constructor.name ]);
            })();
            var isDebug = Effect_Ref.read(bus.debugMode)();
            when(isDebug)($foreign.logEvent(bus.name)(event))();
            var subs = Effect_Ref.read(bus.subscribers)();
            var matchingSubs = Data_Array.filter(shouldHandle(event))(subs);
            var onceSubs = Data_Array.filter(function (v) {
                return v.once;
            })(matchingSubs);
            unless(Data_Array["null"](onceSubs))((function () {
                var onceIds = map(function (v) {
                    return v.id;
                })(onceSubs);
                return Effect_Ref.modify_(Data_Array.filter(function (s) {
                    return !elem(s.id)(onceIds);
                }))(bus.subscribers);
            })())();
            return for_(matchingSubs)(function (sub) {
                return sub.handler(event);
            })();
        };
    };
};

// | Emit an event asynchronously (non-blocking)
var emitAsync = function (bus) {
    return function (event) {
        return liftEffect(emit(bus)(event));
    };
};

// | Emit an event after a delay
var emitDelayed = function (bus) {
    return function (v) {
        return function (event) {
            return discard2(Effect_Aff.delay(v))(function () {
                return liftEffect(emit(bus)(event));
            });
        };
    };
};

// | Emit to a specific channel
var emitToChannel = function (bus) {
    return function (ch) {
        return function (payload) {
            return emit(bus)({
                channel: ch,
                payload: payload
            });
        };
    };
};

// | Emit to a typed channel
var emitTyped = function (bus) {
    return function (v) {
        return function (event) {
            return emit(bus)($foreign.wrapEvent(v)(event));
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════
// Debugging
// ═══════════════════════════════════════════════════════════════════════════
// | Enable debug mode for a bus
var debugBus = function (bus) {
    return function (enabled) {
        return Effect_Ref.write(enabled)(bus.debugMode);
    };
};

// | Create a new event bus
var create = function __do() {
    var subscribers = Effect_Ref["new"]([  ])();
    var nextId = Effect_Ref["new"](0)();
    var debugMode = Effect_Ref["new"](false)();
    return {
        name: Data_Maybe.Nothing.value,
        subscribers: subscribers,
        nextId: nextId,
        history: Data_Maybe.Nothing.value,
        debugMode: debugMode
    };
};

// | Create a named event bus (useful for debugging)
var createNamed = function (name) {
    return function __do() {
        var bus = create();
        return {
            debugMode: bus.debugMode,
            history: bus.history,
            nextId: bus.nextId,
            subscribers: bus.subscribers,
            name: new Data_Maybe.Just(name)
        };
    };
};

// | Create a bus with history tracking
var withHistory = function (maxSize) {
    return function __do() {
        var bus = create();
        var events = Effect_Ref["new"]([  ])();
        return {
            debugMode: bus.debugMode,
            name: bus.name,
            nextId: bus.nextId,
            subscribers: bus.subscribers,
            history: new Data_Maybe.Just({
                events: events,
                maxSize: maxSize
            })
        };
    };
};

// | Clear the event history
var clearHistory = function (bus) {
    if (bus.history instanceof Data_Maybe.Just) {
        return Effect_Ref.write([  ])(bus.history.value0.events);
    };
    if (bus.history instanceof Data_Maybe.Nothing) {
        return pure(Data_Unit.unit);
    };
    throw new Error("Failed pattern match at Hydrogen.Event.Bus (line 318, column 20 - line 320, column 23): " + [ bus.history.constructor.name ]);
};

// | Create a named channel (alias)
var channelNamed = Channel;

// | Create a channel
var channel = Channel;
export {
    create,
    createNamed,
    subscribe,
    subscribeOnce,
    subscribeWithFilter,
    unsubscribeAll,
    emit,
    emitAsync,
    emitDelayed,
    channel,
    channelNamed,
    onChannel,
    emitToChannel,
    withHistory,
    getHistory,
    clearHistory,
    replay,
    debugBus,
    getSubscriberCount,
    typedChannel,
    subscribeTyped,
    emitTyped,
    eqChannel,
    ordChannel,
    showChannel,
    eqTypedChannel,
    ordTypedChannel
};
