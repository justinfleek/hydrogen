// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                     // hydrogen // analytics
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Analytics and performance tracking
// |
// | Provides a unified interface for tracking page views, custom events,
// | and Core Web Vitals. Supports multiple analytics backends and
// | respects user privacy preferences.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Analytics.Tracker as Analytics
// |
// | -- Initialize tracker
// | tracker <- Analytics.create
// |   { providers: [ Analytics.console, Analytics.googleAnalytics "GA-123" ]
// |   , respectDoNotTrack: true
// |   }
// |
// | -- Track page views
// | Analytics.trackPageView tracker { path: "/home", title: "Home" }
// |
// | -- Track custom events
// | Analytics.trackEvent tracker "button_click"
// |   { button: "signup", location: "header" }
// |
// | -- Track Core Web Vitals
// | Analytics.trackWebVitals tracker
// | ```
import * as $foreign from "./foreign.js";
import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Control_Category from "../Control.Category/index.js";
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Foldable from "../Data.Foldable/index.js";
import * as Data_Function from "../Data.Function/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Data_HeytingAlgebra from "../Data.HeytingAlgebra/index.js";
import * as Data_Map_Internal from "../Data.Map.Internal/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Data_Tuple from "../Data.Tuple/index.js";
import * as Data_Unfoldable from "../Data.Unfoldable/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
import * as Effect from "../Effect/index.js";
import * as Effect_Ref from "../Effect.Ref/index.js";
import * as Foreign_Object from "../Foreign.Object/index.js";
var pure = /* #__PURE__ */ Control_Applicative.pure(Effect.applicativeEffect);
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showNumber);
var identity = /* #__PURE__ */ Control_Category.identity(Control_Category.categoryFn);
var $$void = /* #__PURE__ */ Data_Functor["void"](Effect.functorEffect);
var union = /* #__PURE__ */ Data_Map_Internal.union(Data_Ord.ordString);
var toUnfoldable = /* #__PURE__ */ Data_Map_Internal.toUnfoldable(Data_Unfoldable.unfoldableArray);
var fromFoldable = /* #__PURE__ */ Foreign_Object.fromFoldable(Data_Foldable.foldableArray);
var show1 = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);
var map = /* #__PURE__ */ Data_Functor.map(Effect.functorEffect);
var not = /* #__PURE__ */ Data_HeytingAlgebra.not(Data_HeytingAlgebra.heytingAlgebraBoolean);

// | Individual web vital metric
var LCP = /* #__PURE__ */ (function () {
    function LCP(value0) {
        this.value0 = value0;
    };
    LCP.create = function (value0) {
        return new LCP(value0);
    };
    return LCP;
})();

// | Individual web vital metric
var FID = /* #__PURE__ */ (function () {
    function FID(value0) {
        this.value0 = value0;
    };
    FID.create = function (value0) {
        return new FID(value0);
    };
    return FID;
})();

// | Individual web vital metric
var CLS = /* #__PURE__ */ (function () {
    function CLS(value0) {
        this.value0 = value0;
    };
    CLS.create = function (value0) {
        return new CLS(value0);
    };
    return CLS;
})();

// | Individual web vital metric
var FCP = /* #__PURE__ */ (function () {
    function FCP(value0) {
        this.value0 = value0;
    };
    FCP.create = function (value0) {
        return new FCP(value0);
    };
    return FCP;
})();

// | Individual web vital metric
var TTFB = /* #__PURE__ */ (function () {
    function TTFB(value0) {
        this.value0 = value0;
    };
    TTFB.create = function (value0) {
        return new TTFB(value0);
    };
    return TTFB;
})();

// | Individual web vital metric
var INP = /* #__PURE__ */ (function () {
    function INP(value0) {
        this.value0 = value0;
    };
    INP.create = function (value0) {
        return new INP(value0);
    };
    return INP;
})();

// ═══════════════════════════════════════════════════════════════════════════
// Privacy
// ═══════════════════════════════════════════════════════════════════════════
// | Privacy mode settings
var FullTracking = /* #__PURE__ */ (function () {
    function FullTracking() {

    };
    FullTracking.value = new FullTracking();
    return FullTracking;
})();

// ═══════════════════════════════════════════════════════════════════════════
// Privacy
// ═══════════════════════════════════════════════════════════════════════════
// | Privacy mode settings
var AnonymousOnly = /* #__PURE__ */ (function () {
    function AnonymousOnly() {

    };
    AnonymousOnly.value = new AnonymousOnly();
    return AnonymousOnly;
})();

// ═══════════════════════════════════════════════════════════════════════════
// Privacy
// ═══════════════════════════════════════════════════════════════════════════
// | Privacy mode settings
var NoTracking = /* #__PURE__ */ (function () {
    function NoTracking() {

    };
    NoTracking.value = new NoTracking();
    return NoTracking;
})();
var when = function (v) {
    return function (v1) {
        if (v) {
            return v1;
        };
        if (!v) {
            return pure(Data_Unit.unit);
        };
        throw new Error("Failed pattern match at Hydrogen.Analytics.Tracker (line 595, column 1 - line 595, column 46): " + [ v.constructor.name, v1.constructor.name ]);
    };
};
var traverse = $foreign.traverseImpl;
var showWebVitalMetric = {
    show: function (v) {
        if (v instanceof LCP) {
            return "LCP(" + (show(v.value0) + "ms)");
        };
        if (v instanceof FID) {
            return "FID(" + (show(v.value0) + "ms)");
        };
        if (v instanceof CLS) {
            return "CLS(" + (show(v.value0) + ")");
        };
        if (v instanceof FCP) {
            return "FCP(" + (show(v.value0) + "ms)");
        };
        if (v instanceof TTFB) {
            return "TTFB(" + (show(v.value0) + "ms)");
        };
        if (v instanceof INP) {
            return "INP(" + (show(v.value0) + "ms)");
        };
        throw new Error("Failed pattern match at Hydrogen.Analytics.Tracker (line 360, column 10 - line 366, column 39): " + [ v.constructor.name ]);
    }
};

// | Set the buffer size
var setBufferSize = function (tracker) {
    return function (size) {
        return pure(Data_Unit.unit);
    };
};

// | Plausible Analytics provider
var plausible = function (domain) {
    return {
        name: "plausible",
        init: $foreign.initPlausible(domain)
    };
};

// | Opt out of tracking
var optOut = function (tracker) {
    return function __do() {
        Effect_Ref.write(false)(tracker.isEnabled)();
        return $foreign.persistOptOut(true)();
    };
};

// | Opt back in to tracking
var optIn = function (tracker) {
    return function __do() {
        Effect_Ref.write(true)(tracker.isEnabled)();
        return $foreign.persistOptOut(false)();
    };
};

// | Subscribe to vital metrics
var onVital = function (_tracker) {
    return function (handler) {
        return $foreign.observeWebVitals(handler);
    };
};

// | Mixpanel provider
var mixpanel = function (token) {
    return {
        name: "mixpanel",
        init: $foreign.initMixpanel(token)
    };
};
var maybeInsert = function (key) {
    return function (v) {
        if (v instanceof Data_Maybe.Just) {
            return Foreign_Object.insert(key)(v.value0);
        };
        if (v instanceof Data_Maybe.Nothing) {
            return identity;
        };
        throw new Error("Failed pattern match at Hydrogen.Analytics.Tracker (line 605, column 19 - line 607, column 22): " + [ v.constructor.name ]);
    };
};

// | Check if tracking is enabled
var isTracking = function (tracker) {
    return Effect_Ref.read(tracker.isEnabled);
};

// | Initialize a provider from config
var initProvider = function (config) {
    return config.init;
};

// | Google Analytics 4 provider
var googleAnalytics = function (measurementId) {
    return {
        name: "google-analytics",
        init: $foreign.initGoogleAnalytics(measurementId)
    };
};

// | Get the current event queue (for debugging)
var getQueue = function (tracker) {
    return Effect_Ref.read(tracker.queue);
};
var fromMaybe = function ($$default) {
    return function (v) {
        if (v instanceof Data_Maybe.Just) {
            return v.value0;
        };
        if (v instanceof Data_Maybe.Nothing) {
            return $$default;
        };
        throw new Error("Failed pattern match at Hydrogen.Analytics.Tracker (line 600, column 21 - line 602, column 21): " + [ v.constructor.name ]);
    };
};
var for_ = function (arr) {
    return function (f) {
        return $$void(traverse(f)(arr));
    };
};

// ═══════════════════════════════════════════════════════════════════════════
// User Identity
// ═══════════════════════════════════════════════════════════════════════════
// | Identify a user
var identify = function (tracker) {
    return function (uid) {
        return function __do() {
            Effect_Ref.write(new Data_Maybe.Just(uid))(tracker.userId)();
            return for_(tracker.providers)(function (provider) {
                return provider.identify(uid);
            })();
        };
    };
};

// | Reset user identity (e.g., on logout)
var reset = function (tracker) {
    return function __do() {
        Effect_Ref.write(Data_Maybe.Nothing.value)(tracker.userId)();
        Effect_Ref.write(Data_Map_Internal.empty)(tracker.userProperties)();
        return for_(tracker.providers)(function (provider) {
            return provider.reset;
        })();
    };
};

// | Set privacy mode
var setPrivacyMode = function (tracker) {
    return function (mode) {
        if (mode instanceof FullTracking) {
            return Effect_Ref.write(true)(tracker.isEnabled);
        };
        if (mode instanceof AnonymousOnly) {
            return function __do() {
                Effect_Ref.write(true)(tracker.isEnabled)();
                return reset(tracker)();
            };
        };
        if (mode instanceof NoTracking) {
            return Effect_Ref.write(false)(tracker.isEnabled);
        };
        throw new Error("Failed pattern match at Hydrogen.Analytics.Tracker (line 499, column 31 - line 504, column 50): " + [ mode.constructor.name ]);
    };
};

// | Set user properties
var setUserProperties = function (tracker) {
    return function (props) {
        return function __do() {
            Effect_Ref.modify_(union(props))(tracker.userProperties)();
            var propsArray = toUnfoldable(props);
            var propsObj = fromFoldable(propsArray);
            return for_(tracker.providers)(function (provider) {
                return provider.setUserProperties(propsObj);
            })();
        };
    };
};

// | Flush queued events to providers
var flush = function (tracker) {
    return function __do() {
        var queue = Effect_Ref.read(tracker.queue)();
        Effect_Ref.write([  ])(tracker.queue)();
        for_(queue)(function (event) {
            return for_(tracker.providers)(function (provider) {
                return provider.track(event.eventType)(event.data);
            });
        })();
        return for_(tracker.providers)(function (provider) {
            return provider.flush;
        })();
    };
};

// ═══════════════════════════════════════════════════════════════════════════
// Event Queue & Batching
// ═══════════════════════════════════════════════════════════════════════════
// | Queue an event for sending
var queueEvent = function (tracker) {
    return function (eventType) {
        return function (eventData) {
            return function __do() {
                var timestamp = $foreign.now();
                var userId = Effect_Ref.read(tracker.userId)();
                var userProps = Effect_Ref.read(tracker.userProperties)();
                var enrichedData = maybeInsert("user_id")(userId)(Foreign_Object.insert("timestamp")(show(timestamp))(Foreign_Object.insert("session_id")(tracker.sessionId)(eventData)));
                var isDebug = Effect_Ref.read(tracker.debug)();
                when(isDebug)($foreign.logAnalytics(eventType)(enrichedData))();
                Effect_Ref.modify_(Data_Function.flip(Data_Array.snoc)({
                    eventType: eventType,
                    data: enrichedData,
                    timestamp: timestamp
                }))(tracker.queue)();
                var queue = Effect_Ref.read(tracker.queue)();
                return when(Data_Array.length(queue) >= tracker.config.bufferSize)(flush(tracker))();
            };
        };
    };
};

// | Track a custom event
var trackEvent = function (tracker) {
    return function (eventName) {
        return function (eventData) {
            return function __do() {
                var enabled = Effect_Ref.read(tracker.isEnabled)();
                return when(enabled)((function () {
                    var data$prime = Foreign_Object.insert("event_name")(eventName)(eventData);
                    return queueEvent(tracker)("event")(data$prime);
                })())();
            };
        };
    };
};

// | Track adding item to cart
var trackAddToCart = function (tracker) {
    return function (product) {
        var data$prime = fromFoldable([ new Data_Tuple.Tuple("product_id", product.id), new Data_Tuple.Tuple("product_name", product.name), new Data_Tuple.Tuple("price", show(product.price)), new Data_Tuple.Tuple("quantity", show1(product.quantity)) ]);
        return trackEvent(tracker)("add_to_cart")(data$prime);
    };
};

// | Track checkout step
var trackCheckout = function (tracker) {
    return function (step) {
        return function (paymentMethod) {
            var data$prime = fromFoldable([ new Data_Tuple.Tuple("step", show1(step)), new Data_Tuple.Tuple("payment_method", fromMaybe("")(paymentMethod)) ]);
            return trackEvent(tracker)("checkout")(data$prime);
        };
    };
};

// | Track an event with a numeric value
var trackEventWithValue = function (tracker) {
    return function (eventName) {
        return function (value) {
            return function (eventData) {
                var data$prime = Foreign_Object.insert("value")(show(value))(eventData);
                return trackEvent(tracker)(eventName)(data$prime);
            };
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════
// E-commerce Tracking
// ═══════════════════════════════════════════════════════════════════════════
// | Track a purchase
var trackPurchase = function (tracker) {
    return function (purchase) {
        var data$prime = fromFoldable([ new Data_Tuple.Tuple("transaction_id", purchase.transactionId), new Data_Tuple.Tuple("total", show(purchase.total)), new Data_Tuple.Tuple("currency", purchase.currency), new Data_Tuple.Tuple("item_count", show1(Data_Array.length(purchase.items))) ]);
        return trackEvent(tracker)("purchase")(data$prime);
    };
};

// | Track removing item from cart
var trackRemoveFromCart = function (tracker) {
    return function (product) {
        var data$prime = fromFoldable([ new Data_Tuple.Tuple("product_id", product.id), new Data_Tuple.Tuple("product_name", product.name) ]);
        return trackEvent(tracker)("remove_from_cart")(data$prime);
    };
};

// | Track a page view with full data
var trackPageViewWithData = function (tracker) {
    return function (pageData) {
        return function __do() {
            var enabled = Effect_Ref.read(tracker.isEnabled)();
            return when(enabled)((function () {
                var eventData = fromFoldable([ new Data_Tuple.Tuple("path", pageData.path), new Data_Tuple.Tuple("title", fromMaybe("")(pageData.title)), new Data_Tuple.Tuple("referrer", fromMaybe("")(pageData.referrer)) ]);
                return queueEvent(tracker)("pageview")(Foreign_Object.union(eventData)(pageData.customData));
            })())();
        };
    };
};

// | Track a simple page view
var trackPageView = function (tracker) {
    return function (v) {
        return trackPageViewWithData(tracker)({
            path: v.path,
            title: new Data_Maybe.Just(v.title),
            referrer: Data_Maybe.Nothing.value,
            customData: Foreign_Object.empty
        });
    };
};

// | Track a timing event
var trackTiming = function (tracker) {
    return function (category) {
        return function (duration) {
            return function (eventData) {
                return function __do() {
                    var enabled = Effect_Ref.read(tracker.isEnabled)();
                    return when(enabled)((function () {
                        var data$prime = fromFoldable([ new Data_Tuple.Tuple("category", category), new Data_Tuple.Tuple("duration", show1(duration)) ]);
                        return queueEvent(tracker)("timing")(Foreign_Object.union(data$prime)(eventData));
                    })())();
                };
            };
        };
    };
};

// | Track a single vital metric
var trackVital = function (tracker) {
    return function (metric) {
        var v = (function () {
            if (metric instanceof LCP) {
                return new Data_Tuple.Tuple("lcp", metric.value0);
            };
            if (metric instanceof FID) {
                return new Data_Tuple.Tuple("fid", metric.value0);
            };
            if (metric instanceof CLS) {
                return new Data_Tuple.Tuple("cls", metric.value0);
            };
            if (metric instanceof FCP) {
                return new Data_Tuple.Tuple("fcp", metric.value0);
            };
            if (metric instanceof TTFB) {
                return new Data_Tuple.Tuple("ttfb", metric.value0);
            };
            if (metric instanceof INP) {
                return new Data_Tuple.Tuple("inp", metric.value0);
            };
            throw new Error("Failed pattern match at Hydrogen.Analytics.Tracker (line 381, column 25 - line 387, column 28): " + [ metric.constructor.name ]);
        })();
        var data$prime = fromFoldable([ new Data_Tuple.Tuple("metric", v.value0), new Data_Tuple.Tuple("value", show(v.value1)) ]);
        return queueEvent(tracker)("web_vital")(data$prime);
    };
};

// | Track all Core Web Vitals automatically
var trackWebVitals = function (tracker) {
    return $foreign.observeWebVitals(function (metric) {
        return function __do() {
            var enabled = Effect_Ref.read(tracker.isEnabled)();
            return when(enabled)(trackVital(tracker)(metric))();
        };
    });
};
var eqWebVitalMetric = {
    eq: function (x) {
        return function (y) {
            if (x instanceof LCP && y instanceof LCP) {
                return x.value0 === y.value0;
            };
            if (x instanceof FID && y instanceof FID) {
                return x.value0 === y.value0;
            };
            if (x instanceof CLS && y instanceof CLS) {
                return x.value0 === y.value0;
            };
            if (x instanceof FCP && y instanceof FCP) {
                return x.value0 === y.value0;
            };
            if (x instanceof TTFB && y instanceof TTFB) {
                return x.value0 === y.value0;
            };
            if (x instanceof INP && y instanceof INP) {
                return x.value0 === y.value0;
            };
            return false;
        };
    }
};
var eqPrivacyMode = {
    eq: function (x) {
        return function (y) {
            if (x instanceof FullTracking && y instanceof FullTracking) {
                return true;
            };
            if (x instanceof AnonymousOnly && y instanceof AnonymousOnly) {
                return true;
            };
            if (x instanceof NoTracking && y instanceof NoTracking) {
                return true;
            };
            return false;
        };
    }
};

// ═══════════════════════════════════════════════════════════════════════════
// Debug
// ═══════════════════════════════════════════════════════════════════════════
// | Enable debug mode
var enableDebug = function (tracker) {
    return function (enabled) {
        return Effect_Ref.write(enabled)(tracker.debug);
    };
};

// | Default configuration
var defaultConfig = /* #__PURE__ */ (function () {
    return {
        providers: [  ],
        respectDoNotTrack: true,
        bufferSize: 10,
        flushInterval: new Data_Maybe.Just(5000),
        sessionTimeout: 1800000,
        anonymizeIp: true,
        cookieDomain: Data_Maybe.Nothing.value
    };
})();

// | Create a custom provider
var customProvider = function (name) {
    return function (trackFn) {
        return {
            name: name,
            init: pure({
                name: name,
                track: trackFn,
                identify: function (v) {
                    return pure(Data_Unit.unit);
                },
                setUserProperties: function (v) {
                    return pure(Data_Unit.unit);
                },
                reset: pure(Data_Unit.unit),
                flush: pure(Data_Unit.unit)
            })
        };
    };
};

// | Create a tracker with custom config
var createWithConfig = function (config) {
    return function __do() {
        var shouldTrack = (function () {
            if (config.respectDoNotTrack) {
                return map(not)($foreign.getDoNotTrack)();
            };
            return true;
        })();
        var providers = traverse(initProvider)(config.providers)();
        var queue = Effect_Ref["new"]([  ])();
        var isEnabled = Effect_Ref["new"](shouldTrack)();
        var userId = Effect_Ref["new"](Data_Maybe.Nothing.value)();
        var userProperties = Effect_Ref["new"](Data_Map_Internal.empty)();
        var sessionId = $foreign.generateSessionId();
        var debug = Effect_Ref["new"](false)();
        var tracker = {
            providers: providers,
            queue: queue,
            config: config,
            isEnabled: isEnabled,
            userId: userId,
            userProperties: userProperties,
            sessionId: sessionId,
            debug: debug
        };
        (function () {
            if (config.flushInterval instanceof Data_Maybe.Just) {
                return $foreign.setupFlushInterval(tracker)(config.flushInterval.value0)();
            };
            if (config.flushInterval instanceof Data_Maybe.Nothing) {
                return Data_Unit.unit;
            };
            throw new Error("Failed pattern match at Hydrogen.Analytics.Tracker (line 173, column 3 - line 175, column 25): " + [ config.flushInterval.constructor.name ]);
        })();
        return tracker;
    };
};

// ═══════════════════════════════════════════════════════════════════════════
// Tracker Creation
// ═══════════════════════════════════════════════════════════════════════════
// | Create a tracker with default config
var create = function (providerConfigs) {
    return createWithConfig({
        respectDoNotTrack: defaultConfig.respectDoNotTrack,
        bufferSize: defaultConfig.bufferSize,
        flushInterval: defaultConfig.flushInterval,
        sessionTimeout: defaultConfig.sessionTimeout,
        anonymizeIp: defaultConfig.anonymizeIp,
        cookieDomain: defaultConfig.cookieDomain,
        providers: providerConfigs
    });
};

// | Console provider (for development)
var console = {
    name: "console",
    init: /* #__PURE__ */ pure({
        name: "console",
        track: function (eventType) {
            return function (eventData) {
                return $foreign.logAnalytics(eventType)(eventData);
            };
        },
        identify: function (uid) {
            return $foreign.logIdentify(uid);
        },
        setUserProperties: function (props) {
            return $foreign.logUserProps(props);
        },
        reset: $foreign.logReset,
        flush: /* #__PURE__ */ pure(Data_Unit.unit)
    })
};
export {
    create,
    createWithConfig,
    trackPageView,
    trackPageViewWithData,
    trackEvent,
    trackEventWithValue,
    trackTiming,
    identify,
    setUserProperties,
    reset,
    trackPurchase,
    trackAddToCart,
    trackRemoveFromCart,
    trackCheckout,
    LCP,
    FID,
    CLS,
    FCP,
    TTFB,
    INP,
    trackWebVitals,
    trackVital,
    onVital,
    console,
    googleAnalytics,
    plausible,
    mixpanel,
    customProvider,
    FullTracking,
    AnonymousOnly,
    NoTracking,
    setPrivacyMode,
    optOut,
    optIn,
    isTracking,
    flush,
    setBufferSize,
    enableDebug,
    getQueue,
    eqWebVitalMetric,
    showWebVitalMetric,
    eqPrivacyMode
};
