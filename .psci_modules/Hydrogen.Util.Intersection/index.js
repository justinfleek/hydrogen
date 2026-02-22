// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                   // hydrogen // intersection
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Intersection Observer utilities
// |
// | Type-safe wrapper around the Intersection Observer API for
// | detecting element visibility.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Util.Intersection as Intersection
// |
// | -- Observe an element
// | unobserve <- Intersection.observe element
// |   { threshold: 0.5
// |   , rootMargin: "10px"
// |   }
// |   \entry -> when entry.isIntersecting do
// |     Console.log "Element is 50% visible!"
// |
// | -- Lazy load images
// | Intersection.lazyLoad imageElement \_ -> do
// |   loadHighResImage imageElement
// |
// | -- Infinite scroll
// | Intersection.observe sentinel
// |   { threshold: 0.0 }
// |   \entry -> when entry.isIntersecting do
// |     loadMoreItems
// | ```
import * as $foreign from "./foreign.js";
import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
import * as Effect from "../Effect/index.js";
var pure = /* #__PURE__ */ Control_Applicative.pure(Effect.applicativeEffect);

// Local when helper
var when = function (v) {
    return function (v1) {
        if (v) {
            return v1;
        };
        if (!v) {
            return pure(Data_Unit.unit);
        };
        throw new Error("Failed pattern match at Hydrogen.Util.Intersection (line 244, column 1 - line 244, column 46): " + [ v.constructor.name, v1.constructor.name ]);
    };
};

// | Set multiple thresholds
// |
// | ```purescript
// | config = thresholds [0.0, 0.25, 0.5, 0.75, 1.0] defaultConfig
// | ```
var thresholds = function (ts) {
    return function (config) {
        return {
            rootMargin: config.rootMargin,
            root: config.root,
            threshold: ts
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // config builders
// ═══════════════════════════════════════════════════════════════════════════════
// | Set a single threshold (0.0 to 1.0)
// |
// | ```purescript
// | config = threshold 0.5 defaultConfig  -- Trigger at 50% visibility
// | ```
var threshold = function (t) {
    return function (config) {
        return {
            rootMargin: config.rootMargin,
            root: config.root,
            threshold: [ t ]
        };
    };
};

// | Set root margin (CSS margin syntax)
// |
// | ```purescript
// | config = rootMargin "100px 0px" defaultConfig  -- 100px vertical margin
// | ```
var rootMargin = function (margin) {
    return function (config) {
        return {
            threshold: config.threshold,
            root: config.root,
            rootMargin: margin
        };
    };
};

// | Set root element (defaults to viewport)
// |
// | ```purescript
// | config = root (Just scrollContainer) defaultConfig
// | ```
var root = function (r) {
    return function (config) {
        return {
            threshold: config.threshold,
            rootMargin: config.rootMargin,
            root: r
        };
    };
};

// | Observe an element once, then automatically stop
// |
// | Useful for lazy loading or one-time animations.
var observeOnce = function (element) {
    return function (config) {
        return function (callback) {
            return $foreign.observeOnceImpl(element)(config)(callback);
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // core observer
// ═══════════════════════════════════════════════════════════════════════════════
// | Observe an element for intersection changes
// |
// | Returns an unobserve function to stop observing.
// |
// | ```purescript
// | unobserve <- observe element config \entry ->
// |   Console.log $ "Visibility: " <> show entry.intersectionRatio
// | ```
var observe = function (element) {
    return function (config) {
        return function (callback) {
            return $foreign.observeImpl(element)(config)(callback);
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // default config
// ═══════════════════════════════════════════════════════════════════════════════
// | Default observer configuration
// |
// | - threshold: [0.0] (any pixel visible)
// | - rootMargin: "0px"
// | - root: viewport
var defaultConfig = /* #__PURE__ */ (function () {
    return {
        threshold: [ 0.0 ],
        rootMargin: "0px",
        root: Data_Maybe.Nothing.value
    };
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                        // convenience functions
// ═══════════════════════════════════════════════════════════════════════════════
// | Lazy load helper
// |
// | Calls the callback once when the element enters the viewport.
// |
// | ```purescript
// | lazyLoad imageElement \_ -> do
// |   setAttribute "src" element actualImageUrl
// | ```
var lazyLoad = function (element) {
    return function (callback) {
        return observeOnce(element)(rootMargin("100px")(defaultConfig))(callback);
    };
};

// | Trigger callback when element enters viewport
// |
// | Only fires when transitioning from not-visible to visible.
var onEnterViewport = function (element) {
    return function (callback) {
        return function __do() {
            var wasVisibleRef = $foreign.newBoolRef(false)();
            return observe(element)(defaultConfig)(function (entry) {
                return function __do() {
                    var wasVisible = $foreign.readBoolRef(wasVisibleRef)();
                    when(entry.isIntersecting && !wasVisible)(callback)();
                    return $foreign.writeBoolRef(wasVisibleRef)(entry.isIntersecting)();
                };
            })();
        };
    };
};

// | Trigger callback when element exits viewport
// |
// | Only fires when transitioning from visible to not-visible.
var onExitViewport = function (element) {
    return function (callback) {
        return function __do() {
            var wasVisibleRef = $foreign.newBoolRef(false)();
            return observe(element)(defaultConfig)(function (entry) {
                return function __do() {
                    var wasVisible = $foreign.readBoolRef(wasVisibleRef)();
                    when(!entry.isIntersecting && wasVisible)(callback)();
                    return $foreign.writeBoolRef(wasVisibleRef)(entry.isIntersecting)();
                };
            })();
        };
    };
};

// | Listen for visibility changes (enter and exit)
// |
// | Callback receives true when entering, false when exiting.
var onVisibilityChange = function (element) {
    return function (callback) {
        return function __do() {
            var wasVisibleRef = $foreign.newBoolRef(false)();
            return observe(element)(defaultConfig)(function (entry) {
                return function __do() {
                    var wasVisible = $foreign.readBoolRef(wasVisibleRef)();
                    when(entry.isIntersecting !== wasVisible)(callback(entry.isIntersecting))();
                    return $foreign.writeBoolRef(wasVisibleRef)(entry.isIntersecting)();
                };
            })();
        };
    };
};
export {
    observe,
    observeOnce,
    defaultConfig,
    threshold,
    thresholds,
    rootMargin,
    root,
    lazyLoad,
    onEnterViewport,
    onExitViewport,
    onVisibilityChange
};
