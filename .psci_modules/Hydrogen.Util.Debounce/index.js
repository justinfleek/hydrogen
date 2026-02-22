// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                       // hydrogen // debounce
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Rate limiting utilities
// |
// | Debounce and throttle functions for controlling execution frequency.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Util.Debounce as Debounce
// |
// | -- Debounce search input (trailing edge by default)
// | debouncedSearch <- Debounce.debounce (Milliseconds 300.0) \query ->
// |   performSearch query
// |
// | -- Now use debouncedSearch instead of performSearch
// | debouncedSearch "hello"  -- Called after 300ms of inactivity
// |
// | -- Throttle scroll handler
// | throttledScroll <- Debounce.throttle (Milliseconds 100.0) \_ ->
// |   updateScrollPosition
// |
// | -- Leading edge debounce (execute immediately, then debounce)
// | immediate <- Debounce.debounceLeading (Milliseconds 300.0) \_ ->
// |   doSomething
// |
// | -- Cancel pending calls
// | cancelFn <- Debounce.debounceWithCancel (Milliseconds 300.0) handler
// | cancelFn.cancel  -- Cancel any pending execution
// | ```
import * as $foreign from "./foreign.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Show from "../Data.Show/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showNumber);
var compare = /* #__PURE__ */ Data_Ord.compare(Data_Ord.ordNumber);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Duration in milliseconds
var Milliseconds = function (x) {
    return x;
};

// | Throttle with cancel and flush capabilities
var throttleWithCancel = function (v) {
    return function (fn) {
        return $foreign.throttleImpl(v)(true)(true)(fn);
    };
};

// | Throttle with trailing edge only
// |
// | Queues one call to execute after the throttle period.
var throttleTrailing = function (v) {
    return function (fn) {
        return function __do() {
            var result = $foreign.throttleImpl(v)(false)(true)(fn)();
            return result.call;
        };
    };
};

// | Throttle with leading edge only
// |
// | Executes immediately, ignores calls during the throttle period.
var throttleLeading = function (v) {
    return function (fn) {
        return function __do() {
            var result = $foreign.throttleImpl(v)(true)(false)(fn)();
            return result.call;
        };
    };
};

// | Throttle a function
// |
// | The function will be called at most once per time period.
// |
// | ```purescript
// | throttledFn <- throttle (Milliseconds 100.0) myHandler
// | -- Even if called rapidly, executes at most once per 100ms
// | ```
var throttle = function (v) {
    return function (fn) {
        return function __do() {
            var result = $foreign.throttleImpl(v)(true)(true)(fn)();
            return result.call;
        };
    };
};
var showMilliseconds = {
    show: function (v) {
        return show(v) + "ms";
    }
};
var eqMilliseconds = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var ordMilliseconds = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqMilliseconds;
    }
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // with cancel
// ═══════════════════════════════════════════════════════════════════════════════
// | Debounce with cancel and flush capabilities
// |
// | ```purescript
// | fns <- debounceWithCancel (Milliseconds 300.0) myHandler
// | fns.call "value"  -- Queue a call
// | fns.cancel        -- Cancel pending call
// | fns.flush         -- Execute pending call immediately
// | ```
var debounceWithCancel = function (v) {
    return function (fn) {
        return $foreign.debounceImpl(v)(false)(true)(fn);
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // edge options
// ═══════════════════════════════════════════════════════════════════════════════
// | Debounce with leading edge
// |
// | Executes immediately on first call, then debounces subsequent calls.
var debounceLeading = function (v) {
    return function (fn) {
        return function __do() {
            var result = $foreign.debounceImpl(v)(true)(false)(fn)();
            return result.call;
        };
    };
};

// | Debounce with both leading and trailing edges
// |
// | Executes immediately and also after the debounce period.
var debounceBoth = function (v) {
    return function (fn) {
        return function __do() {
            var result = $foreign.debounceImpl(v)(true)(true)(fn)();
            return result.call;
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // core functions
// ═══════════════════════════════════════════════════════════════════════════════
// | Debounce a function (trailing edge)
// |
// | The function will only be called after the specified time has passed
// | without any new calls.
// |
// | ```purescript
// | debouncedFn <- debounce (Milliseconds 300.0) myHandler
// | debouncedFn "a"  -- Ignored
// | debouncedFn "b"  -- Ignored
// | debouncedFn "c"  -- Called with "c" after 300ms of no calls
// | ```
var debounce = function (v) {
    return function (fn) {
        return function __do() {
            var result = $foreign.debounceImpl(v)(false)(true)(fn)();
            return result.call;
        };
    };
};

// | Debounce with trailing edge (same as debounce)
var debounceTrailing = debounce;
export {
    debounce,
    throttle,
    debounceLeading,
    debounceTrailing,
    debounceBoth,
    throttleLeading,
    throttleTrailing,
    debounceWithCancel,
    throttleWithCancel,
    Milliseconds,
    eqMilliseconds,
    ordMilliseconds,
    showMilliseconds
};
