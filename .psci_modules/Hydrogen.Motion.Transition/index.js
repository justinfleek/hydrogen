// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                     // hydrogen // transition
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | CSS Transitions
// |
// | Type-safe transition utilities for animations.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Motion.Transition as T
// |
// | -- Predefined transitions
// | T.transitionAll      -- "transition-all"
// | T.transitionColors   -- "transition-colors"
// |
// | -- With duration
// | T.duration T.D300    -- "duration-300"
// |
// | -- Combined
// | T.transition T.All T.D300 T.EaseInOut
// | -- "transition-all duration-300 ease-in-out"
// | ```

// ═══════════════════════════════════════════════════════════════════════════════
//                                                       // transition properties
// ═══════════════════════════════════════════════════════════════════════════════
// | Transition property
var None = /* #__PURE__ */ (function () {
    function None() {

    };
    None.value = new None();
    return None;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                       // transition properties
// ═══════════════════════════════════════════════════════════════════════════════
// | Transition property
var All = /* #__PURE__ */ (function () {
    function All() {

    };
    All.value = new All();
    return All;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                       // transition properties
// ═══════════════════════════════════════════════════════════════════════════════
// | Transition property
var Default = /* #__PURE__ */ (function () {
    function Default() {

    };
    Default.value = new Default();
    return Default;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                       // transition properties
// ═══════════════════════════════════════════════════════════════════════════════
// | Transition property
var Colors = /* #__PURE__ */ (function () {
    function Colors() {

    };
    Colors.value = new Colors();
    return Colors;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                       // transition properties
// ═══════════════════════════════════════════════════════════════════════════════
// | Transition property
var Opacity = /* #__PURE__ */ (function () {
    function Opacity() {

    };
    Opacity.value = new Opacity();
    return Opacity;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                       // transition properties
// ═══════════════════════════════════════════════════════════════════════════════
// | Transition property
var Shadow = /* #__PURE__ */ (function () {
    function Shadow() {

    };
    Shadow.value = new Shadow();
    return Shadow;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                       // transition properties
// ═══════════════════════════════════════════════════════════════════════════════
// | Transition property
var Transform = /* #__PURE__ */ (function () {
    function Transform() {

    };
    Transform.value = new Transform();
    return Transform;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // timing functions
// ═══════════════════════════════════════════════════════════════════════════════
// | Timing function (easing)
var EaseLinear = /* #__PURE__ */ (function () {
    function EaseLinear() {

    };
    EaseLinear.value = new EaseLinear();
    return EaseLinear;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // timing functions
// ═══════════════════════════════════════════════════════════════════════════════
// | Timing function (easing)
var EaseIn = /* #__PURE__ */ (function () {
    function EaseIn() {

    };
    EaseIn.value = new EaseIn();
    return EaseIn;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // timing functions
// ═══════════════════════════════════════════════════════════════════════════════
// | Timing function (easing)
var EaseOut = /* #__PURE__ */ (function () {
    function EaseOut() {

    };
    EaseOut.value = new EaseOut();
    return EaseOut;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // timing functions
// ═══════════════════════════════════════════════════════════════════════════════
// | Timing function (easing)
var EaseInOut = /* #__PURE__ */ (function () {
    function EaseInOut() {

    };
    EaseInOut.value = new EaseInOut();
    return EaseInOut;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // durations
// ═══════════════════════════════════════════════════════════════════════════════
// | Transition duration
var D0 = /* #__PURE__ */ (function () {
    function D0() {

    };
    D0.value = new D0();
    return D0;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // durations
// ═══════════════════════════════════════════════════════════════════════════════
// | Transition duration
var D75 = /* #__PURE__ */ (function () {
    function D75() {

    };
    D75.value = new D75();
    return D75;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // durations
// ═══════════════════════════════════════════════════════════════════════════════
// | Transition duration
var D100 = /* #__PURE__ */ (function () {
    function D100() {

    };
    D100.value = new D100();
    return D100;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // durations
// ═══════════════════════════════════════════════════════════════════════════════
// | Transition duration
var D150 = /* #__PURE__ */ (function () {
    function D150() {

    };
    D150.value = new D150();
    return D150;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // durations
// ═══════════════════════════════════════════════════════════════════════════════
// | Transition duration
var D200 = /* #__PURE__ */ (function () {
    function D200() {

    };
    D200.value = new D200();
    return D200;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // durations
// ═══════════════════════════════════════════════════════════════════════════════
// | Transition duration
var D300 = /* #__PURE__ */ (function () {
    function D300() {

    };
    D300.value = new D300();
    return D300;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // durations
// ═══════════════════════════════════════════════════════════════════════════════
// | Transition duration
var D500 = /* #__PURE__ */ (function () {
    function D500() {

    };
    D500.value = new D500();
    return D500;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // durations
// ═══════════════════════════════════════════════════════════════════════════════
// | Transition duration
var D700 = /* #__PURE__ */ (function () {
    function D700() {

    };
    D700.value = new D700();
    return D700;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // durations
// ═══════════════════════════════════════════════════════════════════════════════
// | Transition duration
var D1000 = /* #__PURE__ */ (function () {
    function D1000() {

    };
    D1000.value = new D1000();
    return D1000;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // delay
// ═══════════════════════════════════════════════════════════════════════════════
// | Transition delay
var Delay0 = /* #__PURE__ */ (function () {
    function Delay0() {

    };
    Delay0.value = new Delay0();
    return Delay0;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // delay
// ═══════════════════════════════════════════════════════════════════════════════
// | Transition delay
var Delay75 = /* #__PURE__ */ (function () {
    function Delay75() {

    };
    Delay75.value = new Delay75();
    return Delay75;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // delay
// ═══════════════════════════════════════════════════════════════════════════════
// | Transition delay
var Delay100 = /* #__PURE__ */ (function () {
    function Delay100() {

    };
    Delay100.value = new Delay100();
    return Delay100;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // delay
// ═══════════════════════════════════════════════════════════════════════════════
// | Transition delay
var Delay150 = /* #__PURE__ */ (function () {
    function Delay150() {

    };
    Delay150.value = new Delay150();
    return Delay150;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // delay
// ═══════════════════════════════════════════════════════════════════════════════
// | Transition delay
var Delay200 = /* #__PURE__ */ (function () {
    function Delay200() {

    };
    Delay200.value = new Delay200();
    return Delay200;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // delay
// ═══════════════════════════════════════════════════════════════════════════════
// | Transition delay
var Delay300 = /* #__PURE__ */ (function () {
    function Delay300() {

    };
    Delay300.value = new Delay300();
    return Delay300;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // delay
// ═══════════════════════════════════════════════════════════════════════════════
// | Transition delay
var Delay500 = /* #__PURE__ */ (function () {
    function Delay500() {

    };
    Delay500.value = new Delay500();
    return Delay500;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // delay
// ═══════════════════════════════════════════════════════════════════════════════
// | Transition delay
var Delay700 = /* #__PURE__ */ (function () {
    function Delay700() {

    };
    Delay700.value = new Delay700();
    return Delay700;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // delay
// ═══════════════════════════════════════════════════════════════════════════════
// | Transition delay
var Delay1000 = /* #__PURE__ */ (function () {
    function Delay1000() {

    };
    Delay1000.value = new Delay1000();
    return Delay1000;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // animation
// ═══════════════════════════════════════════════════════════════════════════════
// | Predefined animations
var AnimateNone = /* #__PURE__ */ (function () {
    function AnimateNone() {

    };
    AnimateNone.value = new AnimateNone();
    return AnimateNone;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // animation
// ═══════════════════════════════════════════════════════════════════════════════
// | Predefined animations
var AnimateSpin = /* #__PURE__ */ (function () {
    function AnimateSpin() {

    };
    AnimateSpin.value = new AnimateSpin();
    return AnimateSpin;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // animation
// ═══════════════════════════════════════════════════════════════════════════════
// | Predefined animations
var AnimatePing = /* #__PURE__ */ (function () {
    function AnimatePing() {

    };
    AnimatePing.value = new AnimatePing();
    return AnimatePing;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // animation
// ═══════════════════════════════════════════════════════════════════════════════
// | Predefined animations
var AnimatePulse = /* #__PURE__ */ (function () {
    function AnimatePulse() {

    };
    AnimatePulse.value = new AnimatePulse();
    return AnimatePulse;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // animation
// ═══════════════════════════════════════════════════════════════════════════════
// | Predefined animations
var AnimateBounce = /* #__PURE__ */ (function () {
    function AnimateBounce() {

    };
    AnimateBounce.value = new AnimateBounce();
    return AnimateBounce;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // animation
// ═══════════════════════════════════════════════════════════════════════════════
// | Predefined animations
var AnimateFadeIn = /* #__PURE__ */ (function () {
    function AnimateFadeIn() {

    };
    AnimateFadeIn.value = new AnimateFadeIn();
    return AnimateFadeIn;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // animation
// ═══════════════════════════════════════════════════════════════════════════════
// | Predefined animations
var AnimateFadeOut = /* #__PURE__ */ (function () {
    function AnimateFadeOut() {

    };
    AnimateFadeOut.value = new AnimateFadeOut();
    return AnimateFadeOut;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // animation
// ═══════════════════════════════════════════════════════════════════════════════
// | Predefined animations
var AnimateSlideIn = /* #__PURE__ */ (function () {
    function AnimateSlideIn() {

    };
    AnimateSlideIn.value = new AnimateSlideIn();
    return AnimateSlideIn;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // animation
// ═══════════════════════════════════════════════════════════════════════════════
// | Predefined animations
var AnimateSlideOut = /* #__PURE__ */ (function () {
    function AnimateSlideOut() {

    };
    AnimateSlideOut.value = new AnimateSlideOut();
    return AnimateSlideOut;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // animation
// ═══════════════════════════════════════════════════════════════════════════════
// | Predefined animations
var AnimateZoomIn = /* #__PURE__ */ (function () {
    function AnimateZoomIn() {

    };
    AnimateZoomIn.value = new AnimateZoomIn();
    return AnimateZoomIn;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // animation
// ═══════════════════════════════════════════════════════════════════════════════
// | Predefined animations
var AnimateZoomOut = /* #__PURE__ */ (function () {
    function AnimateZoomOut() {

    };
    AnimateZoomOut.value = new AnimateZoomOut();
    return AnimateZoomOut;
})();

// | Transition transform only
var transitionTransform = "transition-transform";

// | Transition shadow only
var transitionShadow = "transition-shadow";
var transitionProperty = function (v) {
    if (v instanceof None) {
        return "transition-none";
    };
    if (v instanceof All) {
        return "transition-all";
    };
    if (v instanceof Default) {
        return "transition";
    };
    if (v instanceof Colors) {
        return "transition-colors";
    };
    if (v instanceof Opacity) {
        return "transition-opacity";
    };
    if (v instanceof Shadow) {
        return "transition-shadow";
    };
    if (v instanceof Transform) {
        return "transition-transform";
    };
    throw new Error("Failed pattern match at Hydrogen.Motion.Transition (line 153, column 22 - line 160, column 38): " + [ v.constructor.name ]);
};

// | Transition opacity only
var transitionOpacity = "transition-opacity";

// | No transition
var transitionNone = "transition-none";

// | Default transition (common properties)
var transitionDefault = "transition";

// | Transition colors only
var transitionColors = "transition-colors";

// | Transition all properties
var transitionAll = "transition-all";

// | Convert timing function to Tailwind class
var timingFunction = function (v) {
    if (v instanceof EaseLinear) {
        return "ease-linear";
    };
    if (v instanceof EaseIn) {
        return "ease-in";
    };
    if (v instanceof EaseOut) {
        return "ease-out";
    };
    if (v instanceof EaseInOut) {
        return "ease-in-out";
    };
    throw new Error("Failed pattern match at Hydrogen.Motion.Transition (line 99, column 18 - line 103, column 29): " + [ v.constructor.name ]);
};
var eqTransitionProperty = {
    eq: function (x) {
        return function (y) {
            if (x instanceof None && y instanceof None) {
                return true;
            };
            if (x instanceof All && y instanceof All) {
                return true;
            };
            if (x instanceof Default && y instanceof Default) {
                return true;
            };
            if (x instanceof Colors && y instanceof Colors) {
                return true;
            };
            if (x instanceof Opacity && y instanceof Opacity) {
                return true;
            };
            if (x instanceof Shadow && y instanceof Shadow) {
                return true;
            };
            if (x instanceof Transform && y instanceof Transform) {
                return true;
            };
            return false;
        };
    }
};
var eqTimingFunction = {
    eq: function (x) {
        return function (y) {
            if (x instanceof EaseLinear && y instanceof EaseLinear) {
                return true;
            };
            if (x instanceof EaseIn && y instanceof EaseIn) {
                return true;
            };
            if (x instanceof EaseOut && y instanceof EaseOut) {
                return true;
            };
            if (x instanceof EaseInOut && y instanceof EaseInOut) {
                return true;
            };
            return false;
        };
    }
};
var eqDuration = {
    eq: function (x) {
        return function (y) {
            if (x instanceof D0 && y instanceof D0) {
                return true;
            };
            if (x instanceof D75 && y instanceof D75) {
                return true;
            };
            if (x instanceof D100 && y instanceof D100) {
                return true;
            };
            if (x instanceof D150 && y instanceof D150) {
                return true;
            };
            if (x instanceof D200 && y instanceof D200) {
                return true;
            };
            if (x instanceof D300 && y instanceof D300) {
                return true;
            };
            if (x instanceof D500 && y instanceof D500) {
                return true;
            };
            if (x instanceof D700 && y instanceof D700) {
                return true;
            };
            if (x instanceof D1000 && y instanceof D1000) {
                return true;
            };
            return false;
        };
    }
};
var eqDelay = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Delay0 && y instanceof Delay0) {
                return true;
            };
            if (x instanceof Delay75 && y instanceof Delay75) {
                return true;
            };
            if (x instanceof Delay100 && y instanceof Delay100) {
                return true;
            };
            if (x instanceof Delay150 && y instanceof Delay150) {
                return true;
            };
            if (x instanceof Delay200 && y instanceof Delay200) {
                return true;
            };
            if (x instanceof Delay300 && y instanceof Delay300) {
                return true;
            };
            if (x instanceof Delay500 && y instanceof Delay500) {
                return true;
            };
            if (x instanceof Delay700 && y instanceof Delay700) {
                return true;
            };
            if (x instanceof Delay1000 && y instanceof Delay1000) {
                return true;
            };
            return false;
        };
    }
};
var eqAnimation = {
    eq: function (x) {
        return function (y) {
            if (x instanceof AnimateNone && y instanceof AnimateNone) {
                return true;
            };
            if (x instanceof AnimateSpin && y instanceof AnimateSpin) {
                return true;
            };
            if (x instanceof AnimatePing && y instanceof AnimatePing) {
                return true;
            };
            if (x instanceof AnimatePulse && y instanceof AnimatePulse) {
                return true;
            };
            if (x instanceof AnimateBounce && y instanceof AnimateBounce) {
                return true;
            };
            if (x instanceof AnimateFadeIn && y instanceof AnimateFadeIn) {
                return true;
            };
            if (x instanceof AnimateFadeOut && y instanceof AnimateFadeOut) {
                return true;
            };
            if (x instanceof AnimateSlideIn && y instanceof AnimateSlideIn) {
                return true;
            };
            if (x instanceof AnimateSlideOut && y instanceof AnimateSlideOut) {
                return true;
            };
            if (x instanceof AnimateZoomIn && y instanceof AnimateZoomIn) {
                return true;
            };
            if (x instanceof AnimateZoomOut && y instanceof AnimateZoomOut) {
                return true;
            };
            return false;
        };
    }
};

// | Convert duration to Tailwind class
var duration = function (v) {
    if (v instanceof D0) {
        return "duration-0";
    };
    if (v instanceof D75) {
        return "duration-75";
    };
    if (v instanceof D100) {
        return "duration-100";
    };
    if (v instanceof D150) {
        return "duration-150";
    };
    if (v instanceof D200) {
        return "duration-200";
    };
    if (v instanceof D300) {
        return "duration-300";
    };
    if (v instanceof D500) {
        return "duration-500";
    };
    if (v instanceof D700) {
        return "duration-700";
    };
    if (v instanceof D1000) {
        return "duration-1000";
    };
    throw new Error("Failed pattern match at Hydrogen.Motion.Transition (line 73, column 12 - line 82, column 27): " + [ v.constructor.name ]);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // combined
// ═══════════════════════════════════════════════════════════════════════════════
// | Combined transition class string
var transition = function (prop) {
    return function (dur) {
        return function (timing) {
            return transitionProperty(prop) + (" " + (duration(dur) + (" " + timingFunction(timing))));
        };
    };
};

// | Convert delay to Tailwind class
var delay = function (v) {
    if (v instanceof Delay0) {
        return "delay-0";
    };
    if (v instanceof Delay75) {
        return "delay-75";
    };
    if (v instanceof Delay100) {
        return "delay-100";
    };
    if (v instanceof Delay150) {
        return "delay-150";
    };
    if (v instanceof Delay200) {
        return "delay-200";
    };
    if (v instanceof Delay300) {
        return "delay-300";
    };
    if (v instanceof Delay500) {
        return "delay-500";
    };
    if (v instanceof Delay700) {
        return "delay-700";
    };
    if (v instanceof Delay1000) {
        return "delay-1000";
    };
    throw new Error("Failed pattern match at Hydrogen.Motion.Transition (line 125, column 9 - line 134, column 28): " + [ v.constructor.name ]);
};

// | Convert animation to Tailwind class
var animate = function (v) {
    if (v instanceof AnimateNone) {
        return "animate-none";
    };
    if (v instanceof AnimateSpin) {
        return "animate-spin";
    };
    if (v instanceof AnimatePing) {
        return "animate-ping";
    };
    if (v instanceof AnimatePulse) {
        return "animate-pulse";
    };
    if (v instanceof AnimateBounce) {
        return "animate-bounce";
    };
    if (v instanceof AnimateFadeIn) {
        return "animate-in fade-in";
    };
    if (v instanceof AnimateFadeOut) {
        return "animate-out fade-out";
    };
    if (v instanceof AnimateSlideIn) {
        return "animate-in slide-in-from-bottom";
    };
    if (v instanceof AnimateSlideOut) {
        return "animate-out slide-out-to-bottom";
    };
    if (v instanceof AnimateZoomIn) {
        return "animate-in zoom-in";
    };
    if (v instanceof AnimateZoomOut) {
        return "animate-out zoom-out";
    };
    throw new Error("Failed pattern match at Hydrogen.Motion.Transition (line 222, column 11 - line 233, column 43): " + [ v.constructor.name ]);
};
export {
    transitionNone,
    transitionAll,
    transitionDefault,
    transitionColors,
    transitionOpacity,
    transitionShadow,
    transitionTransform,
    D0,
    D75,
    D100,
    D150,
    D200,
    D300,
    D500,
    D700,
    D1000,
    duration,
    EaseLinear,
    EaseIn,
    EaseOut,
    EaseInOut,
    timingFunction,
    Delay0,
    Delay75,
    Delay100,
    Delay150,
    Delay200,
    Delay300,
    Delay500,
    Delay700,
    Delay1000,
    delay,
    transition,
    None,
    All,
    Default,
    Colors,
    Opacity,
    Shadow,
    Transform,
    animate,
    AnimateNone,
    AnimateSpin,
    AnimatePing,
    AnimatePulse,
    AnimateBounce,
    AnimateFadeIn,
    AnimateFadeOut,
    AnimateSlideIn,
    AnimateSlideOut,
    AnimateZoomIn,
    AnimateZoomOut,
    eqDuration,
    eqTimingFunction,
    eqDelay,
    eqTransitionProperty,
    eqAnimation
};
