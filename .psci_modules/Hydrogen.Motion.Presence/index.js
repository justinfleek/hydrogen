// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                       // hydrogen // presence
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Enter/exit animations for components
// |
// | AnimatePresence enables animations when components mount and unmount,
// | with support for exit animations and layout transitions.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Motion.Presence as P
// |
// | -- Animate mounting/unmounting
// | P.animatePresence
// |   { mode: P.Sync
// |   , initial: true
// |   }
// |   [ when showModal $
// |       P.motion
// |         { initial: P.variant { opacity: 0.0, scale: 0.9 }
// |         , animate: P.variant { opacity: 1.0, scale: 1.0 }
// |         , exit: P.variant { opacity: 0.0, scale: 0.9 }
// |         }
// |         modalContent
// |   ]
// |
// | -- Wait for exit before entering new content
// | P.animatePresence { mode: P.Wait, initial: false }
// |   [ P.motion
// |       { key: currentPage
// |       , initial: P.slideIn P.FromRight
// |       , exit: P.slideOut P.ToLeft
// |       }
// |       pageContent
// |   ]
// |
// | -- With callbacks
// | P.motion
// |   { onAnimationStart: Console.log "Started"
// |   , onAnimationComplete: Console.log "Done"
// |   }
// |   content
// | ```
import * as $foreign from "./foreign.js";
import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Semigroup from "../Data.Semigroup/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
import * as Effect from "../Effect/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Properties from "../Halogen.HTML.Properties/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showNumber);
var pure = /* #__PURE__ */ Control_Applicative.pure(Effect.applicativeEffect);
var append1 = /* #__PURE__ */ Data_Semigroup.append(Data_Semigroup.semigroupArray);
var show1 = /* #__PURE__ */ Data_Show.show(Data_Show.showBoolean);

// | Presence state for a component
var Entering = /* #__PURE__ */ (function () {
    function Entering() {

    };
    Entering.value = new Entering();
    return Entering;
})();

// | Presence state for a component
var Present = /* #__PURE__ */ (function () {
    function Present() {

    };
    Present.value = new Present();
    return Present;
})();

// | Presence state for a component
var Exiting = /* #__PURE__ */ (function () {
    function Exiting() {

    };
    Exiting.value = new Exiting();
    return Exiting;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Animation presence mode
var Sync = /* #__PURE__ */ (function () {
    function Sync() {

    };
    Sync.value = new Sync();
    return Sync;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Animation presence mode
var Wait = /* #__PURE__ */ (function () {
    function Wait() {

    };
    Wait.value = new Wait();
    return Wait;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Animation presence mode
var PopLayout = /* #__PURE__ */ (function () {
    function PopLayout() {

    };
    PopLayout.value = new PopLayout();
    return PopLayout;
})();

// | Direction for slide animations
var FromTop = /* #__PURE__ */ (function () {
    function FromTop() {

    };
    FromTop.value = new FromTop();
    return FromTop;
})();

// | Direction for slide animations
var FromBottom = /* #__PURE__ */ (function () {
    function FromBottom() {

    };
    FromBottom.value = new FromBottom();
    return FromBottom;
})();

// | Direction for slide animations
var FromLeft = /* #__PURE__ */ (function () {
    function FromLeft() {

    };
    FromLeft.value = new FromLeft();
    return FromLeft;
})();

// | Direction for slide animations
var FromRight = /* #__PURE__ */ (function () {
    function FromRight() {

    };
    FromRight.value = new FromRight();
    return FromRight;
})();

// | Direction for slide animations
var ToTop = /* #__PURE__ */ (function () {
    function ToTop() {

    };
    ToTop.value = new ToTop();
    return ToTop;
})();

// | Direction for slide animations
var ToBottom = /* #__PURE__ */ (function () {
    function ToBottom() {

    };
    ToBottom.value = new ToBottom();
    return ToBottom;
})();

// | Direction for slide animations
var ToLeft = /* #__PURE__ */ (function () {
    function ToLeft() {

    };
    ToLeft.value = new ToLeft();
    return ToLeft;
})();

// | Direction for slide animations
var ToRight = /* #__PURE__ */ (function () {
    function ToRight() {

    };
    ToRight.value = new ToRight();
    return ToRight;
})();

// | Add easing to a variant
var withEasing = function (easing) {
    return function (v) {
        return {
            opacity: v.opacity,
            scale: v.scale,
            scaleX: v.scaleX,
            scaleY: v.scaleY,
            x: v.x,
            y: v.y,
            rotate: v.rotate,
            duration: v.duration,
            delay: v.delay,
            easing: new Data_Maybe.Just(easing)
        };
    };
};

// | Add duration to a variant
var withDuration = function (v) {
    return function (v1) {
        return {
            opacity: v1.opacity,
            scale: v1.scale,
            scaleX: v1.scaleX,
            scaleY: v1.scaleY,
            x: v1.x,
            y: v1.y,
            rotate: v1.rotate,
            delay: v1.delay,
            easing: v1.easing,
            duration: new Data_Maybe.Just(v)
        };
    };
};

// | Add delay to a variant
var withDelay = function (v) {
    return function (v1) {
        return {
            opacity: v1.opacity,
            scale: v1.scale,
            scaleX: v1.scaleX,
            scaleY: v1.scaleY,
            x: v1.x,
            y: v1.y,
            rotate: v1.rotate,
            duration: v1.duration,
            easing: v1.easing,
            delay: new Data_Maybe.Just(v)
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // internals
// ═══════════════════════════════════════════════════════════════════════════════
// | Convert variant to JSON string for data attribute
var variantToString = function (v) {
    var propStr = function (v1) {
        return function (v2) {
            if (v2 instanceof Data_Maybe.Just) {
                return "\"" + (v1 + ("\":\"" + (v2.value0 + "\"")));
            };
            if (v2 instanceof Data_Maybe.Nothing) {
                return "";
            };
            throw new Error("Failed pattern match at Hydrogen.Motion.Presence (line 472, column 3 - line 472, column 46): " + [ v1.constructor.name, v2.constructor.name ]);
        };
    };
    var prop = function (v1) {
        return function (v2) {
            if (v2 instanceof Data_Maybe.Just) {
                return "\"" + (v1 + ("\":" + show(v2.value0)));
            };
            if (v2 instanceof Data_Maybe.Nothing) {
                return "";
            };
            throw new Error("Failed pattern match at Hydrogen.Motion.Presence (line 468, column 3 - line 468, column 43): " + [ v1.constructor.name, v2.constructor.name ]);
        };
    };
    var intercalate = function (v1) {
        return function (v2) {
            if (v2.length === 0) {
                return "";
            };
            return $foreign.intercalateImpl(v1)(v2);
        };
    };
    var filter = function (v1) {
        return function (v2) {
            if (v2.length === 0) {
                return [  ];
            };
            return $foreign.filterImpl(v1)(v2);
        };
    };
    var filterEmpty = filter(function (s) {
        return s !== "";
    });
    return "{" + (intercalate(",")(filterEmpty([ prop("opacity")(v.opacity), prop("scale")(v.scale), prop("scaleX")(v.scaleX), prop("scaleY")(v.scaleY), prop("x")(v.x), prop("y")(v.y), prop("rotate")(v.rotate), prop("duration")(v.duration), prop("delay")(v.delay), propStr("easing")(v.easing) ])) + "}");
};

// | Convert variant to initial inline style
var variantToInitialStyle = function (v) {
    var stylePropTransform = function (v1) {
        return function (v2) {
            if (v2 instanceof Data_Maybe.Just) {
                return "transform: " + (v1 + ("(" + (show(v2.value0) + ")")));
            };
            if (v2 instanceof Data_Maybe.Nothing) {
                return "";
            };
            throw new Error("Failed pattern match at Hydrogen.Motion.Presence (line 503, column 3 - line 503, column 83): " + [ v1.constructor.name, v2.constructor.name ]);
        };
    };
    var stylePropPx = function (v1) {
        return function (v2) {
            if (v2 instanceof Data_Maybe.Just) {
                return "transform: " + (v1 + ("(" + (show(v2.value0) + "px)")));
            };
            if (v2 instanceof Data_Maybe.Nothing) {
                return "";
            };
            throw new Error("Failed pattern match at Hydrogen.Motion.Presence (line 506, column 3 - line 506, column 78): " + [ v1.constructor.name, v2.constructor.name ]);
        };
    };
    var styleProp = function (v1) {
        return function (v2) {
            if (v2 instanceof Data_Maybe.Just) {
                return v1 + (": " + show(v2.value0));
            };
            if (v2 instanceof Data_Maybe.Nothing) {
                return "";
            };
            throw new Error("Failed pattern match at Hydrogen.Motion.Presence (line 500, column 3 - line 500, column 51): " + [ v1.constructor.name, v2.constructor.name ]);
        };
    };
    return $foreign.intercalateImpl("; ")($foreign.filterImpl(function (s) {
        return s !== "";
    })([ styleProp("opacity")(v.opacity), stylePropTransform("scale")(v.scale), stylePropPx("translateX")(v.x), stylePropPx("translateY")(v.y) ]));
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // variants
// ═══════════════════════════════════════════════════════════════════════════════
// | Create a variant with specified properties
var variant = function (v) {
    return {
        opacity: new Data_Maybe.Just(v.opacity),
        scale: new Data_Maybe.Just(v.scale),
        scaleX: Data_Maybe.Nothing.value,
        scaleY: Data_Maybe.Nothing.value,
        x: Data_Maybe.Nothing.value,
        y: Data_Maybe.Nothing.value,
        rotate: Data_Maybe.Nothing.value,
        duration: Data_Maybe.Nothing.value,
        delay: Data_Maybe.Nothing.value,
        easing: Data_Maybe.Nothing.value
    };
};
var usePresence = function (element) {
    var stateFromString = function (v) {
        if (v === "entering") {
            return Entering.value;
        };
        if (v === "exiting") {
            return Exiting.value;
        };
        return Present.value;
    };
    return function __do() {
        var result = $foreign.usePresenceImpl(element)();
        return {
            state: stateFromString(result.state),
            isPresent: result.isPresent
        };
    };
};
var showPresenceState = {
    show: function (v) {
        if (v instanceof Entering) {
            return "Entering";
        };
        if (v instanceof Present) {
            return "Present";
        };
        if (v instanceof Exiting) {
            return "Exiting";
        };
        throw new Error("Failed pattern match at Hydrogen.Motion.Presence (line 125, column 1 - line 128, column 27): " + [ v.constructor.name ]);
    }
};
var showPresenceMode = {
    show: function (v) {
        if (v instanceof Sync) {
            return "Sync";
        };
        if (v instanceof Wait) {
            return "Wait";
        };
        if (v instanceof PopLayout) {
            return "PopLayout";
        };
        throw new Error("Failed pattern match at Hydrogen.Motion.Presence (line 112, column 1 - line 115, column 31): " + [ v.constructor.name ]);
    }
};

// | Set exit complete callback
var onExitComplete = function (v) {
    return Halogen_HTML_Properties.attr("data-motion-on-exit")("true");
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // callbacks
// ═══════════════════════════════════════════════════════════════════════════════
// | Set animation start callback
var onAnimationStart = function (v) {
    return Halogen_HTML_Properties.attr("data-motion-on-start")("true");
};

// | Set animation complete callback
var onAnimationComplete = function (v) {
    return Halogen_HTML_Properties.attr("data-motion-on-complete")("true");
};

// | Motion span element
var motionSpan = function (config) {
    return function (children) {
        return Halogen_HTML_Elements.span([ Halogen_HTML_Properties.attr("data-motion")("true"), Halogen_HTML_Properties.attr("data-motion-initial")(variantToString(config.initial)), Halogen_HTML_Properties.attr("data-motion-animate")(variantToString(config.animate)), Halogen_HTML_Properties.attr("data-motion-exit")(variantToString(config.exit)), Halogen_HTML_Properties.style(variantToInitialStyle(config.initial)) ])(children);
    };
};

// | Motion div element
var motionDiv = function (config) {
    return function (children) {
        var keyAttr = function (v) {
            if (v instanceof Data_Maybe.Just) {
                return [ Halogen_HTML_Properties.attr("data-motion-key")(v.value0) ];
            };
            if (v instanceof Data_Maybe.Nothing) {
                return [  ];
            };
            throw new Error("Failed pattern match at Hydrogen.Motion.Presence (line 256, column 3 - line 256, column 65): " + [ v.constructor.name ]);
        };
        return Halogen_HTML_Elements.div(append1([ Halogen_HTML_Properties.attr("data-motion")("true"), Halogen_HTML_Properties.attr("data-motion-initial")(variantToString(config.initial)), Halogen_HTML_Properties.attr("data-motion-animate")(variantToString(config.animate)), Halogen_HTML_Properties.attr("data-motion-exit")(variantToString(config.exit)), Halogen_HTML_Properties.style(variantToInitialStyle(config.initial)) ])(keyAttr(config.key)))(children);
    };
};

// | Motion wrapper (generic element)
var motion = function (config) {
    return function (children) {
        var keyAttr = function (v) {
            if (v instanceof Data_Maybe.Just) {
                return [ Halogen_HTML_Properties.attr("data-motion-key")(v.value0) ];
            };
            if (v instanceof Data_Maybe.Nothing) {
                return [  ];
            };
            throw new Error("Failed pattern match at Hydrogen.Motion.Presence (line 236, column 3 - line 236, column 65): " + [ v.constructor.name ]);
        };
        return Halogen_HTML_Elements.div(append1([ Halogen_HTML_Properties.attr("data-motion")("true"), Halogen_HTML_Properties.attr("data-motion-initial")(variantToString(config.initial)), Halogen_HTML_Properties.attr("data-motion-animate")(variantToString(config.animate)), Halogen_HTML_Properties.attr("data-motion-exit")(variantToString(config.exit)), Halogen_HTML_Properties.style(variantToInitialStyle(config.initial)) ])(keyAttr(config.key)))(children);
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // layout animation
// ═══════════════════════════════════════════════════════════════════════════════
// | Set layout ID for shared layout animations
var layoutId = function (id) {
    return Halogen_HTML_Properties.attr("data-layout-id")(id);
};

// | Set layout group
var layoutGroup = function (group) {
    return Halogen_HTML_Properties.attr("data-layout-group")(group);
};
var eqPresenceState = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Entering && y instanceof Entering) {
                return true;
            };
            if (x instanceof Present && y instanceof Present) {
                return true;
            };
            if (x instanceof Exiting && y instanceof Exiting) {
                return true;
            };
            return false;
        };
    }
};
var eqPresenceMode = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Sync && y instanceof Sync) {
                return true;
            };
            if (x instanceof Wait && y instanceof Wait) {
                return true;
            };
            if (x instanceof PopLayout && y instanceof PopLayout) {
                return true;
            };
            return false;
        };
    }
};
var eqDirection = {
    eq: function (x) {
        return function (y) {
            if (x instanceof FromTop && y instanceof FromTop) {
                return true;
            };
            if (x instanceof FromBottom && y instanceof FromBottom) {
                return true;
            };
            if (x instanceof FromLeft && y instanceof FromLeft) {
                return true;
            };
            if (x instanceof FromRight && y instanceof FromRight) {
                return true;
            };
            if (x instanceof ToTop && y instanceof ToTop) {
                return true;
            };
            if (x instanceof ToBottom && y instanceof ToBottom) {
                return true;
            };
            if (x instanceof ToLeft && y instanceof ToLeft) {
                return true;
            };
            if (x instanceof ToRight && y instanceof ToRight) {
                return true;
            };
            return false;
        };
    }
};

// | Empty variant (no changes)
var emptyVariant = /* #__PURE__ */ (function () {
    return {
        opacity: Data_Maybe.Nothing.value,
        scale: Data_Maybe.Nothing.value,
        scaleX: Data_Maybe.Nothing.value,
        scaleY: Data_Maybe.Nothing.value,
        x: Data_Maybe.Nothing.value,
        y: Data_Maybe.Nothing.value,
        rotate: Data_Maybe.Nothing.value,
        duration: Data_Maybe.Nothing.value,
        delay: Data_Maybe.Nothing.value,
        easing: Data_Maybe.Nothing.value
    };
})();

// | Fade in variant
var fadeIn = /* #__PURE__ */ (function () {
    return {
        scale: emptyVariant.scale,
        scaleX: emptyVariant.scaleX,
        scaleY: emptyVariant.scaleY,
        x: emptyVariant.x,
        y: emptyVariant.y,
        rotate: emptyVariant.rotate,
        duration: emptyVariant.duration,
        delay: emptyVariant.delay,
        easing: emptyVariant.easing,
        opacity: new Data_Maybe.Just(1.0)
    };
})();

// | Fade out variant
var fadeOut = /* #__PURE__ */ (function () {
    return {
        scale: emptyVariant.scale,
        scaleX: emptyVariant.scaleX,
        scaleY: emptyVariant.scaleY,
        x: emptyVariant.x,
        y: emptyVariant.y,
        rotate: emptyVariant.rotate,
        duration: emptyVariant.duration,
        delay: emptyVariant.delay,
        easing: emptyVariant.easing,
        opacity: new Data_Maybe.Just(0.0)
    };
})();

// | Pop in (scale with overshoot feel)
var popIn = /* #__PURE__ */ (function () {
    return {
        scaleX: emptyVariant.scaleX,
        scaleY: emptyVariant.scaleY,
        x: emptyVariant.x,
        y: emptyVariant.y,
        rotate: emptyVariant.rotate,
        duration: emptyVariant.duration,
        delay: emptyVariant.delay,
        scale: new Data_Maybe.Just(1.0),
        opacity: new Data_Maybe.Just(1.0),
        easing: new Data_Maybe.Just("cubic-bezier(0.34, 1.56, 0.64, 1)")
    };
})();

// | Pop out
var popOut = /* #__PURE__ */ (function () {
    return {
        scaleX: emptyVariant.scaleX,
        scaleY: emptyVariant.scaleY,
        x: emptyVariant.x,
        y: emptyVariant.y,
        rotate: emptyVariant.rotate,
        duration: emptyVariant.duration,
        delay: emptyVariant.delay,
        easing: emptyVariant.easing,
        scale: new Data_Maybe.Just(0.8),
        opacity: new Data_Maybe.Just(0.0)
    };
})();

// | Scale in variant
var scaleIn = /* #__PURE__ */ (function () {
    return {
        scaleX: emptyVariant.scaleX,
        scaleY: emptyVariant.scaleY,
        x: emptyVariant.x,
        y: emptyVariant.y,
        rotate: emptyVariant.rotate,
        duration: emptyVariant.duration,
        delay: emptyVariant.delay,
        easing: emptyVariant.easing,
        scale: new Data_Maybe.Just(1.0),
        opacity: new Data_Maybe.Just(1.0)
    };
})();

// | Scale out variant
var scaleOut = /* #__PURE__ */ (function () {
    return {
        scaleX: emptyVariant.scaleX,
        scaleY: emptyVariant.scaleY,
        x: emptyVariant.x,
        y: emptyVariant.y,
        rotate: emptyVariant.rotate,
        duration: emptyVariant.duration,
        delay: emptyVariant.delay,
        easing: emptyVariant.easing,
        scale: new Data_Maybe.Just(0.0),
        opacity: new Data_Maybe.Just(0.0)
    };
})();

// | Slide in from direction
var slideIn = function (dir) {
    if (dir instanceof FromTop) {
        return {
            scale: emptyVariant.scale,
            scaleX: emptyVariant.scaleX,
            scaleY: emptyVariant.scaleY,
            x: emptyVariant.x,
            rotate: emptyVariant.rotate,
            duration: emptyVariant.duration,
            delay: emptyVariant.delay,
            easing: emptyVariant.easing,
            y: new Data_Maybe.Just(0.0),
            opacity: new Data_Maybe.Just(1.0)
        };
    };
    if (dir instanceof FromBottom) {
        return {
            scale: emptyVariant.scale,
            scaleX: emptyVariant.scaleX,
            scaleY: emptyVariant.scaleY,
            x: emptyVariant.x,
            rotate: emptyVariant.rotate,
            duration: emptyVariant.duration,
            delay: emptyVariant.delay,
            easing: emptyVariant.easing,
            y: new Data_Maybe.Just(0.0),
            opacity: new Data_Maybe.Just(1.0)
        };
    };
    if (dir instanceof FromLeft) {
        return {
            scale: emptyVariant.scale,
            scaleX: emptyVariant.scaleX,
            scaleY: emptyVariant.scaleY,
            y: emptyVariant.y,
            rotate: emptyVariant.rotate,
            duration: emptyVariant.duration,
            delay: emptyVariant.delay,
            easing: emptyVariant.easing,
            x: new Data_Maybe.Just(0.0),
            opacity: new Data_Maybe.Just(1.0)
        };
    };
    if (dir instanceof FromRight) {
        return {
            scale: emptyVariant.scale,
            scaleX: emptyVariant.scaleX,
            scaleY: emptyVariant.scaleY,
            y: emptyVariant.y,
            rotate: emptyVariant.rotate,
            duration: emptyVariant.duration,
            delay: emptyVariant.delay,
            easing: emptyVariant.easing,
            x: new Data_Maybe.Just(0.0),
            opacity: new Data_Maybe.Just(1.0)
        };
    };
    if (dir instanceof ToTop) {
        return {
            opacity: emptyVariant.opacity,
            scale: emptyVariant.scale,
            scaleX: emptyVariant.scaleX,
            scaleY: emptyVariant.scaleY,
            x: emptyVariant.x,
            rotate: emptyVariant.rotate,
            duration: emptyVariant.duration,
            delay: emptyVariant.delay,
            easing: emptyVariant.easing,
            y: new Data_Maybe.Just(-20.0)
        };
    };
    if (dir instanceof ToBottom) {
        return {
            opacity: emptyVariant.opacity,
            scale: emptyVariant.scale,
            scaleX: emptyVariant.scaleX,
            scaleY: emptyVariant.scaleY,
            x: emptyVariant.x,
            rotate: emptyVariant.rotate,
            duration: emptyVariant.duration,
            delay: emptyVariant.delay,
            easing: emptyVariant.easing,
            y: new Data_Maybe.Just(20.0)
        };
    };
    if (dir instanceof ToLeft) {
        return {
            opacity: emptyVariant.opacity,
            scale: emptyVariant.scale,
            scaleX: emptyVariant.scaleX,
            scaleY: emptyVariant.scaleY,
            y: emptyVariant.y,
            rotate: emptyVariant.rotate,
            duration: emptyVariant.duration,
            delay: emptyVariant.delay,
            easing: emptyVariant.easing,
            x: new Data_Maybe.Just(-20.0)
        };
    };
    if (dir instanceof ToRight) {
        return {
            opacity: emptyVariant.opacity,
            scale: emptyVariant.scale,
            scaleX: emptyVariant.scaleX,
            scaleY: emptyVariant.scaleY,
            y: emptyVariant.y,
            rotate: emptyVariant.rotate,
            duration: emptyVariant.duration,
            delay: emptyVariant.delay,
            easing: emptyVariant.easing,
            x: new Data_Maybe.Just(20.0)
        };
    };
    throw new Error("Failed pattern match at Hydrogen.Motion.Presence (line 321, column 15 - line 329, column 44): " + [ dir.constructor.name ]);
};

// | Slide out to direction
var slideOut = function (dir) {
    if (dir instanceof FromTop) {
        return {
            scale: emptyVariant.scale,
            scaleX: emptyVariant.scaleX,
            scaleY: emptyVariant.scaleY,
            x: emptyVariant.x,
            rotate: emptyVariant.rotate,
            duration: emptyVariant.duration,
            delay: emptyVariant.delay,
            easing: emptyVariant.easing,
            y: new Data_Maybe.Just(-20.0),
            opacity: new Data_Maybe.Just(0.0)
        };
    };
    if (dir instanceof FromBottom) {
        return {
            scale: emptyVariant.scale,
            scaleX: emptyVariant.scaleX,
            scaleY: emptyVariant.scaleY,
            x: emptyVariant.x,
            rotate: emptyVariant.rotate,
            duration: emptyVariant.duration,
            delay: emptyVariant.delay,
            easing: emptyVariant.easing,
            y: new Data_Maybe.Just(20.0),
            opacity: new Data_Maybe.Just(0.0)
        };
    };
    if (dir instanceof FromLeft) {
        return {
            scale: emptyVariant.scale,
            scaleX: emptyVariant.scaleX,
            scaleY: emptyVariant.scaleY,
            y: emptyVariant.y,
            rotate: emptyVariant.rotate,
            duration: emptyVariant.duration,
            delay: emptyVariant.delay,
            easing: emptyVariant.easing,
            x: new Data_Maybe.Just(-20.0),
            opacity: new Data_Maybe.Just(0.0)
        };
    };
    if (dir instanceof FromRight) {
        return {
            scale: emptyVariant.scale,
            scaleX: emptyVariant.scaleX,
            scaleY: emptyVariant.scaleY,
            y: emptyVariant.y,
            rotate: emptyVariant.rotate,
            duration: emptyVariant.duration,
            delay: emptyVariant.delay,
            easing: emptyVariant.easing,
            x: new Data_Maybe.Just(20.0),
            opacity: new Data_Maybe.Just(0.0)
        };
    };
    if (dir instanceof ToTop) {
        return {
            scale: emptyVariant.scale,
            scaleX: emptyVariant.scaleX,
            scaleY: emptyVariant.scaleY,
            x: emptyVariant.x,
            rotate: emptyVariant.rotate,
            duration: emptyVariant.duration,
            delay: emptyVariant.delay,
            easing: emptyVariant.easing,
            y: new Data_Maybe.Just(-20.0),
            opacity: new Data_Maybe.Just(0.0)
        };
    };
    if (dir instanceof ToBottom) {
        return {
            scale: emptyVariant.scale,
            scaleX: emptyVariant.scaleX,
            scaleY: emptyVariant.scaleY,
            x: emptyVariant.x,
            rotate: emptyVariant.rotate,
            duration: emptyVariant.duration,
            delay: emptyVariant.delay,
            easing: emptyVariant.easing,
            y: new Data_Maybe.Just(20.0),
            opacity: new Data_Maybe.Just(0.0)
        };
    };
    if (dir instanceof ToLeft) {
        return {
            scale: emptyVariant.scale,
            scaleX: emptyVariant.scaleX,
            scaleY: emptyVariant.scaleY,
            y: emptyVariant.y,
            rotate: emptyVariant.rotate,
            duration: emptyVariant.duration,
            delay: emptyVariant.delay,
            easing: emptyVariant.easing,
            x: new Data_Maybe.Just(-20.0),
            opacity: new Data_Maybe.Just(0.0)
        };
    };
    if (dir instanceof ToRight) {
        return {
            scale: emptyVariant.scale,
            scaleX: emptyVariant.scaleX,
            scaleY: emptyVariant.scaleY,
            y: emptyVariant.y,
            rotate: emptyVariant.rotate,
            duration: emptyVariant.duration,
            delay: emptyVariant.delay,
            easing: emptyVariant.easing,
            x: new Data_Maybe.Just(20.0),
            opacity: new Data_Maybe.Just(0.0)
        };
    };
    throw new Error("Failed pattern match at Hydrogen.Motion.Presence (line 333, column 16 - line 341, column 64): " + [ dir.constructor.name ]);
};

// | Default presence configuration
var defaultPresenceConfig = /* #__PURE__ */ (function () {
    return {
        mode: Sync.value,
        initial: true,
        onExitComplete: pure(Data_Unit.unit)
    };
})();

// | Default motion configuration
var defaultMotionConfig = /* #__PURE__ */ (function () {
    return {
        initial: emptyVariant,
        animate: emptyVariant,
        exit: emptyVariant,
        key: Data_Maybe.Nothing.value,
        onAnimationStart: pure(Data_Unit.unit),
        onAnimationComplete: pure(Data_Unit.unit)
    };
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                         // variant composition
// ═══════════════════════════════════════════════════════════════════════════════
// | Combine two variants (second takes precedence)
var combineVariants = function (v1) {
    return function (v2) {
        var orElse = function (v) {
            return function (v3) {
                if (v instanceof Data_Maybe.Just) {
                    return new Data_Maybe.Just(v.value0);
                };
                if (v instanceof Data_Maybe.Nothing) {
                    return v3;
                };
                throw new Error("Failed pattern match at Hydrogen.Motion.Presence (line 385, column 3 - line 385, column 52): " + [ v.constructor.name, v3.constructor.name ]);
            };
        };
        return {
            opacity: orElse(v2.opacity)(v1.opacity),
            scale: orElse(v2.scale)(v1.scale),
            scaleX: orElse(v2.scaleX)(v1.scaleX),
            scaleY: orElse(v2.scaleY)(v1.scaleY),
            x: orElse(v2.x)(v1.x),
            y: orElse(v2.y)(v1.y),
            rotate: orElse(v2.rotate)(v1.rotate),
            duration: orElse(v2.duration)(v1.duration),
            delay: orElse(v2.delay)(v1.delay),
            easing: orElse(v2.easing)(v1.easing)
        };
    };
};

// | AnimatePresence wrapper component
var animatePresence = function (config) {
    return function (children) {
        var modeToString = function (v) {
            if (v instanceof Sync) {
                return "sync";
            };
            if (v instanceof Wait) {
                return "wait";
            };
            if (v instanceof PopLayout) {
                return "pop-layout";
            };
            throw new Error("Failed pattern match at Hydrogen.Motion.Presence (line 190, column 3 - line 190, column 29): " + [ v.constructor.name ]);
        };
        return Halogen_HTML_Elements.div([ Halogen_HTML_Properties.attr("data-animate-presence")("true"), Halogen_HTML_Properties.attr("data-presence-mode")(modeToString(config.mode)), Halogen_HTML_Properties.attr("data-presence-initial")(show1(config.initial)) ])(children);
    };
};
export {
    Sync,
    Wait,
    PopLayout,
    animatePresence,
    defaultPresenceConfig,
    motion,
    motionDiv,
    motionSpan,
    defaultMotionConfig,
    variant,
    emptyVariant,
    fadeIn,
    fadeOut,
    FromTop,
    FromBottom,
    FromLeft,
    FromRight,
    ToTop,
    ToBottom,
    ToLeft,
    ToRight,
    slideIn,
    slideOut,
    scaleIn,
    scaleOut,
    popIn,
    popOut,
    combineVariants,
    withDuration,
    withDelay,
    withEasing,
    Entering,
    Present,
    Exiting,
    usePresence,
    onAnimationStart,
    onAnimationComplete,
    onExitComplete,
    layoutId,
    layoutGroup,
    eqPresenceMode,
    showPresenceMode,
    eqPresenceState,
    showPresenceState,
    eqDirection
};
