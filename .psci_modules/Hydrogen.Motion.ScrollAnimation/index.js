// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                 // hydrogen // scroll-animation
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Scroll-triggered animations
// |
// | Intersection Observer based scroll animations with parallax support,
// | progress tracking, and animation presets.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Motion.ScrollAnimation as SA
// |
// | -- Trigger animation when element enters viewport
// | SA.onEnterViewport element
// |   { animation: SA.FadeIn
// |   , threshold: 0.2        -- 20% visible
// |   , once: true            -- Only animate once
// |   , delay: Milliseconds 0.0
// |   }
// |
// | -- Progress-based animation (parallax)
// | SA.onScrollProgress element
// |   { onProgress: \progress -> setTransform ("translateY(" <> show (progress * 50.0) <> "px)")
// |   , start: 0.0            -- Start when element enters bottom
// |   , end: 1.0              -- End when element leaves top
// |   }
// |
// | -- Smooth scroll to element
// | SA.scrollToElement element { behavior: SA.Smooth, block: SA.Center }
// |
// | -- Detect scroll direction
// | SA.onScrollDirection
// |   { onUp: Console.log "Scrolling up"
// |   , onDown: Console.log "Scrolling down"
// |   }
// | ```
import * as $foreign from "./foreign.js";
import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
import * as Effect from "../Effect/index.js";
var pure = /* #__PURE__ */ Control_Applicative.pure(Effect.applicativeEffect);

// | Horizontal alignment
var InlineStart = /* #__PURE__ */ (function () {
    function InlineStart() {

    };
    InlineStart.value = new InlineStart();
    return InlineStart;
})();

// | Horizontal alignment
var InlineCenter = /* #__PURE__ */ (function () {
    function InlineCenter() {

    };
    InlineCenter.value = new InlineCenter();
    return InlineCenter;
})();

// | Horizontal alignment
var InlineEnd = /* #__PURE__ */ (function () {
    function InlineEnd() {

    };
    InlineEnd.value = new InlineEnd();
    return InlineEnd;
})();

// | Horizontal alignment
var InlineNearest = /* #__PURE__ */ (function () {
    function InlineNearest() {

    };
    InlineNearest.value = new InlineNearest();
    return InlineNearest;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // scroll direction
// ═══════════════════════════════════════════════════════════════════════════════
// | Scroll direction
var ScrollingUp = /* #__PURE__ */ (function () {
    function ScrollingUp() {

    };
    ScrollingUp.value = new ScrollingUp();
    return ScrollingUp;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // scroll direction
// ═══════════════════════════════════════════════════════════════════════════════
// | Scroll direction
var ScrollingDown = /* #__PURE__ */ (function () {
    function ScrollingDown() {

    };
    ScrollingDown.value = new ScrollingDown();
    return ScrollingDown;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // scroll direction
// ═══════════════════════════════════════════════════════════════════════════════
// | Scroll direction
var NotScrolling = /* #__PURE__ */ (function () {
    function NotScrolling() {

    };
    NotScrolling.value = new NotScrolling();
    return NotScrolling;
})();

// | Vertical alignment
var BlockStart = /* #__PURE__ */ (function () {
    function BlockStart() {

    };
    BlockStart.value = new BlockStart();
    return BlockStart;
})();

// | Vertical alignment
var BlockCenter = /* #__PURE__ */ (function () {
    function BlockCenter() {

    };
    BlockCenter.value = new BlockCenter();
    return BlockCenter;
})();

// | Vertical alignment
var BlockEnd = /* #__PURE__ */ (function () {
    function BlockEnd() {

    };
    BlockEnd.value = new BlockEnd();
    return BlockEnd;
})();

// | Vertical alignment
var BlockNearest = /* #__PURE__ */ (function () {
    function BlockNearest() {

    };
    BlockNearest.value = new BlockNearest();
    return BlockNearest;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // smooth scroll
// ═══════════════════════════════════════════════════════════════════════════════
// | Scroll behavior
var Smooth = /* #__PURE__ */ (function () {
    function Smooth() {

    };
    Smooth.value = new Smooth();
    return Smooth;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // smooth scroll
// ═══════════════════════════════════════════════════════════════════════════════
// | Scroll behavior
var Instant = /* #__PURE__ */ (function () {
    function Instant() {

    };
    Instant.value = new Instant();
    return Instant;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // smooth scroll
// ═══════════════════════════════════════════════════════════════════════════════
// | Scroll behavior
var Auto = /* #__PURE__ */ (function () {
    function Auto() {

    };
    Auto.value = new Auto();
    return Auto;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // animation presets
// ═══════════════════════════════════════════════════════════════════════════════
// | Predefined animation presets
var FadeIn = /* #__PURE__ */ (function () {
    function FadeIn() {

    };
    FadeIn.value = new FadeIn();
    return FadeIn;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // animation presets
// ═══════════════════════════════════════════════════════════════════════════════
// | Predefined animation presets
var FadeInUp = /* #__PURE__ */ (function () {
    function FadeInUp() {

    };
    FadeInUp.value = new FadeInUp();
    return FadeInUp;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // animation presets
// ═══════════════════════════════════════════════════════════════════════════════
// | Predefined animation presets
var FadeInDown = /* #__PURE__ */ (function () {
    function FadeInDown() {

    };
    FadeInDown.value = new FadeInDown();
    return FadeInDown;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // animation presets
// ═══════════════════════════════════════════════════════════════════════════════
// | Predefined animation presets
var FadeInLeft = /* #__PURE__ */ (function () {
    function FadeInLeft() {

    };
    FadeInLeft.value = new FadeInLeft();
    return FadeInLeft;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // animation presets
// ═══════════════════════════════════════════════════════════════════════════════
// | Predefined animation presets
var FadeInRight = /* #__PURE__ */ (function () {
    function FadeInRight() {

    };
    FadeInRight.value = new FadeInRight();
    return FadeInRight;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // animation presets
// ═══════════════════════════════════════════════════════════════════════════════
// | Predefined animation presets
var SlideUp = /* #__PURE__ */ (function () {
    function SlideUp() {

    };
    SlideUp.value = new SlideUp();
    return SlideUp;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // animation presets
// ═══════════════════════════════════════════════════════════════════════════════
// | Predefined animation presets
var SlideDown = /* #__PURE__ */ (function () {
    function SlideDown() {

    };
    SlideDown.value = new SlideDown();
    return SlideDown;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // animation presets
// ═══════════════════════════════════════════════════════════════════════════════
// | Predefined animation presets
var SlideLeft = /* #__PURE__ */ (function () {
    function SlideLeft() {

    };
    SlideLeft.value = new SlideLeft();
    return SlideLeft;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // animation presets
// ═══════════════════════════════════════════════════════════════════════════════
// | Predefined animation presets
var SlideRight = /* #__PURE__ */ (function () {
    function SlideRight() {

    };
    SlideRight.value = new SlideRight();
    return SlideRight;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // animation presets
// ═══════════════════════════════════════════════════════════════════════════════
// | Predefined animation presets
var ScaleIn = /* #__PURE__ */ (function () {
    function ScaleIn() {

    };
    ScaleIn.value = new ScaleIn();
    return ScaleIn;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // animation presets
// ═══════════════════════════════════════════════════════════════════════════════
// | Predefined animation presets
var ScaleInUp = /* #__PURE__ */ (function () {
    function ScaleInUp() {

    };
    ScaleInUp.value = new ScaleInUp();
    return ScaleInUp;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // animation presets
// ═══════════════════════════════════════════════════════════════════════════════
// | Predefined animation presets
var ZoomIn = /* #__PURE__ */ (function () {
    function ZoomIn() {

    };
    ZoomIn.value = new ZoomIn();
    return ZoomIn;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // animation presets
// ═══════════════════════════════════════════════════════════════════════════════
// | Predefined animation presets
var FlipIn = /* #__PURE__ */ (function () {
    function FlipIn() {

    };
    FlipIn.value = new FlipIn();
    return FlipIn;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // animation presets
// ═══════════════════════════════════════════════════════════════════════════════
// | Predefined animation presets
var RotateIn = /* #__PURE__ */ (function () {
    function RotateIn() {

    };
    RotateIn.value = new RotateIn();
    return RotateIn;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // animation presets
// ═══════════════════════════════════════════════════════════════════════════════
// | Predefined animation presets
var Bounce = /* #__PURE__ */ (function () {
    function Bounce() {

    };
    Bounce.value = new Bounce();
    return Bounce;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // animation presets
// ═══════════════════════════════════════════════════════════════════════════════
// | Predefined animation presets
var Custom = /* #__PURE__ */ (function () {
    function Custom(value0) {
        this.value0 = value0;
    };
    Custom.create = function (value0) {
        return new Custom(value0);
    };
    return Custom;
})();
var showScrollDirection = {
    show: function (v) {
        if (v instanceof ScrollingUp) {
            return "ScrollingUp";
        };
        if (v instanceof ScrollingDown) {
            return "ScrollingDown";
        };
        if (v instanceof NotScrolling) {
            return "NotScrolling";
        };
        throw new Error("Failed pattern match at Hydrogen.Motion.ScrollAnimation (line 335, column 1 - line 338, column 37): " + [ v.constructor.name ]);
    }
};
var showAnimationPreset = {
    show: function (v) {
        if (v instanceof FadeIn) {
            return "FadeIn";
        };
        if (v instanceof FadeInUp) {
            return "FadeInUp";
        };
        if (v instanceof FadeInDown) {
            return "FadeInDown";
        };
        if (v instanceof FadeInLeft) {
            return "FadeInLeft";
        };
        if (v instanceof FadeInRight) {
            return "FadeInRight";
        };
        if (v instanceof SlideUp) {
            return "SlideUp";
        };
        if (v instanceof SlideDown) {
            return "SlideDown";
        };
        if (v instanceof SlideLeft) {
            return "SlideLeft";
        };
        if (v instanceof SlideRight) {
            return "SlideRight";
        };
        if (v instanceof ScaleIn) {
            return "ScaleIn";
        };
        if (v instanceof ScaleInUp) {
            return "ScaleInUp";
        };
        if (v instanceof ZoomIn) {
            return "ZoomIn";
        };
        if (v instanceof FlipIn) {
            return "FlipIn";
        };
        if (v instanceof RotateIn) {
            return "RotateIn";
        };
        if (v instanceof Bounce) {
            return "Bounce";
        };
        if (v instanceof Custom) {
            return "Custom " + v.value0;
        };
        throw new Error("Failed pattern match at Hydrogen.Motion.ScrollAnimation (line 107, column 1 - line 123, column 35): " + [ v.constructor.name ]);
    }
};

// | Convert preset to Tailwind/CSS animation classes
var presetToClasses = function (v) {
    if (v instanceof FadeIn) {
        return {
            initial: "opacity-0",
            animate: "opacity-100 transition-opacity duration-500"
        };
    };
    if (v instanceof FadeInUp) {
        return {
            initial: "opacity-0 translate-y-8",
            animate: "opacity-100 translate-y-0 transition-all duration-500"
        };
    };
    if (v instanceof FadeInDown) {
        return {
            initial: "opacity-0 -translate-y-8",
            animate: "opacity-100 translate-y-0 transition-all duration-500"
        };
    };
    if (v instanceof FadeInLeft) {
        return {
            initial: "opacity-0 -translate-x-8",
            animate: "opacity-100 translate-x-0 transition-all duration-500"
        };
    };
    if (v instanceof FadeInRight) {
        return {
            initial: "opacity-0 translate-x-8",
            animate: "opacity-100 translate-x-0 transition-all duration-500"
        };
    };
    if (v instanceof SlideUp) {
        return {
            initial: "translate-y-full",
            animate: "translate-y-0 transition-transform duration-500"
        };
    };
    if (v instanceof SlideDown) {
        return {
            initial: "-translate-y-full",
            animate: "translate-y-0 transition-transform duration-500"
        };
    };
    if (v instanceof SlideLeft) {
        return {
            initial: "translate-x-full",
            animate: "translate-x-0 transition-transform duration-500"
        };
    };
    if (v instanceof SlideRight) {
        return {
            initial: "-translate-x-full",
            animate: "translate-x-0 transition-transform duration-500"
        };
    };
    if (v instanceof ScaleIn) {
        return {
            initial: "scale-0 opacity-0",
            animate: "scale-100 opacity-100 transition-all duration-500"
        };
    };
    if (v instanceof ScaleInUp) {
        return {
            initial: "scale-75 opacity-0 translate-y-4",
            animate: "scale-100 opacity-100 translate-y-0 transition-all duration-500"
        };
    };
    if (v instanceof ZoomIn) {
        return {
            initial: "scale-50 opacity-0",
            animate: "scale-100 opacity-100 transition-all duration-700 ease-out"
        };
    };
    if (v instanceof FlipIn) {
        return {
            initial: "opacity-0 rotateX-90",
            animate: "opacity-100 rotateX-0 transition-all duration-500"
        };
    };
    if (v instanceof RotateIn) {
        return {
            initial: "opacity-0 rotate-180 scale-50",
            animate: "opacity-100 rotate-0 scale-100 transition-all duration-500"
        };
    };
    if (v instanceof Bounce) {
        return {
            initial: "opacity-0 translate-y-8",
            animate: "opacity-100 translate-y-0 animate-bounce transition-all duration-500"
        };
    };
    if (v instanceof Custom) {
        return {
            initial: "",
            animate: v.value0
        };
    };
    throw new Error("Failed pattern match at Hydrogen.Motion.ScrollAnimation (line 127, column 19 - line 191, column 6): " + [ v.constructor.name ]);
};
var onViewportChange = function (element) {
    return function (config) {
        return $foreign.onViewportChangeImpl(element)({
            threshold: config.threshold,
            rootMargin: "0px",
            onChange: config.onChange
        });
    };
};
var onScrollProgress = $foreign.onScrollProgressImpl;
var onScrollDirection = $foreign.onScrollDirectionImpl;
var onExitViewport = function (element) {
    return function (config) {
        return $foreign.onExitViewportImpl(element)({
            threshold: config.threshold,
            rootMargin: "0px",
            onExit: config.onExit
        });
    };
};
var onEnterViewport = function (element) {
    return function (config) {
        var unwrapMs = function (v) {
            return v;
        };
        return $foreign.onEnterViewportImpl(element)({
            animation: presetToClasses(config.animation),
            threshold: config.threshold,
            rootMargin: config.rootMargin,
            once: config.once,
            delay: unwrapMs(config.delay),
            onEnter: config.onEnter,
            onExit: config.onExit
        });
    };
};
var inlineToString = function (v) {
    if (v instanceof InlineStart) {
        return "start";
    };
    if (v instanceof InlineCenter) {
        return "center";
    };
    if (v instanceof InlineEnd) {
        return "end";
    };
    if (v instanceof InlineNearest) {
        return "nearest";
    };
    throw new Error("Failed pattern match at Hydrogen.Motion.ScrollAnimation (line 425, column 1 - line 425, column 41): " + [ v.constructor.name ]);
};
var getScrollDirection = function __do() {
    var dir = $foreign.getScrollDirectionImpl();
    if (dir === "up") {
        return ScrollingUp.value;
    };
    if (dir === "down") {
        return ScrollingDown.value;
    };
    return NotScrolling.value;
};
var eqScrollInline = {
    eq: function (x) {
        return function (y) {
            if (x instanceof InlineStart && y instanceof InlineStart) {
                return true;
            };
            if (x instanceof InlineCenter && y instanceof InlineCenter) {
                return true;
            };
            if (x instanceof InlineEnd && y instanceof InlineEnd) {
                return true;
            };
            if (x instanceof InlineNearest && y instanceof InlineNearest) {
                return true;
            };
            return false;
        };
    }
};
var eqScrollDirection = {
    eq: function (x) {
        return function (y) {
            if (x instanceof ScrollingUp && y instanceof ScrollingUp) {
                return true;
            };
            if (x instanceof ScrollingDown && y instanceof ScrollingDown) {
                return true;
            };
            if (x instanceof NotScrolling && y instanceof NotScrolling) {
                return true;
            };
            return false;
        };
    }
};
var eqScrollBlock = {
    eq: function (x) {
        return function (y) {
            if (x instanceof BlockStart && y instanceof BlockStart) {
                return true;
            };
            if (x instanceof BlockCenter && y instanceof BlockCenter) {
                return true;
            };
            if (x instanceof BlockEnd && y instanceof BlockEnd) {
                return true;
            };
            if (x instanceof BlockNearest && y instanceof BlockNearest) {
                return true;
            };
            return false;
        };
    }
};
var eqScrollBehavior = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Smooth && y instanceof Smooth) {
                return true;
            };
            if (x instanceof Instant && y instanceof Instant) {
                return true;
            };
            if (x instanceof Auto && y instanceof Auto) {
                return true;
            };
            return false;
        };
    }
};
var eqAnimationPreset = {
    eq: function (x) {
        return function (y) {
            if (x instanceof FadeIn && y instanceof FadeIn) {
                return true;
            };
            if (x instanceof FadeInUp && y instanceof FadeInUp) {
                return true;
            };
            if (x instanceof FadeInDown && y instanceof FadeInDown) {
                return true;
            };
            if (x instanceof FadeInLeft && y instanceof FadeInLeft) {
                return true;
            };
            if (x instanceof FadeInRight && y instanceof FadeInRight) {
                return true;
            };
            if (x instanceof SlideUp && y instanceof SlideUp) {
                return true;
            };
            if (x instanceof SlideDown && y instanceof SlideDown) {
                return true;
            };
            if (x instanceof SlideLeft && y instanceof SlideLeft) {
                return true;
            };
            if (x instanceof SlideRight && y instanceof SlideRight) {
                return true;
            };
            if (x instanceof ScaleIn && y instanceof ScaleIn) {
                return true;
            };
            if (x instanceof ScaleInUp && y instanceof ScaleInUp) {
                return true;
            };
            if (x instanceof ZoomIn && y instanceof ZoomIn) {
                return true;
            };
            if (x instanceof FlipIn && y instanceof FlipIn) {
                return true;
            };
            if (x instanceof RotateIn && y instanceof RotateIn) {
                return true;
            };
            if (x instanceof Bounce && y instanceof Bounce) {
                return true;
            };
            if (x instanceof Custom && y instanceof Custom) {
                return x.value0 === y.value0;
            };
            return false;
        };
    }
};

// | Default viewport configuration
var defaultViewportConfig = /* #__PURE__ */ (function () {
    return {
        animation: FadeInUp.value,
        threshold: 0.1,
        rootMargin: "0px",
        once: true,
        delay: 0.0,
        onEnter: pure(Data_Unit.unit),
        onExit: pure(Data_Unit.unit)
    };
})();

// | Default scroll options
var defaultScrollOptions = /* #__PURE__ */ (function () {
    return {
        behavior: Smooth.value,
        block: BlockStart.value,
        inline: InlineNearest.value
    };
})();

// | Default progress configuration
var defaultProgressConfig = {
    onProgress: function (v) {
        return pure(Data_Unit.unit);
    },
    start: 0.0,
    end: 1.0,
    clamp: true
};
var blockToString = function (v) {
    if (v instanceof BlockStart) {
        return "start";
    };
    if (v instanceof BlockCenter) {
        return "center";
    };
    if (v instanceof BlockEnd) {
        return "end";
    };
    if (v instanceof BlockNearest) {
        return "nearest";
    };
    throw new Error("Failed pattern match at Hydrogen.Motion.ScrollAnimation (line 419, column 1 - line 419, column 39): " + [ v.constructor.name ]);
};
var behaviorToString = function (v) {
    if (v instanceof Smooth) {
        return "smooth";
    };
    if (v instanceof Instant) {
        return "instant";
    };
    if (v instanceof Auto) {
        return "auto";
    };
    throw new Error("Failed pattern match at Hydrogen.Motion.ScrollAnimation (line 414, column 1 - line 414, column 45): " + [ v.constructor.name ]);
};
var scrollToElement = function (element) {
    return function (opts) {
        return $foreign.scrollToElementImpl(element)({
            behavior: behaviorToString(opts.behavior),
            block: blockToString(opts.block),
            inline: inlineToString(opts.inline)
        });
    };
};
var scrollToPosition = function (pos) {
    return function (behavior) {
        return $foreign.scrollToPositionImpl(pos)(behaviorToString(behavior));
    };
};
var scrollToTop = function (behavior) {
    return $foreign.scrollToTopImpl(behaviorToString(behavior));
};
export {
    disconnectObserver,
    reconnectObserver
} from "./foreign.js";
export {
    FadeIn,
    FadeInUp,
    FadeInDown,
    FadeInLeft,
    FadeInRight,
    SlideUp,
    SlideDown,
    SlideLeft,
    SlideRight,
    ScaleIn,
    ScaleInUp,
    ZoomIn,
    FlipIn,
    RotateIn,
    Bounce,
    Custom,
    presetToClasses,
    onEnterViewport,
    onExitViewport,
    onViewportChange,
    defaultViewportConfig,
    onScrollProgress,
    defaultProgressConfig,
    ScrollingUp,
    ScrollingDown,
    NotScrolling,
    onScrollDirection,
    getScrollDirection,
    Smooth,
    Instant,
    Auto,
    BlockStart,
    BlockCenter,
    BlockEnd,
    BlockNearest,
    InlineStart,
    InlineCenter,
    InlineEnd,
    InlineNearest,
    scrollToElement,
    scrollToTop,
    scrollToPosition,
    defaultScrollOptions,
    eqAnimationPreset,
    showAnimationPreset,
    eqScrollDirection,
    showScrollDirection,
    eqScrollBehavior,
    eqScrollBlock,
    eqScrollInline
};
