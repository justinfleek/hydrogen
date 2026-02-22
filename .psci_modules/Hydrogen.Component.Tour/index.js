// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                           // hydrogen // tour
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Product tour / onboarding component
// |
// | Step-by-step guided tours with element highlighting and tooltips.
// |
// | ## Features
// |
// | - Step-by-step tour
// | - Highlight target elements
// | - Tooltip with content
// | - Navigation (next, prev, skip)
// | - Step counter
// | - Keyboard navigation
// | - Scroll to step
// | - Backdrop overlay
// | - Progress bar
// | - Callbacks: onStart, onStep, onComplete, onSkip
// | - Persist progress (localStorage)
// | - Conditional steps
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Component.Tour as Tour
// |
// | -- Define tour steps
// | tourSteps :: Array Tour.Step
// | tourSteps =
// |   [ Tour.step
// |       { target: "#welcome-button"
// |       , title: "Welcome!"
// |       , content: "Click here to get started."
// |       }
// |   , Tour.step
// |       { target: "#sidebar"
// |       , title: "Navigation"
// |       , content: "Use the sidebar to navigate."
// |       , placement: Tour.Right
// |       }
// |   , Tour.step
// |       { target: "#settings"
// |       , title: "Settings"
// |       , content: "Customize your experience here."
// |       , condition: \state -> state.showAdvanced
// |       }
// |   ]
// |
// | -- Render tour
// | Tour.tour
// |   [ Tour.steps tourSteps
// |   , Tour.showProgress true
// |   , Tour.onComplete HandleTourComplete
// |   , Tour.persistKey "onboarding-tour"
// |   ]
// |
// | -- Or with manual control
// | Tour.tour
// |   [ Tour.steps tourSteps
// |   , Tour.currentStep state.tourStep
// |   , Tour.isActive state.tourActive
// |   , Tour.onStepChange HandleStepChange
// |   ]
// | ```
import * as $foreign from "./foreign.js";
import * as Control_Applicative from "../Control.Applicative/index.js";
import * as DOM_HTML_Indexed_ButtonType from "../DOM.HTML.Indexed.ButtonType/index.js";
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Semigroup from "../Data.Semigroup/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
import * as Effect from "../Effect/index.js";
import * as Halogen_HTML_Core from "../Halogen.HTML.Core/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Events from "../Halogen.HTML.Events/index.js";
import * as Halogen_HTML_Properties from "../Halogen.HTML.Properties/index.js";
import * as Halogen_HTML_Properties_ARIA from "../Halogen.HTML.Properties.ARIA/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);
var show1 = /* #__PURE__ */ Data_Show.show(Data_Show.showNumber);
var append1 = /* #__PURE__ */ Data_Semigroup.append(Data_Semigroup.semigroupArray);
var type_ = /* #__PURE__ */ Halogen_HTML_Properties.type_(Halogen_HTML_Core.isPropButtonType);
var pure = /* #__PURE__ */ Control_Applicative.pure(Effect.applicativeEffect);

// | Scroll behavior when moving to a step
var Smooth = /* #__PURE__ */ (function () {
    function Smooth() {

    };
    Smooth.value = new Smooth();
    return Smooth;
})();

// | Scroll behavior when moving to a step
var Instant = /* #__PURE__ */ (function () {
    function Instant() {

    };
    Instant.value = new Instant();
    return Instant;
})();

// | Scroll behavior when moving to a step
var None = /* #__PURE__ */ (function () {
    function None() {

    };
    None.value = new None();
    return None;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Tooltip placement relative to target
var Top = /* #__PURE__ */ (function () {
    function Top() {

    };
    Top.value = new Top();
    return Top;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Tooltip placement relative to target
var TopStart = /* #__PURE__ */ (function () {
    function TopStart() {

    };
    TopStart.value = new TopStart();
    return TopStart;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Tooltip placement relative to target
var TopEnd = /* #__PURE__ */ (function () {
    function TopEnd() {

    };
    TopEnd.value = new TopEnd();
    return TopEnd;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Tooltip placement relative to target
var Bottom = /* #__PURE__ */ (function () {
    function Bottom() {

    };
    Bottom.value = new Bottom();
    return Bottom;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Tooltip placement relative to target
var BottomStart = /* #__PURE__ */ (function () {
    function BottomStart() {

    };
    BottomStart.value = new BottomStart();
    return BottomStart;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Tooltip placement relative to target
var BottomEnd = /* #__PURE__ */ (function () {
    function BottomEnd() {

    };
    BottomEnd.value = new BottomEnd();
    return BottomEnd;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Tooltip placement relative to target
var Left = /* #__PURE__ */ (function () {
    function Left() {

    };
    Left.value = new Left();
    return Left;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Tooltip placement relative to target
var LeftStart = /* #__PURE__ */ (function () {
    function LeftStart() {

    };
    LeftStart.value = new LeftStart();
    return LeftStart;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Tooltip placement relative to target
var LeftEnd = /* #__PURE__ */ (function () {
    function LeftEnd() {

    };
    LeftEnd.value = new LeftEnd();
    return LeftEnd;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Tooltip placement relative to target
var Right = /* #__PURE__ */ (function () {
    function Right() {

    };
    Right.value = new Right();
    return Right;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Tooltip placement relative to target
var RightStart = /* #__PURE__ */ (function () {
    function RightStart() {

    };
    RightStart.value = new RightStart();
    return RightStart;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Tooltip placement relative to target
var RightEnd = /* #__PURE__ */ (function () {
    function RightEnd() {

    };
    RightEnd.value = new RightEnd();
    return RightEnd;
})();

// | Tour progress indicator
// |
// | Dots or progress bar showing current position
var tourProgress = function (currentIdx) {
    return function (total) {
        var renderDot = function (idx) {
            return function (v) {
                var isActiveStep = idx === currentIdx;
                var activeClass = (function () {
                    if (isActiveStep) {
                        return "bg-primary w-3";
                    };
                    return "bg-muted-foreground/50 w-2";
                })();
                return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "tour-progress-dot h-2 rounded-full transition-all", activeClass ]) ])([  ]);
            };
        };
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "tour-progress flex items-center gap-1" ]), Halogen_HTML_Properties_ARIA.label("Step " + (show(currentIdx + 1 | 0) + (" of " + show(total)))) ])(Data_Array.mapWithIndex(renderDot)(Data_Array.replicate(total)(Data_Unit.unit)));
    };
};

// | Tour overlay
// |
// | Semi-transparent backdrop
var tourOverlay = function (opacity) {
    return function (allowClick) {
        var pointerEvents = (function () {
            if (allowClick) {
                return "pointer-events-none";
            };
            return "";
        })();
        var opacityStyle = "opacity: " + show1(opacity);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "tour-overlay fixed inset-0 bg-black transition-opacity", pointerEvents ]), Halogen_HTML_Properties.attr("style")(opacityStyle), Halogen_HTML_Properties_ARIA.hidden("true") ])([  ]);
    };
};

// | Tour navigation
// |
// | Previous, Next, Skip buttons
var tourNavigation = function (props) {
    return function (total) {
        var skipHandler = (function () {
            if (props.onSkip instanceof Data_Maybe.Just) {
                return [ Halogen_HTML_Events.onClick(function (v) {
                    return props.onSkip.value0(Data_Unit.unit);
                }) ];
            };
            if (props.onSkip instanceof Data_Maybe.Nothing) {
                return [  ];
            };
            throw new Error("Failed pattern match at Hydrogen.Component.Tour (line 625, column 19 - line 627, column 20): " + [ props.onSkip.constructor.name ]);
        })();
        var prevHandler = (function () {
            if (props.onStepChange instanceof Data_Maybe.Just) {
                return [ Halogen_HTML_Events.onClick(function (v) {
                    return props.onStepChange.value0(props.currentStep - 1 | 0);
                }) ];
            };
            if (props.onStepChange instanceof Data_Maybe.Nothing) {
                return [  ];
            };
            throw new Error("Failed pattern match at Hydrogen.Component.Tour (line 617, column 19 - line 619, column 20): " + [ props.onStepChange.constructor.name ]);
        })();
        var nextHandler = (function () {
            if (props.onStepChange instanceof Data_Maybe.Just) {
                return [ Halogen_HTML_Events.onClick(function (v) {
                    return props.onStepChange.value0(props.currentStep + 1 | 0);
                }) ];
            };
            if (props.onStepChange instanceof Data_Maybe.Nothing) {
                return [  ];
            };
            throw new Error("Failed pattern match at Hydrogen.Component.Tour (line 621, column 19 - line 623, column 20): " + [ props.onStepChange.constructor.name ]);
        })();
        var isLast = props.currentStep >= (total - 1 | 0);
        var isFirst = props.currentStep === 0;
        var completeHandler = (function () {
            if (props.onComplete instanceof Data_Maybe.Just) {
                return [ Halogen_HTML_Events.onClick(function (v) {
                    return props.onComplete.value0(Data_Unit.unit);
                }) ];
            };
            if (props.onComplete instanceof Data_Maybe.Nothing) {
                return [  ];
            };
            throw new Error("Failed pattern match at Hydrogen.Component.Tour (line 629, column 23 - line 631, column 20): " + [ props.onComplete.constructor.name ]);
        })();
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "tour-navigation flex items-center gap-2 bg-popover rounded-lg p-2 shadow-lg border" ]) ])([ Halogen_HTML_Elements.button(append1([ Hydrogen_UI_Core.cls([ "tour-skip px-3 py-1.5 text-sm text-muted-foreground hover:text-foreground transition-colors" ]), type_(DOM_HTML_Indexed_ButtonType.ButtonButton.value) ])(skipHandler))([ Halogen_HTML_Core.text("Skip") ]), Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex-1" ]) ])([  ]), (function () {
            if (isFirst) {
                return Halogen_HTML_Core.text("");
            };
            return Halogen_HTML_Elements.button(append1([ Hydrogen_UI_Core.cls([ "tour-prev px-3 py-1.5 text-sm rounded-md border border-input bg-background hover:bg-accent transition-colors" ]), type_(DOM_HTML_Indexed_ButtonType.ButtonButton.value) ])(prevHandler))([ Halogen_HTML_Core.text("Previous") ]);
        })(), Halogen_HTML_Elements.button(append1([ Hydrogen_UI_Core.cls([ "tour-next px-3 py-1.5 text-sm rounded-md bg-primary text-primary-foreground hover:bg-primary/90 transition-colors" ]), type_(DOM_HTML_Indexed_ButtonType.ButtonButton.value) ])((function () {
            if (isLast) {
                return completeHandler;
            };
            return nextHandler;
        })()))([ Halogen_HTML_Core.text((function () {
            if (isLast) {
                return "Complete";
            };
            return "Next";
        })()) ]) ]);
    };
};

// | Tour highlight
// |
// | Highlights the target element
var tourHighlight = function (target) {
    return function (padding) {
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "tour-highlight fixed ring-2 ring-primary ring-offset-2 rounded-md transition-all pointer-events-none z-[55]" ]), Halogen_HTML_Properties.attr("data-target")(target), Halogen_HTML_Properties.attr("data-padding")(show(padding)), Halogen_HTML_Properties_ARIA.hidden("true") ])([  ]);
    };
};

// | Add custom class to tooltip
var tooltipClassName = function (c) {
    return function (props) {
        return {
            placement: props.placement,
            offset: props.offset,
            showArrow: props.showArrow,
            className: props.className + (" " + c)
        };
    };
};

// | Tooltip arrow
var tooltipArrow = function (placementVal) {
    var arrowClass = (function () {
        if (placementVal instanceof Top) {
            return "bottom-0 left-1/2 -translate-x-1/2 translate-y-1/2 rotate-45";
        };
        if (placementVal instanceof TopStart) {
            return "bottom-0 left-4 translate-y-1/2 rotate-45";
        };
        if (placementVal instanceof TopEnd) {
            return "bottom-0 right-4 translate-y-1/2 rotate-45";
        };
        if (placementVal instanceof Bottom) {
            return "top-0 left-1/2 -translate-x-1/2 -translate-y-1/2 rotate-45";
        };
        if (placementVal instanceof BottomStart) {
            return "top-0 left-4 -translate-y-1/2 rotate-45";
        };
        if (placementVal instanceof BottomEnd) {
            return "top-0 right-4 -translate-y-1/2 rotate-45";
        };
        if (placementVal instanceof Left) {
            return "right-0 top-1/2 translate-x-1/2 -translate-y-1/2 rotate-45";
        };
        if (placementVal instanceof LeftStart) {
            return "right-0 top-4 translate-x-1/2 rotate-45";
        };
        if (placementVal instanceof LeftEnd) {
            return "right-0 bottom-4 translate-x-1/2 rotate-45";
        };
        if (placementVal instanceof Right) {
            return "left-0 top-1/2 -translate-x-1/2 -translate-y-1/2 rotate-45";
        };
        if (placementVal instanceof RightStart) {
            return "left-0 top-4 -translate-x-1/2 rotate-45";
        };
        if (placementVal instanceof RightEnd) {
            return "left-0 bottom-4 -translate-x-1/2 rotate-45";
        };
        throw new Error("Failed pattern match at Hydrogen.Component.Tour (line 556, column 18 - line 568, column 63): " + [ placementVal.constructor.name ]);
    })();
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "tour-tooltip-arrow absolute w-3 h-3 bg-popover border-r border-b", arrowClass ]) ])([  ]);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // prop builders
// ═══════════════════════════════════════════════════════════════════════════════
// | Set tour steps
var steps = function (s) {
    return function (props) {
        return {
            currentStep: props.currentStep,
            isActive: props.isActive,
            showProgress: props.showProgress,
            showOverlay: props.showOverlay,
            overlayOpacity: props.overlayOpacity,
            allowClickThrough: props.allowClickThrough,
            scrollBehavior: props.scrollBehavior,
            persistKey: props.persistKey,
            onStart: props.onStart,
            onStep: props.onStep,
            onComplete: props.onComplete,
            onSkip: props.onSkip,
            onStepChange: props.onStepChange,
            className: props.className,
            steps: s
        };
    };
};

// | Create a tour step
var step = function (cfg) {
    return {
        config: {
            target: cfg.target,
            title: cfg.title,
            content: cfg.content,
            placement: Bottom.value,
            offset: 8,
            showArrow: true,
            highlightPadding: 4,
            scrollMargin: 20
        },
        condition: Data_Maybe.Nothing.value
    };
};

// | Start tour
var startTour = function (v) {
    return pure(Data_Unit.unit);
};

// | Skip tour
var skipTour = function (v) {
    return pure(Data_Unit.unit);
};

// | Show progress bar
var showProgress = function (s) {
    return function (props) {
        return {
            steps: props.steps,
            currentStep: props.currentStep,
            isActive: props.isActive,
            showOverlay: props.showOverlay,
            overlayOpacity: props.overlayOpacity,
            allowClickThrough: props.allowClickThrough,
            scrollBehavior: props.scrollBehavior,
            persistKey: props.persistKey,
            onStart: props.onStart,
            onStep: props.onStep,
            onComplete: props.onComplete,
            onSkip: props.onSkip,
            onStepChange: props.onStepChange,
            className: props.className,
            showProgress: s
        };
    };
};

// | Show backdrop overlay
var showOverlay = function (s) {
    return function (props) {
        return {
            steps: props.steps,
            currentStep: props.currentStep,
            isActive: props.isActive,
            showProgress: props.showProgress,
            overlayOpacity: props.overlayOpacity,
            allowClickThrough: props.allowClickThrough,
            scrollBehavior: props.scrollBehavior,
            persistKey: props.persistKey,
            onStart: props.onStart,
            onStep: props.onStep,
            onComplete: props.onComplete,
            onSkip: props.onSkip,
            onStepChange: props.onStepChange,
            className: props.className,
            showOverlay: s
        };
    };
};

// | Set scroll behavior
var scrollBehavior = function (s) {
    return function (props) {
        return {
            steps: props.steps,
            currentStep: props.currentStep,
            isActive: props.isActive,
            showProgress: props.showProgress,
            showOverlay: props.showOverlay,
            overlayOpacity: props.overlayOpacity,
            allowClickThrough: props.allowClickThrough,
            persistKey: props.persistKey,
            onStart: props.onStart,
            onStep: props.onStep,
            onComplete: props.onComplete,
            onSkip: props.onSkip,
            onStepChange: props.onStepChange,
            className: props.className,
            scrollBehavior: s
        };
    };
};

// | Previous step
var prevStep = function (v) {
    return pure(false);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // components
// ═══════════════════════════════════════════════════════════════════════════════
// | Convert placement to string
var placementToString = function (v) {
    if (v instanceof Top) {
        return "top";
    };
    if (v instanceof TopStart) {
        return "top-start";
    };
    if (v instanceof TopEnd) {
        return "top-end";
    };
    if (v instanceof Bottom) {
        return "bottom";
    };
    if (v instanceof BottomStart) {
        return "bottom-start";
    };
    if (v instanceof BottomEnd) {
        return "bottom-end";
    };
    if (v instanceof Left) {
        return "left";
    };
    if (v instanceof LeftStart) {
        return "left-start";
    };
    if (v instanceof LeftEnd) {
        return "left-end";
    };
    if (v instanceof Right) {
        return "right";
    };
    if (v instanceof RightStart) {
        return "right-start";
    };
    if (v instanceof RightEnd) {
        return "right-end";
    };
    throw new Error("Failed pattern match at Hydrogen.Component.Tour (line 446, column 21 - line 458, column 26): " + [ v.constructor.name ]);
};

// | Tour tooltip
// |
// | Tooltip with title and content
var tourTooltip = function (title) {
    return function (content) {
        return function (placementVal) {
            var placementClass = "tour-tooltip-" + placementToString(placementVal);
            return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "tour-tooltip fixed bg-popover text-popover-foreground rounded-lg shadow-lg border p-4 max-w-sm z-[60]", placementClass ]), Halogen_HTML_Properties_ARIA.role("tooltip") ])([ tooltipArrow(placementVal), Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "tour-tooltip-content" ]) ])([ Halogen_HTML_Elements.h4([ Hydrogen_UI_Core.cls([ "tour-tooltip-title font-semibold text-lg mb-2" ]) ])([ Halogen_HTML_Core.text(title) ]), Halogen_HTML_Elements.p([ Hydrogen_UI_Core.cls([ "tour-tooltip-description text-sm text-muted-foreground" ]) ])([ Halogen_HTML_Core.text(content) ]) ]) ]);
        };
    };
};

// | Set tooltip placement
var placement = function (p) {
    return function (props) {
        return {
            offset: props.offset,
            showArrow: props.showArrow,
            className: props.className,
            placement: p
        };
    };
};

// | Set localStorage key for persistence
var persistKey = function (k) {
    return function (props) {
        return {
            steps: props.steps,
            currentStep: props.currentStep,
            isActive: props.isActive,
            showProgress: props.showProgress,
            showOverlay: props.showOverlay,
            overlayOpacity: props.overlayOpacity,
            allowClickThrough: props.allowClickThrough,
            scrollBehavior: props.scrollBehavior,
            onStart: props.onStart,
            onStep: props.onStep,
            onComplete: props.onComplete,
            onSkip: props.onSkip,
            onStepChange: props.onStepChange,
            className: props.className,
            persistKey: new Data_Maybe.Just(k)
        };
    };
};

// | Set overlay opacity
var overlayOpacity = function (o) {
    return function (props) {
        return {
            steps: props.steps,
            currentStep: props.currentStep,
            isActive: props.isActive,
            showProgress: props.showProgress,
            showOverlay: props.showOverlay,
            allowClickThrough: props.allowClickThrough,
            scrollBehavior: props.scrollBehavior,
            persistKey: props.persistKey,
            onStart: props.onStart,
            onStep: props.onStep,
            onComplete: props.onComplete,
            onSkip: props.onSkip,
            onStepChange: props.onStepChange,
            className: props.className,
            overlayOpacity: o
        };
    };
};

// | Set step change handler
var onStepChange = function (handler) {
    return function (props) {
        return {
            steps: props.steps,
            currentStep: props.currentStep,
            isActive: props.isActive,
            showProgress: props.showProgress,
            showOverlay: props.showOverlay,
            overlayOpacity: props.overlayOpacity,
            allowClickThrough: props.allowClickThrough,
            scrollBehavior: props.scrollBehavior,
            persistKey: props.persistKey,
            onStart: props.onStart,
            onStep: props.onStep,
            onComplete: props.onComplete,
            onSkip: props.onSkip,
            className: props.className,
            onStepChange: new Data_Maybe.Just(handler)
        };
    };
};

// | Set step handler
var onStep = function (handler) {
    return function (props) {
        return {
            steps: props.steps,
            currentStep: props.currentStep,
            isActive: props.isActive,
            showProgress: props.showProgress,
            showOverlay: props.showOverlay,
            overlayOpacity: props.overlayOpacity,
            allowClickThrough: props.allowClickThrough,
            scrollBehavior: props.scrollBehavior,
            persistKey: props.persistKey,
            onStart: props.onStart,
            onComplete: props.onComplete,
            onSkip: props.onSkip,
            onStepChange: props.onStepChange,
            className: props.className,
            onStep: new Data_Maybe.Just(handler)
        };
    };
};

// | Set start handler
var onStart = function (handler) {
    return function (props) {
        return {
            steps: props.steps,
            currentStep: props.currentStep,
            isActive: props.isActive,
            showProgress: props.showProgress,
            showOverlay: props.showOverlay,
            overlayOpacity: props.overlayOpacity,
            allowClickThrough: props.allowClickThrough,
            scrollBehavior: props.scrollBehavior,
            persistKey: props.persistKey,
            onStep: props.onStep,
            onComplete: props.onComplete,
            onSkip: props.onSkip,
            onStepChange: props.onStepChange,
            className: props.className,
            onStart: new Data_Maybe.Just(handler)
        };
    };
};

// | Set skip handler
var onSkip = function (handler) {
    return function (props) {
        return {
            steps: props.steps,
            currentStep: props.currentStep,
            isActive: props.isActive,
            showProgress: props.showProgress,
            showOverlay: props.showOverlay,
            overlayOpacity: props.overlayOpacity,
            allowClickThrough: props.allowClickThrough,
            scrollBehavior: props.scrollBehavior,
            persistKey: props.persistKey,
            onStart: props.onStart,
            onStep: props.onStep,
            onComplete: props.onComplete,
            onStepChange: props.onStepChange,
            className: props.className,
            onSkip: new Data_Maybe.Just(handler)
        };
    };
};

// | Set complete handler
var onComplete = function (handler) {
    return function (props) {
        return {
            steps: props.steps,
            currentStep: props.currentStep,
            isActive: props.isActive,
            showProgress: props.showProgress,
            showOverlay: props.showOverlay,
            overlayOpacity: props.overlayOpacity,
            allowClickThrough: props.allowClickThrough,
            scrollBehavior: props.scrollBehavior,
            persistKey: props.persistKey,
            onStart: props.onStart,
            onStep: props.onStep,
            onSkip: props.onSkip,
            onStepChange: props.onStepChange,
            className: props.className,
            onComplete: new Data_Maybe.Just(handler)
        };
    };
};

// | Set tooltip offset
var offset = function (o) {
    return function (props) {
        return {
            placement: props.placement,
            showArrow: props.showArrow,
            className: props.className,
            offset: o
        };
    };
};

// | Next step
var nextStep = function (v) {
    return pure(false);
};

// | Set active state
var isActive = function (a) {
    return function (props) {
        return {
            steps: props.steps,
            currentStep: props.currentStep,
            showProgress: props.showProgress,
            showOverlay: props.showOverlay,
            overlayOpacity: props.overlayOpacity,
            allowClickThrough: props.allowClickThrough,
            scrollBehavior: props.scrollBehavior,
            persistKey: props.persistKey,
            onStart: props.onStart,
            onStep: props.onStep,
            onComplete: props.onComplete,
            onSkip: props.onSkip,
            onStepChange: props.onStepChange,
            className: props.className,
            isActive: a
        };
    };
};

// | Initialize tour
var initTour = function (v) {
    return function (v1) {
        return pure($foreign.unsafeTourElement);
    };
};

// | Go to step
var goToStep = function (v) {
    return function (v1) {
        return pure(false);
    };
};

// | Get progress
var getProgress = function (v) {
    return pure(0);
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
            if (x instanceof None && y instanceof None) {
                return true;
            };
            return false;
        };
    }
};
var eqPlacement = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Top && y instanceof Top) {
                return true;
            };
            if (x instanceof TopStart && y instanceof TopStart) {
                return true;
            };
            if (x instanceof TopEnd && y instanceof TopEnd) {
                return true;
            };
            if (x instanceof Bottom && y instanceof Bottom) {
                return true;
            };
            if (x instanceof BottomStart && y instanceof BottomStart) {
                return true;
            };
            if (x instanceof BottomEnd && y instanceof BottomEnd) {
                return true;
            };
            if (x instanceof Left && y instanceof Left) {
                return true;
            };
            if (x instanceof LeftStart && y instanceof LeftStart) {
                return true;
            };
            if (x instanceof LeftEnd && y instanceof LeftEnd) {
                return true;
            };
            if (x instanceof Right && y instanceof Right) {
                return true;
            };
            if (x instanceof RightStart && y instanceof RightStart) {
                return true;
            };
            if (x instanceof RightEnd && y instanceof RightEnd) {
                return true;
            };
            return false;
        };
    }
};

// | Destroy tour
var destroyTour = function (v) {
    return pure(Data_Unit.unit);
};

// | Default tooltip properties
var defaultTooltipProps = /* #__PURE__ */ (function () {
    return {
        placement: Bottom.value,
        offset: 8,
        showArrow: true,
        className: ""
    };
})();

// | Default tour properties
var defaultProps = /* #__PURE__ */ (function () {
    return {
        steps: [  ],
        currentStep: 0,
        isActive: true,
        showProgress: true,
        showOverlay: true,
        overlayOpacity: 0.5,
        allowClickThrough: false,
        scrollBehavior: Smooth.value,
        persistKey: Data_Maybe.Nothing.value,
        onStart: Data_Maybe.Nothing.value,
        onStep: Data_Maybe.Nothing.value,
        onComplete: Data_Maybe.Nothing.value,
        onSkip: Data_Maybe.Nothing.value,
        onStepChange: Data_Maybe.Nothing.value,
        className: ""
    };
})();

// | Tour component
// |
// | Main tour container with overlay and tooltips
var tour = function (propMods) {
    var props = Data_Array.foldl(function (p) {
        return function (f) {
            return f(p);
        };
    })(defaultProps)(propMods);
    var stepCount = Data_Array.length(props.steps);
    var currentStepData = Data_Array.index(props.steps)(props.currentStep);
    var $70 = !props.isActive || stepCount === 0;
    if ($70) {
        return Halogen_HTML_Core.text("");
    };
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "tour-container fixed inset-0 z-50", props.className ]), Halogen_HTML_Properties.attr("data-step")(show(props.currentStep)), Halogen_HTML_Properties.attr("data-total")(show(stepCount)), Halogen_HTML_Properties_ARIA.role("dialog"), Halogen_HTML_Properties_ARIA.modal("true"), Halogen_HTML_Properties_ARIA.label("Product tour") ])([ (function () {
        if (props.showOverlay) {
            return tourOverlay(props.overlayOpacity)(props.allowClickThrough);
        };
        return Halogen_HTML_Core.text("");
    })(), (function () {
        if (currentStepData instanceof Data_Maybe.Just) {
            return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "tour-step" ]) ])([ tourHighlight(currentStepData.value0.config.target)(currentStepData.value0.config.highlightPadding), tourTooltip(currentStepData.value0.config.title)(currentStepData.value0.config.content)(currentStepData.value0.config.placement) ]);
        };
        if (currentStepData instanceof Data_Maybe.Nothing) {
            return Halogen_HTML_Core.text("");
        };
        throw new Error("Failed pattern match at Hydrogen.Component.Tour (line 486, column 13 - line 496, column 36): " + [ currentStepData.constructor.name ]);
    })(), Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "tour-footer fixed bottom-4 left-1/2 -translate-x-1/2 flex flex-col items-center gap-2" ]) ])([ (function () {
        if (props.showProgress) {
            return tourProgress(props.currentStep)(stepCount);
        };
        return Halogen_HTML_Core.text("");
    })(), tourNavigation(props)(stepCount) ]) ]);
};

// | Set current step index
var currentStep = function (s) {
    return function (props) {
        return {
            steps: props.steps,
            isActive: props.isActive,
            showProgress: props.showProgress,
            showOverlay: props.showOverlay,
            overlayOpacity: props.overlayOpacity,
            allowClickThrough: props.allowClickThrough,
            scrollBehavior: props.scrollBehavior,
            persistKey: props.persistKey,
            onStart: props.onStart,
            onStep: props.onStep,
            onComplete: props.onComplete,
            onSkip: props.onSkip,
            onStepChange: props.onStepChange,
            className: props.className,
            currentStep: s
        };
    };
};

// | Clear progress
var clearProgress = function (v) {
    return pure(Data_Unit.unit);
};

// | Add custom class
var className = function (c) {
    return function (props) {
        return {
            steps: props.steps,
            currentStep: props.currentStep,
            isActive: props.isActive,
            showProgress: props.showProgress,
            showOverlay: props.showOverlay,
            overlayOpacity: props.overlayOpacity,
            allowClickThrough: props.allowClickThrough,
            scrollBehavior: props.scrollBehavior,
            persistKey: props.persistKey,
            onStart: props.onStart,
            onStep: props.onStep,
            onComplete: props.onComplete,
            onSkip: props.onSkip,
            onStepChange: props.onStepChange,
            className: props.className + (" " + c)
        };
    };
};

// | Allow clicking through overlay
var allowClickThrough = function (a) {
    return function (props) {
        return {
            steps: props.steps,
            currentStep: props.currentStep,
            isActive: props.isActive,
            showProgress: props.showProgress,
            showOverlay: props.showOverlay,
            overlayOpacity: props.overlayOpacity,
            scrollBehavior: props.scrollBehavior,
            persistKey: props.persistKey,
            onStart: props.onStart,
            onStep: props.onStep,
            onComplete: props.onComplete,
            onSkip: props.onSkip,
            onStepChange: props.onStepChange,
            className: props.className,
            allowClickThrough: a
        };
    };
};
export {
    tour,
    tourOverlay,
    tourTooltip,
    tourHighlight,
    tourProgress,
    tourNavigation,
    step,
    defaultProps,
    defaultTooltipProps,
    steps,
    currentStep,
    isActive,
    showProgress,
    showOverlay,
    overlayOpacity,
    allowClickThrough,
    scrollBehavior,
    persistKey,
    onStart,
    onStep,
    onComplete,
    onSkip,
    onStepChange,
    className,
    placement,
    offset,
    tooltipClassName,
    Top,
    TopStart,
    TopEnd,
    Bottom,
    BottomStart,
    BottomEnd,
    Left,
    LeftStart,
    LeftEnd,
    Right,
    RightStart,
    RightEnd,
    Smooth,
    Instant,
    None,
    initTour,
    destroyTour,
    startTour,
    nextStep,
    prevStep,
    goToStep,
    skipTour,
    getProgress,
    clearProgress,
    eqPlacement,
    eqScrollBehavior
};
