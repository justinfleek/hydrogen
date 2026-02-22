// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                // hydrogen // layout-animation
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Automatic layout animations using FLIP technique
// |
// | Smoothly animate layout changes including position, size, and 
// | shared element transitions between components.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Motion.LayoutAnimation as LA
// |
// | -- Auto-animate layout changes
// | LA.layoutRoot
// |   { duration: Milliseconds 300.0
// |   , easing: "ease-out"
// |   }
// |   [ LA.layoutItem { id: "card-1" } cardContent
// |   , LA.layoutItem { id: "card-2" } cardContent
// |   ]
// |
// | -- Shared layout animations (hero transitions)
// | -- In list view:
// | LA.sharedElement { id: "product-" <> productId }
// |   [ productThumbnail ]
// |
// | -- In detail view:
// | LA.sharedElement { id: "product-" <> productId }
// |   [ productFullImage ]
// |
// | -- Layout groups for independent animations
// | LA.layoutGroup "sidebar"
// |   [ LA.layoutItem { id: "nav-1" } navItem1
// |   , LA.layoutItem { id: "nav-2" } navItem2
// |   ]
// |
// | -- Crossfade between elements
// | LA.crossfade currentView
// |   [ Tuple "list" listView
// |   , Tuple "grid" gridView
// |   ]
// | ```
import * as $foreign from "./foreign.js";
import * as Control_Applicative from "../Control.Applicative/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
import * as Effect from "../Effect/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Properties from "../Halogen.HTML.Properties/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);
var show1 = /* #__PURE__ */ Data_Show.show(Data_Show.showNumber);
var show2 = /* #__PURE__ */ Data_Show.show(Data_Show.showBoolean);
var pure = /* #__PURE__ */ Control_Applicative.pure(Effect.applicativeEffect);
var map = /* #__PURE__ */ Data_Functor.map(Data_Functor.functorArray);

// | Shared element wrapper for hero transitions
var sharedElement = function (config) {
    return function (children) {
        return Halogen_HTML_Elements.div([ Halogen_HTML_Properties.attr("data-shared-element")(config.id), Halogen_HTML_Properties.attr("data-shared-transition")(config.transition), Halogen_HTML_Properties.attr("data-shared-zindex")(show(config.zIndex)) ])(children);
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // layout callbacks
// ═══════════════════════════════════════════════════════════════════════════════
// | Set layout animation start callback
var onLayoutAnimationStart = function (v) {
    return Halogen_HTML_Properties.attr("data-layout-on-start")("true");
};

// | Set layout animation complete callback
var onLayoutAnimationComplete = function (v) {
    return Halogen_HTML_Properties.attr("data-layout-on-complete")("true");
};

// | Layout root container
var layoutRoot = function (config) {
    return function (children) {
        var unwrapMs = function (v) {
            return v;
        };
        var staggerAttr = function (v) {
            if (v instanceof Data_Maybe.Just) {
                return Halogen_HTML_Properties.attr("data-layout-stagger")(show1(v.value0));
            };
            if (v instanceof Data_Maybe.Nothing) {
                return Halogen_HTML_Properties.attr("data-layout-stagger")("");
            };
            throw new Error("Failed pattern match at Hydrogen.Motion.LayoutAnimation (line 146, column 3 - line 146, column 95): " + [ v.constructor.name ]);
        };
        return Halogen_HTML_Elements.div([ Halogen_HTML_Properties.attr("data-layout-root")("true"), Halogen_HTML_Properties.attr("data-layout-duration")(show1(unwrapMs(config.duration))), Halogen_HTML_Properties.attr("data-layout-easing")(config.easing), staggerAttr(config.stagger) ])(children);
    };
};

// | Layout item wrapper
var layoutItem = function (config) {
    return function (children) {
        return Halogen_HTML_Elements.div([ Halogen_HTML_Properties.attr("data-layout-item")(config.id), Halogen_HTML_Properties.attr("data-animate-position")(show2(config.animatePosition)), Halogen_HTML_Properties.attr("data-animate-size")(show2(config.animateSize)), Halogen_HTML_Properties.attr("data-animate-opacity")(show2(config.animateOpacity)) ])(children);
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // layout groups
// ═══════════════════════════════════════════════════════════════════════════════
// | Group items for independent layout animations
var layoutGroup = function (name) {
    return function (children) {
        return Halogen_HTML_Elements.div([ Halogen_HTML_Properties.attr("data-layout-group")(name) ])(children);
    };
};
var flipAnimate = function (element) {
    return function (first) {
        return function (last) {
            return function (config) {
                var unwrapMs = function (v) {
                    return v;
                };
                return function __do() {
                    config.onStart();
                    return $foreign.flipAnimateImpl(element)(first)(last)({
                        duration: unwrapMs(config.duration),
                        easing: config.easing
                    })();
                };
            };
        };
    };
};

// | Default shared element configuration
var defaultSharedConfig = {
    id: "",
    transition: "morph",
    zIndex: 1000
};

// | Default layout configuration
var defaultLayoutConfig = /* #__PURE__ */ (function () {
    return {
        duration: 300.0,
        easing: "ease-out",
        stagger: Data_Maybe.Nothing.value,
        onStart: pure(Data_Unit.unit),
        onComplete: pure(Data_Unit.unit)
    };
})();

// | Default item configuration
var defaultItemConfig = {
    id: "",
    animatePosition: true,
    animateSize: true,
    animateOpacity: false
};

// | Default FLIP configuration
var defaultFlipConfig = {
    duration: 300.0,
    easing: "ease-out",
    onStart: /* #__PURE__ */ pure(Data_Unit.unit),
    onComplete: /* #__PURE__ */ pure(Data_Unit.unit)
};

// | Crossfade with explicit key
var crossfadeWithKey = function (config) {
    return function (views) {
        var unwrapMs = function (v) {
            return v;
        };
        var renderView = function (v) {
            return Halogen_HTML_Elements.div([ Halogen_HTML_Properties.attr("data-crossfade-key")(v.value0) ])([ v.value1 ]);
        };
        return Halogen_HTML_Elements.div([ Halogen_HTML_Properties.attr("data-crossfade")("true"), Halogen_HTML_Properties.attr("data-crossfade-current")(config.current), Halogen_HTML_Properties.attr("data-crossfade-duration")(show1(unwrapMs(config.duration))) ])(map(renderView)(views));
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // crossfade
// ═══════════════════════════════════════════════════════════════════════════════
// | Crossfade between different views
var crossfade = function (current) {
    return function (views) {
        var renderView = function (v) {
            return Halogen_HTML_Elements.div([ Halogen_HTML_Properties.attr("data-crossfade-key")(v.value0), Halogen_HTML_Properties.style((function () {
                var $26 = v.value0 === current;
                if ($26) {
                    return "";
                };
                return "display: none";
            })()) ])([ v.value1 ]);
        };
        return Halogen_HTML_Elements.div([ Halogen_HTML_Properties.attr("data-crossfade")("true"), Halogen_HTML_Properties.attr("data-crossfade-current")(current) ])(map(renderView)(views));
    };
};
var createLayoutController = function (element) {
    return function (config) {
        var unwrapMs = function (v) {
            return v;
        };
        return $foreign.createLayoutControllerImpl(element)({
            duration: unwrapMs(config.duration),
            easing: config.easing
        });
    };
};
export {
    measureElement,
    animateLayout,
    forceLayout,
    pauseLayout,
    resumeLayout
} from "./foreign.js";
export {
    layoutRoot,
    defaultLayoutConfig,
    layoutItem,
    defaultItemConfig,
    layoutGroup,
    sharedElement,
    defaultSharedConfig,
    crossfade,
    crossfadeWithKey,
    flipAnimate,
    defaultFlipConfig,
    onLayoutAnimationStart,
    onLayoutAnimationComplete,
    createLayoutController
};
