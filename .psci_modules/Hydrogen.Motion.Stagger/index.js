// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                        // hydrogen // stagger
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Staggered animations for lists and groups
// |
// | Create cascading animation effects by staggering the animation
// | of child elements with configurable delays and directions.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Motion.Stagger as S
// |
// | -- Stagger a list of elements
// | S.staggerElements container
// |   { delayPerItem: Milliseconds 50.0
// |   , direction: S.Forward
// |   , animation: "opacity-0 -> opacity-100 transition-opacity"
// |   }
// |
// | -- Center-out stagger (middle items first)
// | S.staggerElements container
// |   { delayPerItem: Milliseconds 30.0
// |   , direction: S.CenterOut
// |   , animation: "scale-0 -> scale-100 transition-transform"
// |   }
// |
// | -- Custom stagger function
// | S.staggerWithFunction container
// |   { staggerFn: \index total -> Milliseconds (index * index * 10.0)
// |   , animation: "translate-y-4 opacity-0 -> translate-y-0 opacity-100"
// |   }
// |
// | -- Halogen component
// | S.staggerContainer [ S.direction S.Reverse, S.delay (Milliseconds 75.0) ]
// |   [ S.staggerItem [] [ HH.text "First" ]
// |   , S.staggerItem [] [ HH.text "Second" ]
// |   , S.staggerItem [] [ HH.text "Third" ]
// |   ]
// | ```
import * as $foreign from "./foreign.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Properties from "../Halogen.HTML.Properties/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showNumber);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Direction of stagger animation
var Forward = /* #__PURE__ */ (function () {
    function Forward() {

    };
    Forward.value = new Forward();
    return Forward;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Direction of stagger animation
var Reverse = /* #__PURE__ */ (function () {
    function Reverse() {

    };
    Reverse.value = new Reverse();
    return Reverse;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Direction of stagger animation
var CenterOut = /* #__PURE__ */ (function () {
    function CenterOut() {

    };
    CenterOut.value = new CenterOut();
    return CenterOut;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Direction of stagger animation
var EdgesIn = /* #__PURE__ */ (function () {
    function EdgesIn() {

    };
    EdgesIn.value = new EdgesIn();
    return EdgesIn;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Direction of stagger animation
var Random = /* #__PURE__ */ (function () {
    function Random() {

    };
    Random.value = new Random();
    return Random;
})();

// Helper functions
var toNumber = function (n) {
    var $24 = n <= 0;
    if ($24) {
        return 0.0;
    };
    return toNumber(n - 1 | 0) + 1.0;
};
var staggerWithFunction = function (element) {
    return function (config) {
        var unwrapMs = function (v) {
            return v;
        };
        return $foreign.staggerWithFunctionImpl(element)({
            staggerFn: function (i) {
                return function (t) {
                    return unwrapMs(config.staggerFn(i)(t));
                };
            },
            animation: config.animation,
            selector: "> *"
        });
    };
};

// | Stagger item (child of stagger container)
var staggerItem = function (children) {
    return Halogen_HTML_Elements.div([ Halogen_HTML_Properties.attr("data-stagger-item")("true") ])(children);
};

// | Group multiple items for synchronized stagger
var staggerGroup = function (groupName) {
    return function (children) {
        return Halogen_HTML_Elements.div([ Halogen_HTML_Properties.attr("data-stagger-group")(groupName) ])(children);
    };
};
var staggerElements = function (element) {
    return function (config) {
        var unwrapMs = function (v) {
            return v;
        };
        var directionToString = function (v) {
            if (v instanceof Forward) {
                return "forward";
            };
            if (v instanceof Reverse) {
                return "reverse";
            };
            if (v instanceof CenterOut) {
                return "center-out";
            };
            if (v instanceof EdgesIn) {
                return "edges-in";
            };
            if (v instanceof Random) {
                return "random";
            };
            throw new Error("Failed pattern match at Hydrogen.Motion.Stagger (line 155, column 3 - line 155, column 40): " + [ v.constructor.name ]);
        };
        return $foreign.staggerElementsImpl(element)({
            delayPerItem: unwrapMs(config.delayPerItem),
            direction: directionToString(config.direction),
            initialDelay: unwrapMs(config.initialDelay),
            animation: config.animation,
            selector: config.selector
        });
    };
};

// | Set delay between each item
var staggerDelay = function (v) {
    return Halogen_HTML_Properties.attr("data-stagger-delay")(show(v));
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                             // declarative api
// ═══════════════════════════════════════════════════════════════════════════════
// | Stagger container with configuration via data attributes
var staggerContainer = function (children) {
    return Halogen_HTML_Elements.div([ Halogen_HTML_Properties.attr("data-stagger-container")("true") ])(children);
};
var showStaggerDirection = {
    show: function (v) {
        if (v instanceof Forward) {
            return "Forward";
        };
        if (v instanceof Reverse) {
            return "Reverse";
        };
        if (v instanceof CenterOut) {
            return "CenterOut";
        };
        if (v instanceof EdgesIn) {
            return "EdgesIn";
        };
        if (v instanceof Random) {
            return "Random";
        };
        throw new Error("Failed pattern match at Hydrogen.Motion.Stagger (line 97, column 1 - line 102, column 25): " + [ v.constructor.name ]);
    }
};
var show1 = /* #__PURE__ */ Data_Show.show(showStaggerDirection);

// | Random stagger (random delay within range)
var randomStagger = function (v) {
    return function (v1) {
        return function (index) {
            return function (v2) {
                var pseudo = $foreign.sin(toNumber(index) * 12.9898) * 43758.5453;
                var random = pseudo - $foreign.floor(pseudo);
                return v + random * (v1 - v);
            };
        };
    };
};
var max = function (a) {
    return function (b) {
        var $32 = a > b;
        if ($32) {
            return a;
        };
        return b;
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                           // stagger functions
// ═══════════════════════════════════════════════════════════════════════════════
// | Linear stagger (constant delay between items)
var linearStagger = function (v) {
    return function (index) {
        return function (v1) {
            return toNumber(index) * v;
        };
    };
};

// | Set initial delay before first item
var initialDelay = function (v) {
    return Halogen_HTML_Properties.attr("data-stagger-initial-delay")(show(v));
};
var eqStaggerDirection = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Forward && y instanceof Forward) {
                return true;
            };
            if (x instanceof Reverse && y instanceof Reverse) {
                return true;
            };
            if (x instanceof CenterOut && y instanceof CenterOut) {
                return true;
            };
            if (x instanceof EdgesIn && y instanceof EdgesIn) {
                return true;
            };
            if (x instanceof Random && y instanceof Random) {
                return true;
            };
            return false;
        };
    }
};

// | Ease-out stagger (fast start, slow end)
var easeOutStagger = function (v) {
    return function (index) {
        return function (total) {
            var t = toNumber(index) / toNumber(max(1)(total - 1 | 0));
            var eased = 1.0 - (1.0 - t) * (1.0 - t);
            return eased * v * toNumber(total);
        };
    };
};

// | Ease-in stagger (slow start, fast end)
var easeInStagger = function (v) {
    return function (index) {
        return function (total) {
            var t = toNumber(index) / toNumber(max(1)(total - 1 | 0));
            var eased = t * t;
            return eased * v * toNumber(total);
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // stagger properties
// ═══════════════════════════════════════════════════════════════════════════════
// | Set stagger direction
var direction = function (dir) {
    return Halogen_HTML_Properties.attr("data-stagger-direction")(show1(dir));
};

// | Set delay per item (alias for staggerDelay)
var delay = staggerDelay;

// | Default stagger configuration
var defaultStaggerConfig = /* #__PURE__ */ (function () {
    return {
        delayPerItem: 50.0,
        direction: Forward.value,
        initialDelay: 0.0,
        animation: "opacity-0 -> opacity-100 transition-opacity duration-300",
        selector: "> *"
    };
})();

// | Set animation classes
var animation = function (anim) {
    return Halogen_HTML_Properties.attr("data-stagger-animation")(anim);
};
export {
    resetStagger,
    playStagger,
    reverseStagger
} from "./foreign.js";
export {
    Forward,
    Reverse,
    CenterOut,
    EdgesIn,
    Random,
    defaultStaggerConfig,
    staggerElements,
    staggerWithFunction,
    staggerContainer,
    staggerItem,
    staggerGroup,
    direction,
    delay,
    staggerDelay,
    initialDelay,
    animation,
    linearStagger,
    easeInStagger,
    easeOutStagger,
    randomStagger,
    eqStaggerDirection,
    showStaggerDirection
};
