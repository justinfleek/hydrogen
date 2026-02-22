// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                        // hydrogen // tooltip
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Tooltip component
// |
// | Accessible tooltips with positioning.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Primitive.Tooltip as Tooltip
// |
// | Tooltip.tooltip []
// |   [ Tooltip.tooltipTrigger []
// |       [ Button.button [] [ HH.text "Hover me" ] ]
// |   , Tooltip.tooltipContent [ Tooltip.side Tooltip.Top ]
// |       [ HH.text "Tooltip content" ]
// |   ]
// | ```
import * as Data_Array from "../Data.Array/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Properties_ARIA from "../Halogen.HTML.Properties.ARIA/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                        // side
// ═══════════════════════════════════════════════════════════════════════════════
// | Tooltip side positioning
var Top = /* #__PURE__ */ (function () {
    function Top() {

    };
    Top.value = new Top();
    return Top;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                        // side
// ═══════════════════════════════════════════════════════════════════════════════
// | Tooltip side positioning
var Right = /* #__PURE__ */ (function () {
    function Right() {

    };
    Right.value = new Right();
    return Right;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                        // side
// ═══════════════════════════════════════════════════════════════════════════════
// | Tooltip side positioning
var Bottom = /* #__PURE__ */ (function () {
    function Bottom() {

    };
    Bottom.value = new Bottom();
    return Bottom;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                        // side
// ═══════════════════════════════════════════════════════════════════════════════
// | Tooltip side positioning
var Left = /* #__PURE__ */ (function () {
    function Left() {

    };
    Left.value = new Left();
    return Left;
})();
var sideClasses = function (v) {
    if (v instanceof Top) {
        return "bottom-full left-1/2 -translate-x-1/2 mb-2";
    };
    if (v instanceof Right) {
        return "left-full top-1/2 -translate-y-1/2 ml-2";
    };
    if (v instanceof Bottom) {
        return "top-full left-1/2 -translate-x-1/2 mt-2";
    };
    if (v instanceof Left) {
        return "right-full top-1/2 -translate-y-1/2 mr-2";
    };
    throw new Error("Failed pattern match at Hydrogen.Primitive.Tooltip (line 57, column 15 - line 61, column 53): " + [ v.constructor.name ]);
};

// | Set tooltip side
var side = function (s) {
    return function (props) {
        return {
            open: props.open,
            className: props.className,
            side: s
        };
    };
};

// | Set open state
var open = function (o) {
    return function (props) {
        return {
            side: props.side,
            className: props.className,
            open: o
        };
    };
};
var eqSide = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Top && y instanceof Top) {
                return true;
            };
            if (x instanceof Right && y instanceof Right) {
                return true;
            };
            if (x instanceof Bottom && y instanceof Bottom) {
                return true;
            };
            if (x instanceof Left && y instanceof Left) {
                return true;
            };
            return false;
        };
    }
};
var defaultProps = /* #__PURE__ */ (function () {
    return {
        side: Top.value,
        open: false,
        className: ""
    };
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // components
// ═══════════════════════════════════════════════════════════════════════════════
// | Tooltip container (must wrap trigger and content)
var tooltip = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "relative inline-block group", props.className ]) ])(children);
    };
};

// | Tooltip content (shown on hover)
var tooltipContent = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        var visibilityClass = (function () {
            if (props.open) {
                return "opacity-100 visible";
            };
            return "opacity-0 invisible group-hover:opacity-100 group-hover:visible";
        })();
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "absolute z-50 overflow-hidden rounded-md border bg-popover px-3 py-1.5 text-sm text-popover-foreground shadow-md transition-opacity duration-150", sideClasses(props.side), visibilityClass, props.className ]), Halogen_HTML_Properties_ARIA.role("tooltip") ])(children);
    };
};

// | Tooltip trigger (the element that shows tooltip on hover)
var tooltipTrigger = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ props.className ]) ])(children);
    };
};

// | Add custom class
var className = function (c) {
    return function (props) {
        return {
            side: props.side,
            open: props.open,
            className: props.className + (" " + c)
        };
    };
};
export {
    tooltip,
    tooltipTrigger,
    tooltipContent,
    side,
    open,
    className,
    Top,
    Right,
    Bottom,
    Left,
    eqSide
};
