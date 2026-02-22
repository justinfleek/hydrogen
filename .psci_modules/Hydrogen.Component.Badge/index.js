// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                          // hydrogen // badge
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Badge component with variants
// |
// | Small status badges inspired by shadcn/ui.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Component.Badge as Badge
// |
// | -- Default badge
// | Badge.badge [] [ HH.text "New" ]
// |
// | -- With variant
// | Badge.badge [ Badge.variant Badge.Success ] [ HH.text "Active" ]
// |
// | -- Outline style
// | Badge.badge [ Badge.variant Badge.Outline ] [ HH.text "Draft" ]
// | ```
import * as Data_Array from "../Data.Array/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // variants
// ═══════════════════════════════════════════════════════════════════════════════
// | Badge variants
var Default = /* #__PURE__ */ (function () {
    function Default() {

    };
    Default.value = new Default();
    return Default;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // variants
// ═══════════════════════════════════════════════════════════════════════════════
// | Badge variants
var Secondary = /* #__PURE__ */ (function () {
    function Secondary() {

    };
    Secondary.value = new Secondary();
    return Secondary;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // variants
// ═══════════════════════════════════════════════════════════════════════════════
// | Badge variants
var Destructive = /* #__PURE__ */ (function () {
    function Destructive() {

    };
    Destructive.value = new Destructive();
    return Destructive;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // variants
// ═══════════════════════════════════════════════════════════════════════════════
// | Badge variants
var Outline = /* #__PURE__ */ (function () {
    function Outline() {

    };
    Outline.value = new Outline();
    return Outline;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // variants
// ═══════════════════════════════════════════════════════════════════════════════
// | Badge variants
var Success = /* #__PURE__ */ (function () {
    function Success() {

    };
    Success.value = new Success();
    return Success;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // variants
// ═══════════════════════════════════════════════════════════════════════════════
// | Badge variants
var Warning = /* #__PURE__ */ (function () {
    function Warning() {

    };
    Warning.value = new Warning();
    return Warning;
})();

// | Get variant classes
var variantClasses = function (v) {
    if (v instanceof Default) {
        return "border-transparent bg-primary text-primary-foreground hover:bg-primary/80";
    };
    if (v instanceof Secondary) {
        return "border-transparent bg-secondary text-secondary-foreground hover:bg-secondary/80";
    };
    if (v instanceof Destructive) {
        return "border-transparent bg-destructive text-destructive-foreground hover:bg-destructive/80";
    };
    if (v instanceof Outline) {
        return "text-foreground";
    };
    if (v instanceof Success) {
        return "border-transparent bg-green-500 text-white hover:bg-green-600";
    };
    if (v instanceof Warning) {
        return "border-transparent bg-yellow-500 text-white hover:bg-yellow-600";
    };
    throw new Error("Failed pattern match at Hydrogen.Component.Badge (line 58, column 18 - line 70, column 70): " + [ v.constructor.name ]);
};

// | Set variant
var variant = function (v) {
    return function (props) {
        return {
            className: props.className,
            variant: v
        };
    };
};
var eqBadgeVariant = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Default && y instanceof Default) {
                return true;
            };
            if (x instanceof Secondary && y instanceof Secondary) {
                return true;
            };
            if (x instanceof Destructive && y instanceof Destructive) {
                return true;
            };
            if (x instanceof Outline && y instanceof Outline) {
                return true;
            };
            if (x instanceof Success && y instanceof Success) {
                return true;
            };
            if (x instanceof Warning && y instanceof Warning) {
                return true;
            };
            return false;
        };
    }
};
var defaultProps = /* #__PURE__ */ (function () {
    return {
        variant: Default.value,
        className: ""
    };
})();

// | Add custom class
var className = function (c) {
    return function (props) {
        return {
            variant: props.variant,
            className: props.className + (" " + c)
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // component
// ═══════════════════════════════════════════════════════════════════════════════
// | Base badge classes
var baseClasses = "inline-flex items-center rounded-full border px-2.5 py-0.5 text-xs font-semibold transition-colors focus:outline-none focus:ring-2 focus:ring-ring focus:ring-offset-2";

// | Render a badge
var badge = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ baseClasses, variantClasses(props.variant), props.className ]) ])(children);
    };
};
export {
    badge,
    variant,
    className,
    Default,
    Secondary,
    Destructive,
    Outline,
    Success,
    Warning,
    eqBadgeVariant
};
