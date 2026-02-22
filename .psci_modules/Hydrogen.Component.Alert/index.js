// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                          // hydrogen // alert
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Alert component with variants
// |
// | Alert messages for important information.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Component.Alert as Alert
// | import Hydrogen.Icon.Icons as Icon
// |
// | -- Default alert
// | Alert.alert []
// |   [ Alert.alertTitle [] [ HH.text "Heads up!" ]
// |   , Alert.alertDescription [] [ HH.text "You can add components here." ]
// |   ]
// |
// | -- Destructive alert
// | Alert.alert [ Alert.variant Alert.Destructive ]
// |   [ Icon.alertCircle []
// |   , Alert.alertTitle [] [ HH.text "Error" ]
// |   , Alert.alertDescription [] [ HH.text "Something went wrong." ]
// |   ]
// | ```
import * as Data_Array from "../Data.Array/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Properties_ARIA from "../Halogen.HTML.Properties.ARIA/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // variants
// ═══════════════════════════════════════════════════════════════════════════════
// | Alert variants
var Default = /* #__PURE__ */ (function () {
    function Default() {

    };
    Default.value = new Default();
    return Default;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // variants
// ═══════════════════════════════════════════════════════════════════════════════
// | Alert variants
var Destructive = /* #__PURE__ */ (function () {
    function Destructive() {

    };
    Destructive.value = new Destructive();
    return Destructive;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // variants
// ═══════════════════════════════════════════════════════════════════════════════
// | Alert variants
var Success = /* #__PURE__ */ (function () {
    function Success() {

    };
    Success.value = new Success();
    return Success;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // variants
// ═══════════════════════════════════════════════════════════════════════════════
// | Alert variants
var Warning = /* #__PURE__ */ (function () {
    function Warning() {

    };
    Warning.value = new Warning();
    return Warning;
})();

// | Get variant classes
var variantClasses = function (v) {
    if (v instanceof Default) {
        return "bg-background text-foreground";
    };
    if (v instanceof Destructive) {
        return "border-destructive/50 text-destructive dark:border-destructive [&>svg]:text-destructive";
    };
    if (v instanceof Success) {
        return "border-green-500/50 text-green-700 dark:text-green-400 [&>svg]:text-green-500";
    };
    if (v instanceof Warning) {
        return "border-yellow-500/50 text-yellow-700 dark:text-yellow-400 [&>svg]:text-yellow-500";
    };
    throw new Error("Failed pattern match at Hydrogen.Component.Alert (line 64, column 18 - line 72, column 88): " + [ v.constructor.name ]);
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
var eqAlertVariant = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Default && y instanceof Default) {
                return true;
            };
            if (x instanceof Destructive && y instanceof Destructive) {
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
//                                                                  // components
// ═══════════════════════════════════════════════════════════════════════════════
// | Base alert classes
var baseClasses = "relative w-full rounded-lg border p-4 [&>svg~*]:pl-7 [&>svg+div]:translate-y-[-3px] [&>svg]:absolute [&>svg]:left-4 [&>svg]:top-4 [&>svg]:text-foreground";

// | Alert title
var alertTitle = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.h5([ Hydrogen_UI_Core.cls([ "mb-1 font-medium leading-none tracking-tight", props.className ]) ])(children);
    };
};

// | Alert description
var alertDescription = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "text-sm [&_p]:leading-relaxed", props.className ]) ])(children);
    };
};

// | Render an alert
var alert = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ baseClasses, variantClasses(props.variant), props.className ]), Halogen_HTML_Properties_ARIA.role("alert") ])(children);
    };
};
export {
    alert,
    alertTitle,
    alertDescription,
    variant,
    className,
    Default,
    Destructive,
    Success,
    Warning,
    eqAlertVariant
};
