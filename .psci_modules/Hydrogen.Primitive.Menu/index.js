// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                           // hydrogen // menu
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Dropdown Menu component
// |
// | Accessible dropdown menus with keyboard navigation.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Primitive.Menu as Menu
// |
// | Menu.menu [ Menu.open state.isOpen ]
// |   [ Menu.menuTrigger [ Menu.onToggle ToggleMenu ]
// |       [ Button.button [] [ HH.text "Menu" ] ]
// |   , Menu.menuContent []
// |       [ Menu.menuItem [ Menu.onSelect SelectEdit ] [ HH.text "Edit" ]
// |       , Menu.menuItem [ Menu.onSelect SelectDelete ] [ HH.text "Delete" ]
// |       , Menu.menuSeparator []
// |       , Menu.menuItem [ Menu.disabled true ] [ HH.text "Disabled" ]
// |       ]
// |   ]
// | ```
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Semigroup from "../Data.Semigroup/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Events from "../Halogen.HTML.Events/index.js";
import * as Halogen_HTML_Properties from "../Halogen.HTML.Properties/index.js";
import * as Halogen_HTML_Properties_ARIA from "../Halogen.HTML.Properties.ARIA/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";
var append = /* #__PURE__ */ Data_Semigroup.append(Data_Semigroup.semigroupArray);

// | Set open state
var open = function (o) {
    return function (props) {
        return {
            disabled: props.disabled,
            onToggle: props.onToggle,
            onSelect: props.onSelect,
            className: props.className,
            open: o
        };
    };
};

// | Set toggle handler
var onToggle = function (handler) {
    return function (props) {
        return {
            open: props.open,
            disabled: props.disabled,
            onSelect: props.onSelect,
            className: props.className,
            onToggle: new Data_Maybe.Just(handler)
        };
    };
};

// | Set select handler
var onSelect = function (handler) {
    return function (props) {
        return {
            open: props.open,
            disabled: props.disabled,
            onToggle: props.onToggle,
            className: props.className,
            onSelect: new Data_Maybe.Just(handler)
        };
    };
};

// | Set disabled state
var disabled = function (d) {
    return function (props) {
        return {
            open: props.open,
            onToggle: props.onToggle,
            onSelect: props.onSelect,
            className: props.className,
            disabled: d
        };
    };
};
var defaultProps = /* #__PURE__ */ (function () {
    return {
        open: false,
        disabled: false,
        onToggle: Data_Maybe.Nothing.value,
        onSelect: Data_Maybe.Nothing.value,
        className: ""
    };
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // components
// ═══════════════════════════════════════════════════════════════════════════════
// | Menu container
var menu = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "relative inline-block text-left", props.className ]) ])(children);
    };
};

// | Menu content panel
var menuContent = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        var visibilityClass = (function () {
            if (props.open) {
                return "";
            };
            return "hidden";
        })();
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "absolute right-0 z-50 mt-2 min-w-[8rem] overflow-hidden rounded-md border bg-popover p-1 text-popover-foreground shadow-md animate-in fade-in-0 zoom-in-95", visibilityClass, props.className ]), Halogen_HTML_Properties_ARIA.role("menu") ])(children);
    };
};

// | Menu group (for grouping items)
var menuGroup = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ props.className ]), Halogen_HTML_Properties_ARIA.role("group") ])(children);
    };
};

// | Menu item
var menuItem = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        var disabledClasses = (function () {
            if (props.disabled) {
                return "opacity-50 pointer-events-none";
            };
            return "cursor-pointer";
        })();
        return Halogen_HTML_Elements.div(append([ Hydrogen_UI_Core.cls([ "relative flex select-none items-center rounded-sm px-2 py-1.5 text-sm outline-none transition-colors focus:bg-accent focus:text-accent-foreground hover:bg-accent hover:text-accent-foreground", disabledClasses, props.className ]), Halogen_HTML_Properties_ARIA.role("menuitem"), Halogen_HTML_Properties.attr("data-disabled")((function () {
            if (props.disabled) {
                return "true";
            };
            return "false";
        })()) ])((function () {
            if (props.onSelect instanceof Data_Maybe.Just && !props.disabled) {
                return [ Halogen_HTML_Events.onClick(props.onSelect.value0) ];
            };
            return [  ];
        })()))(children);
    };
};

// | Menu label (non-interactive heading)
var menuLabel = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "px-2 py-1.5 text-sm font-semibold", props.className ]) ])(children);
    };
};

// | Menu separator
var menuSeparator = function (propMods) {
    var props = Data_Array.foldl(function (p) {
        return function (f) {
            return f(p);
        };
    })(defaultProps)(propMods);
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "-mx-1 my-1 h-px bg-muted", props.className ]), Halogen_HTML_Properties_ARIA.role("separator") ])([  ]);
};

// | Menu trigger
var menuTrigger = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.div(append([ Hydrogen_UI_Core.cls([ props.className ]), Halogen_HTML_Properties_ARIA.hasPopup("menu"), Halogen_HTML_Properties_ARIA.expanded((function () {
            if (props.open) {
                return "true";
            };
            return "false";
        })()) ])((function () {
            if (props.onToggle instanceof Data_Maybe.Just) {
                return [ Halogen_HTML_Events.onClick(props.onToggle.value0) ];
            };
            if (props.onToggle instanceof Data_Maybe.Nothing) {
                return [  ];
            };
            throw new Error("Failed pattern match at Hydrogen.Primitive.Menu (line 118, column 12 - line 120, column 22): " + [ props.onToggle.constructor.name ]);
        })()))(children);
    };
};

// | Add custom class
var className = function (c) {
    return function (props) {
        return {
            open: props.open,
            disabled: props.disabled,
            onToggle: props.onToggle,
            onSelect: props.onSelect,
            className: props.className + (" " + c)
        };
    };
};
export {
    menu,
    menuTrigger,
    menuContent,
    menuItem,
    menuSeparator,
    menuLabel,
    menuGroup,
    open,
    disabled,
    onToggle,
    onSelect,
    className
};
