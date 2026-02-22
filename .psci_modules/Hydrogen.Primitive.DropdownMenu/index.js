// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                   // hydrogen // dropdownmenu
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Cascading Dropdown Menu component
// |
// | Accessible dropdown menus with submenus, checkboxes, radio items,
// | and keyboard navigation. Follows the ARIA menu pattern.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Primitive.DropdownMenu as DropdownMenu
// |
// | DropdownMenu.dropdownMenu [ DropdownMenu.open state.isOpen ]
// |   [ DropdownMenu.dropdownMenuTrigger [ DropdownMenu.onToggle ToggleMenu ]
// |       [ Button.button [] [ HH.text "Options" ] ]
// |   , DropdownMenu.dropdownMenuContent []
// |       [ DropdownMenu.dropdownMenuLabel [] [ HH.text "My Account" ]
// |       , DropdownMenu.dropdownMenuSeparator []
// |       , DropdownMenu.dropdownMenuItem
// |           [ DropdownMenu.onSelect HandleProfile
// |           , DropdownMenu.icon userIcon
// |           , DropdownMenu.shortcut "⌘P"
// |           ]
// |           [ HH.text "Profile" ]
// |       , DropdownMenu.dropdownMenuItem
// |           [ DropdownMenu.onSelect HandleSettings
// |           , DropdownMenu.shortcut "⌘,"
// |           ]
// |           [ HH.text "Settings" ]
// |       , DropdownMenu.dropdownMenuSeparator []
// |       , DropdownMenu.dropdownMenuCheckboxItem
// |           [ DropdownMenu.checked state.showToolbar
// |           , DropdownMenu.onCheckedChange ToggleToolbar
// |           ]
// |           [ HH.text "Show Toolbar" ]
// |       , DropdownMenu.dropdownMenuSeparator []
// |       , DropdownMenu.dropdownMenuSub []
// |           [ DropdownMenu.dropdownMenuSubTrigger []
// |               [ HH.text "More Options →" ]
// |           , DropdownMenu.dropdownMenuSubContent []
// |               [ DropdownMenu.dropdownMenuItem [] [ HH.text "Option 1" ]
// |               , DropdownMenu.dropdownMenuItem [] [ HH.text "Option 2" ]
// |               ]
// |           ]
// |       ]
// |   ]
// | ```
// |
// | ## Radio Groups
// |
// | ```purescript
// | DropdownMenu.dropdownMenuRadioGroup [ DropdownMenu.value state.theme ]
// |   [ DropdownMenu.dropdownMenuRadioItem [ DropdownMenu.value "light" ]
// |       [ HH.text "Light" ]
// |   , DropdownMenu.dropdownMenuRadioItem [ DropdownMenu.value "dark" ]
// |       [ HH.text "Dark" ]
// |   , DropdownMenu.dropdownMenuRadioItem [ DropdownMenu.value "system" ]
// |       [ HH.text "System" ]
// |   ]
// | ```
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Semigroup from "../Data.Semigroup/index.js";
import * as Halogen_HTML_Core from "../Halogen.HTML.Core/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Events from "../Halogen.HTML.Events/index.js";
import * as Halogen_HTML_Properties from "../Halogen.HTML.Properties/index.js";
import * as Halogen_HTML_Properties_ARIA from "../Halogen.HTML.Properties.ARIA/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";
var append1 = /* #__PURE__ */ Data_Semigroup.append(Data_Semigroup.semigroupArray);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // positioning
// ═══════════════════════════════════════════════════════════════════════════════
// | Menu side positioning relative to trigger
var Top = /* #__PURE__ */ (function () {
    function Top() {

    };
    Top.value = new Top();
    return Top;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // positioning
// ═══════════════════════════════════════════════════════════════════════════════
// | Menu side positioning relative to trigger
var Right = /* #__PURE__ */ (function () {
    function Right() {

    };
    Right.value = new Right();
    return Right;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // positioning
// ═══════════════════════════════════════════════════════════════════════════════
// | Menu side positioning relative to trigger
var Bottom = /* #__PURE__ */ (function () {
    function Bottom() {

    };
    Bottom.value = new Bottom();
    return Bottom;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // positioning
// ═══════════════════════════════════════════════════════════════════════════════
// | Menu side positioning relative to trigger
var Left = /* #__PURE__ */ (function () {
    function Left() {

    };
    Left.value = new Left();
    return Left;
})();

// | Menu alignment relative to trigger
var Start = /* #__PURE__ */ (function () {
    function Start() {

    };
    Start.value = new Start();
    return Start;
})();

// | Menu alignment relative to trigger
var Center = /* #__PURE__ */ (function () {
    function Center() {

    };
    Center.value = new Center();
    return Center;
})();

// | Menu alignment relative to trigger
var End = /* #__PURE__ */ (function () {
    function End() {

    };
    End.value = new End();
    return End;
})();

// | Set value (for radio items)
var value = function (v) {
    return function (props) {
        return {
            open: props.open,
            disabled: props.disabled,
            checked: props.checked,
            side: props.side,
            align: props.align,
            onToggle: props.onToggle,
            onSelect: props.onSelect,
            onCheckedChange: props.onCheckedChange,
            onValueChange: props.onValueChange,
            shortcut: props.shortcut,
            className: props.className,
            value: v
        };
    };
};

// | Set menu side positioning
var side = function (s) {
    return function (props) {
        return {
            open: props.open,
            disabled: props.disabled,
            checked: props.checked,
            value: props.value,
            align: props.align,
            onToggle: props.onToggle,
            onSelect: props.onSelect,
            onCheckedChange: props.onCheckedChange,
            onValueChange: props.onValueChange,
            shortcut: props.shortcut,
            className: props.className,
            side: s
        };
    };
};

// | Set keyboard shortcut
var shortcut = function (s) {
    return function (props) {
        return {
            open: props.open,
            disabled: props.disabled,
            checked: props.checked,
            value: props.value,
            side: props.side,
            align: props.align,
            onToggle: props.onToggle,
            onSelect: props.onSelect,
            onCheckedChange: props.onCheckedChange,
            onValueChange: props.onValueChange,
            className: props.className,
            shortcut: s
        };
    };
};

// | Radio dot icon for radio items
var radioIcon = /* #__PURE__ */ Halogen_HTML_Elements.elementNS("http://www.w3.org/2000/svg")("svg")([ /* #__PURE__ */ Halogen_HTML_Properties.attr("class")("h-2 w-2 fill-current"), /* #__PURE__ */ Halogen_HTML_Properties.attr("viewBox")("0 0 24 24") ])([ /* #__PURE__ */ Halogen_HTML_Elements.elementNS("http://www.w3.org/2000/svg")("circle")([ /* #__PURE__ */ Halogen_HTML_Properties.attr("cx")("12"), /* #__PURE__ */ Halogen_HTML_Properties.attr("cy")("12"), /* #__PURE__ */ Halogen_HTML_Properties.attr("r")("12") ])([  ]) ]);

// | Get positioning classes based on side and alignment
var positionClasses = function (side$prime) {
    return function (align$prime) {
        var alignClasses = function (v) {
            if (v instanceof Start) {
                return "left-0";
            };
            if (v instanceof Center) {
                return "left-1/2 -translate-x-1/2";
            };
            if (v instanceof End) {
                return "right-0";
            };
            throw new Error("Failed pattern match at Hydrogen.Primitive.DropdownMenu (line 140, column 18 - line 143, column 21): " + [ v.constructor.name ]);
        };
        if (side$prime instanceof Top) {
            return "bottom-full mb-2 " + alignClasses(align$prime);
        };
        if (side$prime instanceof Right) {
            return "left-full ml-2 top-0";
        };
        if (side$prime instanceof Bottom) {
            return "top-full mt-2 " + alignClasses(align$prime);
        };
        if (side$prime instanceof Left) {
            return "right-full mr-2 top-0";
        };
        throw new Error("Failed pattern match at Hydrogen.Primitive.DropdownMenu (line 133, column 32 - line 137, column 34): " + [ side$prime.constructor.name ]);
    };
};

// | Set open state
var open = function (o) {
    return function (props) {
        return {
            disabled: props.disabled,
            checked: props.checked,
            value: props.value,
            side: props.side,
            align: props.align,
            onToggle: props.onToggle,
            onSelect: props.onSelect,
            onCheckedChange: props.onCheckedChange,
            onValueChange: props.onValueChange,
            shortcut: props.shortcut,
            className: props.className,
            open: o
        };
    };
};

// | Set value change handler (for radio groups)
var onValueChange = function (handler) {
    return function (props) {
        return {
            open: props.open,
            disabled: props.disabled,
            checked: props.checked,
            value: props.value,
            side: props.side,
            align: props.align,
            onToggle: props.onToggle,
            onSelect: props.onSelect,
            onCheckedChange: props.onCheckedChange,
            shortcut: props.shortcut,
            className: props.className,
            onValueChange: new Data_Maybe.Just(handler)
        };
    };
};

// | Set toggle handler
var onToggle = function (handler) {
    return function (props) {
        return {
            open: props.open,
            disabled: props.disabled,
            checked: props.checked,
            value: props.value,
            side: props.side,
            align: props.align,
            onSelect: props.onSelect,
            onCheckedChange: props.onCheckedChange,
            onValueChange: props.onValueChange,
            shortcut: props.shortcut,
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
            checked: props.checked,
            value: props.value,
            side: props.side,
            align: props.align,
            onToggle: props.onToggle,
            onCheckedChange: props.onCheckedChange,
            onValueChange: props.onValueChange,
            shortcut: props.shortcut,
            className: props.className,
            onSelect: new Data_Maybe.Just(handler)
        };
    };
};

// | Set checked change handler
var onCheckedChange = function (handler) {
    return function (props) {
        return {
            open: props.open,
            disabled: props.disabled,
            checked: props.checked,
            value: props.value,
            side: props.side,
            align: props.align,
            onToggle: props.onToggle,
            onSelect: props.onSelect,
            onValueChange: props.onValueChange,
            shortcut: props.shortcut,
            className: props.className,
            onCheckedChange: new Data_Maybe.Just(handler)
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
var eqAlign = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Start && y instanceof Start) {
                return true;
            };
            if (x instanceof Center && y instanceof Center) {
                return true;
            };
            if (x instanceof End && y instanceof End) {
                return true;
            };
            return false;
        };
    }
};

// | Set disabled state
var disabled = function (d) {
    return function (props) {
        return {
            open: props.open,
            checked: props.checked,
            value: props.value,
            side: props.side,
            align: props.align,
            onToggle: props.onToggle,
            onSelect: props.onSelect,
            onCheckedChange: props.onCheckedChange,
            onValueChange: props.onValueChange,
            shortcut: props.shortcut,
            className: props.className,
            disabled: d
        };
    };
};
var defaultProps = /* #__PURE__ */ (function () {
    return {
        open: false,
        disabled: false,
        checked: false,
        value: "",
        side: Bottom.value,
        align: Start.value,
        onToggle: Data_Maybe.Nothing.value,
        onSelect: Data_Maybe.Nothing.value,
        onCheckedChange: Data_Maybe.Nothing.value,
        onValueChange: Data_Maybe.Nothing.value,
        shortcut: "",
        className: ""
    };
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // components
// ═══════════════════════════════════════════════════════════════════════════════
// | Dropdown menu root container
var dropdownMenu = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "relative inline-block text-left", props.className ]) ])(children);
    };
};

// | Dropdown menu content panel
var dropdownMenuContent = function (propMods) {
    return function (children) {
        var sideToString = function (v) {
            if (v instanceof Top) {
                return "top";
            };
            if (v instanceof Right) {
                return "right";
            };
            if (v instanceof Bottom) {
                return "bottom";
            };
            if (v instanceof Left) {
                return "left";
            };
            throw new Error("Failed pattern match at Hydrogen.Primitive.DropdownMenu (line 276, column 18 - line 280, column 19): " + [ v.constructor.name ]);
        };
        var alignToString = function (v) {
            if (v instanceof Start) {
                return "start";
            };
            if (v instanceof Center) {
                return "center";
            };
            if (v instanceof End) {
                return "end";
            };
            throw new Error("Failed pattern match at Hydrogen.Primitive.DropdownMenu (line 283, column 19 - line 286, column 17): " + [ v.constructor.name ]);
        };
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
        var posClass = positionClasses(props.side)(props.align);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "absolute z-50 min-w-[8rem] overflow-hidden rounded-md border bg-popover p-1 text-popover-foreground shadow-md", posClass, visibilityClass, props.className ]), Hydrogen_UI_Core.cls([ "animate-in fade-in-0 zoom-in-95" ]), Halogen_HTML_Properties_ARIA.role("menu"), Halogen_HTML_Properties.attr("data-state")((function () {
            if (props.open) {
                return "open";
            };
            return "closed";
        })()), Halogen_HTML_Properties.attr("data-side")(sideToString(props.side)), Halogen_HTML_Properties.attr("data-align")(alignToString(props.align)) ])(children);
    };
};

// | Dropdown menu group
var dropdownMenuGroup = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ props.className ]), Halogen_HTML_Properties_ARIA.role("group") ])(children);
    };
};

// | Dropdown menu label (non-interactive heading)
var dropdownMenuLabel = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "px-2 py-1.5 text-sm font-semibold", props.className ]) ])(children);
    };
};

// | Dropdown menu radio group
var dropdownMenuRadioGroup = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ props.className ]), Halogen_HTML_Properties_ARIA.role("group"), Halogen_HTML_Properties.attr("data-value")(props.value) ])(children);
    };
};

// | Dropdown menu radio item
var dropdownMenuRadioItem = function (propMods) {
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
        return Halogen_HTML_Elements.div(append1([ Hydrogen_UI_Core.cls([ "relative flex cursor-default select-none items-center rounded-sm py-1.5 pl-8 pr-2 text-sm outline-none transition-colors focus:bg-accent focus:text-accent-foreground hover:bg-accent hover:text-accent-foreground", disabledClasses, props.className ]), Halogen_HTML_Properties_ARIA.role("menuitemradio"), Halogen_HTML_Properties_ARIA.checked((function () {
            if (props.checked) {
                return "true";
            };
            return "false";
        })()), Halogen_HTML_Properties.attr("data-state")((function () {
            if (props.checked) {
                return "checked";
            };
            return "unchecked";
        })()), Halogen_HTML_Properties.attr("data-value")(props.value) ])((function () {
            if (props.onValueChange instanceof Data_Maybe.Just && !props.disabled) {
                return [ Halogen_HTML_Events.onClick(function (v) {
                    return props.onValueChange.value0(props.value);
                }) ];
            };
            return [  ];
        })()))([ Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "absolute left-2 flex h-3.5 w-3.5 items-center justify-center" ]) ])([ (function () {
            if (props.checked) {
                return radioIcon;
            };
            return Halogen_HTML_Core.text("");
        })() ]), Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "flex-1" ]) ])(children) ]);
    };
};

// | Dropdown menu separator
var dropdownMenuSeparator = function (propMods) {
    var props = Data_Array.foldl(function (p) {
        return function (f) {
            return f(p);
        };
    })(defaultProps)(propMods);
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "-mx-1 my-1 h-px bg-muted", props.className ]), Halogen_HTML_Properties_ARIA.role("separator") ])([  ]);
};

// | Keyboard shortcut display
var dropdownMenuShortcut = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "ml-auto text-xs tracking-widest opacity-60", props.className ]) ])(children);
    };
};

// | Dropdown menu item
// | 
// | Children can include icons and labels. Pass icons as the first children.
var dropdownMenuItem = function (propMods) {
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
        return Halogen_HTML_Elements.div(append1([ Hydrogen_UI_Core.cls([ "relative flex cursor-default select-none items-center gap-2 rounded-sm px-2 py-1.5 text-sm outline-none transition-colors focus:bg-accent focus:text-accent-foreground hover:bg-accent hover:text-accent-foreground", disabledClasses, props.className ]), Halogen_HTML_Properties_ARIA.role("menuitem"), Halogen_HTML_Properties.attr("data-disabled")((function () {
            if (props.disabled) {
                return "true";
            };
            return "false";
        })()) ])((function () {
            if (props.onSelect instanceof Data_Maybe.Just && !props.disabled) {
                return [ Halogen_HTML_Events.onClick(props.onSelect.value0) ];
            };
            return [  ];
        })()))(append1([ Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "flex items-center gap-2 flex-1" ]) ])(children) ])((function () {
            var $45 = props.shortcut !== "";
            if ($45) {
                return [ dropdownMenuShortcut([  ])([ Halogen_HTML_Core.text(props.shortcut) ]) ];
            };
            return [  ];
        })()));
    };
};

// | Submenu container
var dropdownMenuSub = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "relative group/submenu", props.className ]) ])(children);
    };
};

// | Submenu content (appears on hover)
var dropdownMenuSubContent = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "absolute left-full top-0 z-50 min-w-[8rem] overflow-hidden rounded-md border bg-popover p-1 text-popover-foreground shadow-lg invisible opacity-0 group-hover/submenu:visible group-hover/submenu:opacity-100 transition-all", props.className ]), Halogen_HTML_Properties_ARIA.role("menu") ])(children);
    };
};

// | Dropdown menu trigger button
var dropdownMenuTrigger = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.div(append1([ Hydrogen_UI_Core.cls([ props.className ]), Halogen_HTML_Properties_ARIA.hasPopup("menu"), Halogen_HTML_Properties_ARIA.expanded((function () {
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
            throw new Error("Failed pattern match at Hydrogen.Primitive.DropdownMenu (line 251, column 12 - line 253, column 22): " + [ props.onToggle.constructor.name ]);
        })()))(children);
    };
};

// | Add custom class
var className = function (c) {
    return function (props) {
        return {
            open: props.open,
            disabled: props.disabled,
            checked: props.checked,
            value: props.value,
            side: props.side,
            align: props.align,
            onToggle: props.onToggle,
            onSelect: props.onSelect,
            onCheckedChange: props.onCheckedChange,
            onValueChange: props.onValueChange,
            shortcut: props.shortcut,
            className: props.className + (" " + c)
        };
    };
};

// | Chevron right icon for submenus
var chevronRightIcon = /* #__PURE__ */ Halogen_HTML_Elements.elementNS("http://www.w3.org/2000/svg")("svg")([ /* #__PURE__ */ Halogen_HTML_Properties.attr("class")("ml-auto h-4 w-4"), /* #__PURE__ */ Halogen_HTML_Properties.attr("viewBox")("0 0 24 24"), /* #__PURE__ */ Halogen_HTML_Properties.attr("fill")("none"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke")("currentColor"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke-width")("2"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke-linecap")("round"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke-linejoin")("round") ])([ /* #__PURE__ */ Halogen_HTML_Elements.elementNS("http://www.w3.org/2000/svg")("polyline")([ /* #__PURE__ */ Halogen_HTML_Properties.attr("points")("9 18 15 12 9 6") ])([  ]) ]);

// | Submenu trigger (hover to open)
var dropdownMenuSubTrigger = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex cursor-default select-none items-center rounded-sm px-2 py-1.5 text-sm outline-none hover:bg-accent focus:bg-accent", props.className ]), Halogen_HTML_Properties_ARIA.hasPopup("menu") ])([ Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "flex-1" ]) ])(children), chevronRightIcon ]);
    };
};

// | Set checked state (for checkbox items)
var checked = function (c) {
    return function (props) {
        return {
            open: props.open,
            disabled: props.disabled,
            value: props.value,
            side: props.side,
            align: props.align,
            onToggle: props.onToggle,
            onSelect: props.onSelect,
            onCheckedChange: props.onCheckedChange,
            onValueChange: props.onValueChange,
            shortcut: props.shortcut,
            className: props.className,
            checked: c
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // icons
// ═══════════════════════════════════════════════════════════════════════════════
// | Check icon for checkbox items
var checkIcon = /* #__PURE__ */ Halogen_HTML_Elements.elementNS("http://www.w3.org/2000/svg")("svg")([ /* #__PURE__ */ Halogen_HTML_Properties.attr("class")("h-4 w-4"), /* #__PURE__ */ Halogen_HTML_Properties.attr("viewBox")("0 0 24 24"), /* #__PURE__ */ Halogen_HTML_Properties.attr("fill")("none"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke")("currentColor"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke-width")("2"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke-linecap")("round"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke-linejoin")("round") ])([ /* #__PURE__ */ Halogen_HTML_Elements.elementNS("http://www.w3.org/2000/svg")("polyline")([ /* #__PURE__ */ Halogen_HTML_Properties.attr("points")("20 6 9 17 4 12") ])([  ]) ]);

// | Dropdown menu checkbox item
var dropdownMenuCheckboxItem = function (propMods) {
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
        return Halogen_HTML_Elements.div(append1([ Hydrogen_UI_Core.cls([ "relative flex cursor-default select-none items-center rounded-sm py-1.5 pl-8 pr-2 text-sm outline-none transition-colors focus:bg-accent focus:text-accent-foreground hover:bg-accent hover:text-accent-foreground", disabledClasses, props.className ]), Halogen_HTML_Properties_ARIA.role("menuitemcheckbox"), Halogen_HTML_Properties_ARIA.checked((function () {
            if (props.checked) {
                return "true";
            };
            return "false";
        })()), Halogen_HTML_Properties.attr("data-state")((function () {
            if (props.checked) {
                return "checked";
            };
            return "unchecked";
        })()) ])((function () {
            if (props.onCheckedChange instanceof Data_Maybe.Just && !props.disabled) {
                return [ Halogen_HTML_Events.onClick(function (v) {
                    return props.onCheckedChange.value0(!props.checked);
                }) ];
            };
            return [  ];
        })()))([ Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "absolute left-2 flex h-3.5 w-3.5 items-center justify-center" ]) ])([ (function () {
            if (props.checked) {
                return checkIcon;
            };
            return Halogen_HTML_Core.text("");
        })() ]), Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "flex-1" ]) ])(children) ]);
    };
};

// | Set menu alignment
var align = function (a) {
    return function (props) {
        return {
            open: props.open,
            disabled: props.disabled,
            checked: props.checked,
            value: props.value,
            side: props.side,
            onToggle: props.onToggle,
            onSelect: props.onSelect,
            onCheckedChange: props.onCheckedChange,
            onValueChange: props.onValueChange,
            shortcut: props.shortcut,
            className: props.className,
            align: a
        };
    };
};
export {
    dropdownMenu,
    dropdownMenuTrigger,
    dropdownMenuContent,
    dropdownMenuItem,
    dropdownMenuCheckboxItem,
    dropdownMenuRadioGroup,
    dropdownMenuRadioItem,
    dropdownMenuLabel,
    dropdownMenuSeparator,
    dropdownMenuGroup,
    dropdownMenuSub,
    dropdownMenuSubTrigger,
    dropdownMenuSubContent,
    dropdownMenuShortcut,
    open,
    disabled,
    checked,
    value,
    side,
    align,
    onToggle,
    onSelect,
    onCheckedChange,
    onValueChange,
    shortcut,
    className,
    Top,
    Right,
    Bottom,
    Left,
    Start,
    Center,
    End,
    eqSide,
    eqAlign
};
