// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                    // hydrogen // contextmenu
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Context Menu component
// |
// | Right-click menus with items, submenus, separators, and keyboard navigation.
// | Follows the ARIA menu pattern for accessibility.
// |
// | ## Features
// |
// | - **Right-click trigger**: Opens at cursor position
// | - **Positioned at cursor**: Appears where user right-clicked
// | - **Menu items**: With optional icons and shortcuts
// | - **Submenus**: Nested menus for hierarchical navigation
// | - **Separators**: Visual dividers between item groups
// | - **Disabled items**: Grayed out non-interactive items
// | - **Keyboard navigation**: Arrow keys, Enter, Escape
// | - **ARIA menu pattern**: Fully accessible
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Primitive.ContextMenu as ContextMenu
// |
// | ContextMenu.contextMenu [ ContextMenu.open state.isOpen ]
// |   [ ContextMenu.contextMenuTrigger []
// |       [ HH.div [ HP.class_ "w-full h-64 border" ]
// |           [ HH.text "Right-click here" ]
// |       ]
// |   , ContextMenu.contextMenuContent
// |       [ ContextMenu.position state.position ]
// |       [ ContextMenu.contextMenuItem
// |           [ ContextMenu.onSelect (SelectAction "edit")
// |           , ContextMenu.icon editIcon
// |           ]
// |           [ HH.text "Edit" ]
// |       , ContextMenu.contextMenuItem
// |           [ ContextMenu.onSelect (SelectAction "copy") ]
// |           [ HH.text "Copy" ]
// |       , ContextMenu.contextMenuSeparator []
// |       , ContextMenu.contextMenuSub []
// |           [ ContextMenu.contextMenuSubTrigger []
// |               [ HH.text "More options" ]
// |           , ContextMenu.contextMenuSubContent []
// |               [ ContextMenu.contextMenuItem [] [ HH.text "Option 1" ]
// |               , ContextMenu.contextMenuItem [] [ HH.text "Option 2" ]
// |               ]
// |           ]
// |       , ContextMenu.contextMenuSeparator []
// |       , ContextMenu.contextMenuItem
// |           [ ContextMenu.disabled true ]
// |           [ HH.text "Disabled item" ]
// |       ]
// |   ]
// | ```
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Semigroup from "../Data.Semigroup/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Halogen_HTML_Core from "../Halogen.HTML.Core/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Events from "../Halogen.HTML.Events/index.js";
import * as Halogen_HTML_Properties from "../Halogen.HTML.Properties/index.js";
import * as Halogen_HTML_Properties_ARIA from "../Halogen.HTML.Properties.ARIA/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";
var append = /* #__PURE__ */ Data_Semigroup.append(Data_Semigroup.semigroupArray);
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);

// | Set Y coordinate only
var positionY = function (y) {
    return function (props) {
        return {
            open: props.open,
            onOpenChange: props.onOpenChange,
            onSelect: props.onSelect,
            disabled: props.disabled,
            className: props.className,
            position: {
                x: props.position.x,
                y: y
            }
        };
    };
};

// | Set X coordinate only
var positionX = function (x) {
    return function (props) {
        return {
            open: props.open,
            onOpenChange: props.onOpenChange,
            onSelect: props.onSelect,
            disabled: props.disabled,
            className: props.className,
            position: {
                y: props.position.y,
                x: x
            }
        };
    };
};

// | Set position (x, y coordinates)
var position = function (p) {
    return function (props) {
        return {
            open: props.open,
            onOpenChange: props.onOpenChange,
            onSelect: props.onSelect,
            disabled: props.disabled,
            className: props.className,
            position: p
        };
    };
};

// | Set open state
var open = function (o) {
    return function (props) {
        return {
            onOpenChange: props.onOpenChange,
            onSelect: props.onSelect,
            disabled: props.disabled,
            position: props.position,
            className: props.className,
            open: o
        };
    };
};

// | Set select handler for menu items
var onSelect = function (handler) {
    return function (props) {
        return {
            open: props.open,
            onOpenChange: props.onOpenChange,
            disabled: props.disabled,
            position: props.position,
            className: props.className,
            onSelect: new Data_Maybe.Just(handler)
        };
    };
};

// | Set open change handler (for controlled mode)
var onOpenChange = function (handler) {
    return function (props) {
        return {
            open: props.open,
            onSelect: props.onSelect,
            disabled: props.disabled,
            position: props.position,
            className: props.className,
            onOpenChange: new Data_Maybe.Just(handler)
        };
    };
};

// | Set disabled state for menu items
var disabled = function (d) {
    return function (props) {
        return {
            open: props.open,
            onOpenChange: props.onOpenChange,
            onSelect: props.onSelect,
            position: props.position,
            className: props.className,
            disabled: d
        };
    };
};
var defaultProps = /* #__PURE__ */ (function () {
    return {
        open: false,
        onOpenChange: Data_Maybe.Nothing.value,
        onSelect: Data_Maybe.Nothing.value,
        disabled: false,
        position: {
            x: 0,
            y: 0
        },
        className: ""
    };
})();

// | Context menu trigger
// |
// | The element that triggers the context menu on right-click.
var contextMenuTrigger = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ props.className ]), Halogen_HTML_Properties.attr("data-context-menu")("trigger") ])(children);
    };
};

// | Context menu submenu content
// |
// | The nested menu that appears when hovering the submenu trigger.
var contextMenuSubContent = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "absolute left-full top-0 z-50 min-w-[8rem] overflow-hidden rounded-md border bg-popover p-1 text-popover-foreground shadow-lg", "opacity-0 invisible group-hover:opacity-100 group-hover:visible", "transition-all duration-150", props.className ]), Halogen_HTML_Properties_ARIA.role("menu"), Halogen_HTML_Properties.attr("data-context-menu")("sub-content") ])(children);
    };
};

// | Context menu submenu container
// |
// | Contains a submenu trigger and content.
var contextMenuSub = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "relative group", props.className ]), Halogen_HTML_Properties.attr("data-context-menu")("sub") ])(children);
    };
};

// | Context menu keyboard shortcut display
// |
// | Shows a keyboard shortcut hint on the right side of an item.
var contextMenuShortcut = function (propMods) {
    return function (shortcutText) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "ml-auto text-xs tracking-widest text-muted-foreground", props.className ]), Halogen_HTML_Properties.attr("data-context-menu")("shortcut") ])([ Halogen_HTML_Core.text(shortcutText) ]);
    };
};

// | Context menu separator
// |
// | A visual divider between groups of items.
var contextMenuSeparator = function (propMods) {
    var props = Data_Array.foldl(function (p) {
        return function (f) {
            return f(p);
        };
    })(defaultProps)(propMods);
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "-mx-1 my-1 h-px bg-muted", props.className ]), Halogen_HTML_Properties_ARIA.role("separator"), Halogen_HTML_Properties.attr("data-context-menu")("separator") ])([  ]);
};

// | Context menu label
// |
// | Non-interactive label for grouping items.
var contextMenuLabel = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "px-2 py-1.5 text-sm font-semibold", props.className ]), Halogen_HTML_Properties.attr("data-context-menu")("label") ])(children);
    };
};

// | Context menu item
// |
// | A selectable item in the context menu.
var contextMenuItem = function (propMods) {
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
        return Halogen_HTML_Elements.div(append([ Hydrogen_UI_Core.cls([ "relative flex select-none items-center rounded-sm px-2 py-1.5 text-sm outline-none", "transition-colors focus:bg-accent focus:text-accent-foreground", "hover:bg-accent hover:text-accent-foreground", disabledClasses, props.className ]), Halogen_HTML_Properties_ARIA.role("menuitem"), Halogen_HTML_Properties.tabIndex((function () {
            if (props.disabled) {
                return -1 | 0;
            };
            return 0;
        })()), Halogen_HTML_Properties.attr("data-disabled")((function () {
            if (props.disabled) {
                return "true";
            };
            return "false";
        })()), Halogen_HTML_Properties.attr("data-context-menu")("item") ])((function () {
            if (props.onSelect instanceof Data_Maybe.Just && !props.disabled) {
                return [ Halogen_HTML_Events.onClick(props.onSelect.value0) ];
            };
            return [  ];
        })()))(children);
    };
};

// | Context menu group
// |
// | Groups related items together.
var contextMenuGroup = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ props.className ]), Halogen_HTML_Properties_ARIA.role("group"), Halogen_HTML_Properties.attr("data-context-menu")("group") ])(children);
    };
};

// | Context menu content panel
// |
// | The floating menu that appears on right-click.
// | Positioned at the cursor coordinates.
var contextMenuContent = function (propMods) {
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
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "fixed z-50 min-w-[8rem] overflow-hidden rounded-md border bg-popover p-1 text-popover-foreground shadow-md", "animate-in fade-in-0 zoom-in-95", visibilityClass, props.className ]), Halogen_HTML_Properties.style("left: " + (show(props.position.x) + ("px; top: " + (show(props.position.y) + "px;")))), Halogen_HTML_Properties_ARIA.role("menu"), Halogen_HTML_Properties.attr("data-context-menu")("content"), Halogen_HTML_Properties.attr("data-state")((function () {
            if (props.open) {
                return "open";
            };
            return "closed";
        })()) ])(children);
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // components
// ═══════════════════════════════════════════════════════════════════════════════
// | Context menu root container
// |
// | Wraps the trigger and content elements.
var contextMenu = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "relative", props.className ]), Halogen_HTML_Properties.attr("data-state")((function () {
            if (props.open) {
                return "open";
            };
            return "closed";
        })()), Halogen_HTML_Properties.attr("data-context-menu")("root") ])(children);
    };
};

// | Add custom class
var className = function (c) {
    return function (props) {
        return {
            open: props.open,
            onOpenChange: props.onOpenChange,
            onSelect: props.onSelect,
            disabled: props.disabled,
            position: props.position,
            className: props.className + (" " + c)
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // helpers
// ═══════════════════════════════════════════════════════════════════════════════
// | Chevron right icon for submenu indicators
var chevronRight = /* #__PURE__ */ Halogen_HTML_Elements.elementNS("http://www.w3.org/2000/svg")("svg")([ /* #__PURE__ */ Halogen_HTML_Properties.attr("class")("ml-auto h-4 w-4"), /* #__PURE__ */ Halogen_HTML_Properties.attr("viewBox")("0 0 24 24"), /* #__PURE__ */ Halogen_HTML_Properties.attr("fill")("none"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke")("currentColor"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke-width")("2"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke-linecap")("round"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke-linejoin")("round") ])([ /* #__PURE__ */ Halogen_HTML_Elements.elementNS("http://www.w3.org/2000/svg")("polyline")([ /* #__PURE__ */ Halogen_HTML_Properties.attr("points")("9 18 15 12 9 6") ])([  ]) ]);

// | Context menu submenu trigger
// |
// | Item that opens a submenu when hovered or focused.
var contextMenuSubTrigger = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "relative flex select-none items-center rounded-sm px-2 py-1.5 text-sm outline-none", "transition-colors focus:bg-accent focus:text-accent-foreground", "hover:bg-accent hover:text-accent-foreground cursor-pointer", props.className ]), Halogen_HTML_Properties_ARIA.role("menuitem"), Halogen_HTML_Properties_ARIA.hasPopup("menu"), Halogen_HTML_Properties.tabIndex(0), Halogen_HTML_Properties.attr("data-context-menu")("sub-trigger") ])(append(children)([ chevronRight ]));
    };
};
export {
    contextMenu,
    contextMenuTrigger,
    contextMenuContent,
    contextMenuItem,
    contextMenuSeparator,
    contextMenuLabel,
    contextMenuGroup,
    contextMenuSub,
    contextMenuSubTrigger,
    contextMenuSubContent,
    contextMenuShortcut,
    open,
    onOpenChange,
    onSelect,
    disabled,
    className,
    position,
    positionX,
    positionY
};
