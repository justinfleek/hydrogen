// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                        // hydrogen // command
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Command Palette component (⌘K)
// |
// | Accessible command palette with fuzzy search, keyboard navigation,
// | command groups, and nested pages. Follows the ARIA combobox pattern.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Primitive.Command as Command
// |
// | Command.commandPalette [ Command.open state.isOpen ]
// |   [ Command.commandInput
// |       [ Command.placeholder "Type a command..."
// |       , Command.onInput HandleInput
// |       , Command.value state.search
// |       ]
// |   , Command.commandList []
// |       [ Command.commandGroup [ Command.heading "Recent" ]
// |           [ Command.commandItem
// |               [ Command.onSelect (HandleCommand "open-file")
// |               , Command.icon fileIcon
// |               , Command.shortcut "⌘O"
// |               ]
// |               [ HH.text "Open File" ]
// |           ]
// |       , Command.commandGroup [ Command.heading "Actions" ]
// |           [ Command.commandItem [ Command.onSelect (HandleCommand "save") ]
// |               [ HH.text "Save" ]
// |           , Command.commandItem [ Command.disabled true ]
// |               [ HH.text "Delete" ]
// |           ]
// |       , Command.commandEmpty []
// |           [ HH.text "No results found." ]
// |       ]
// |   ]
// | ```
// |
// | ## Keyboard Navigation
// |
// | - `↑/↓` - Navigate between items
// | - `Enter` - Select focused item
// | - `Escape` - Close palette
// | - `⌘K` / `Ctrl+K` - Global shortcut to open
// |
// | ## Nested Pages
// |
// | ```purescript
// | Command.commandItem [ Command.onSelect (NavigateTo "theme") ]
// |   [ HH.text "Change Theme →" ]
// |
// | -- In your state, track current page and render appropriate items
// | ```
// |
// | ## Loading State
// |
// | ```purescript
// | Command.commandLoading []
// |   [ HH.text "Searching..." ]
// | ```
import * as $foreign from "./foreign.js";
import * as DOM_HTML_Indexed_InputType from "../DOM.HTML.Indexed.InputType/index.js";
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Boolean from "../Data.Boolean/index.js";
import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Semigroup from "../Data.Semigroup/index.js";
import * as Data_String_CodePoints from "../Data.String.CodePoints/index.js";
import * as Data_String_CodeUnits from "../Data.String.CodeUnits/index.js";
import * as Data_String_Common from "../Data.String.Common/index.js";
import * as Halogen_HTML_Core from "../Halogen.HTML.Core/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Events from "../Halogen.HTML.Events/index.js";
import * as Halogen_HTML_Properties from "../Halogen.HTML.Properties/index.js";
import * as Halogen_HTML_Properties_ARIA from "../Halogen.HTML.Properties.ARIA/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";
var eq = /* #__PURE__ */ Data_Eq.eq(Data_String_CodePoints.eqCodePoint);
var append = /* #__PURE__ */ Data_Semigroup.append(Data_Semigroup.semigroupArray);
var type_ = /* #__PURE__ */ Halogen_HTML_Properties.type_(Halogen_HTML_Core.isPropInputType);
var value1 = /* #__PURE__ */ Halogen_HTML_Properties.value(Halogen_HTML_Core.isPropString);

// | Set input value
var value = function (v) {
    return function (props) {
        return {
            open: props.open,
            onClose: props.onClose,
            onInput: props.onInput,
            onSelect: props.onSelect,
            onKeyDown: props.onKeyDown,
            placeholder: props.placeholder,
            heading: props.heading,
            hasIcon: props.hasIcon,
            shortcut: props.shortcut,
            description: props.description,
            disabled: props.disabled,
            selected: props.selected,
            className: props.className,
            value: v
        };
    };
};

// | Spinner icon for loading state
var spinnerIcon = /* #__PURE__ */ Halogen_HTML_Elements.elementNS("http://www.w3.org/2000/svg")("svg")([ /* #__PURE__ */ Halogen_HTML_Properties.attr("class")("h-4 w-4 animate-spin"), /* #__PURE__ */ Halogen_HTML_Properties.attr("viewBox")("0 0 24 24"), /* #__PURE__ */ Halogen_HTML_Properties.attr("fill")("none"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke")("currentColor"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke-width")("2") ])([ /* #__PURE__ */ Halogen_HTML_Elements.elementNS("http://www.w3.org/2000/svg")("path")([ /* #__PURE__ */ Halogen_HTML_Properties.attr("d")("M21 12a9 9 0 1 1-6.219-8.56") ])([  ]) ]);

// | Set keyboard shortcut badge
var shortcut = function (s) {
    return function (props) {
        return {
            open: props.open,
            onClose: props.onClose,
            onInput: props.onInput,
            onSelect: props.onSelect,
            onKeyDown: props.onKeyDown,
            value: props.value,
            placeholder: props.placeholder,
            heading: props.heading,
            hasIcon: props.hasIcon,
            description: props.description,
            disabled: props.disabled,
            selected: props.selected,
            className: props.className,
            shortcut: s
        };
    };
};

// | Set selected/highlighted state
var selected = function (s) {
    return function (props) {
        return {
            open: props.open,
            onClose: props.onClose,
            onInput: props.onInput,
            onSelect: props.onSelect,
            onKeyDown: props.onKeyDown,
            value: props.value,
            placeholder: props.placeholder,
            heading: props.heading,
            hasIcon: props.hasIcon,
            shortcut: props.shortcut,
            description: props.description,
            disabled: props.disabled,
            className: props.className,
            selected: s
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // icons
// ═══════════════════════════════════════════════════════════════════════════════
// | Search icon for input
var searchIcon = /* #__PURE__ */ Halogen_HTML_Elements.elementNS("http://www.w3.org/2000/svg")("svg")([ /* #__PURE__ */ Halogen_HTML_Properties.attr("class")("mr-2 h-4 w-4 shrink-0 opacity-50"), /* #__PURE__ */ Halogen_HTML_Properties.attr("viewBox")("0 0 24 24"), /* #__PURE__ */ Halogen_HTML_Properties.attr("fill")("none"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke")("currentColor"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke-width")("2"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke-linecap")("round"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke-linejoin")("round") ])([ /* #__PURE__ */ Halogen_HTML_Elements.elementNS("http://www.w3.org/2000/svg")("circle")([ /* #__PURE__ */ Halogen_HTML_Properties.attr("cx")("11"), /* #__PURE__ */ Halogen_HTML_Properties.attr("cy")("11"), /* #__PURE__ */ Halogen_HTML_Properties.attr("r")("8") ])([  ]), /* #__PURE__ */ Halogen_HTML_Elements.elementNS("http://www.w3.org/2000/svg")("path")([ /* #__PURE__ */ Halogen_HTML_Properties.attr("d")("m21 21-4.3-4.3") ])([  ]) ]);

// | Set input placeholder
var placeholder = function (p) {
    return function (props) {
        return {
            open: props.open,
            onClose: props.onClose,
            onInput: props.onInput,
            onSelect: props.onSelect,
            onKeyDown: props.onKeyDown,
            value: props.value,
            heading: props.heading,
            hasIcon: props.hasIcon,
            shortcut: props.shortcut,
            description: props.description,
            disabled: props.disabled,
            selected: props.selected,
            className: props.className,
            placeholder: p
        };
    };
};

// | Set open state
var open = function (o) {
    return function (props) {
        return {
            onClose: props.onClose,
            onInput: props.onInput,
            onSelect: props.onSelect,
            onKeyDown: props.onKeyDown,
            value: props.value,
            placeholder: props.placeholder,
            heading: props.heading,
            hasIcon: props.hasIcon,
            shortcut: props.shortcut,
            description: props.description,
            disabled: props.disabled,
            selected: props.selected,
            className: props.className,
            open: o
        };
    };
};

// | Set item select handler
var onSelect = function (handler) {
    return function (props) {
        return {
            open: props.open,
            onClose: props.onClose,
            onInput: props.onInput,
            onKeyDown: props.onKeyDown,
            value: props.value,
            placeholder: props.placeholder,
            heading: props.heading,
            hasIcon: props.hasIcon,
            shortcut: props.shortcut,
            description: props.description,
            disabled: props.disabled,
            selected: props.selected,
            className: props.className,
            onSelect: new Data_Maybe.Just(handler)
        };
    };
};

// | Set keyboard handler (exported for keyboard navigation)
var onKeyDown = function (handler) {
    return function (props) {
        return {
            open: props.open,
            onClose: props.onClose,
            onInput: props.onInput,
            onSelect: props.onSelect,
            value: props.value,
            placeholder: props.placeholder,
            heading: props.heading,
            hasIcon: props.hasIcon,
            shortcut: props.shortcut,
            description: props.description,
            disabled: props.disabled,
            selected: props.selected,
            className: props.className,
            onKeyDown: new Data_Maybe.Just(handler)
        };
    };
};

// | Set input change handler
var onInput = function (handler) {
    return function (props) {
        return {
            open: props.open,
            onClose: props.onClose,
            onSelect: props.onSelect,
            onKeyDown: props.onKeyDown,
            value: props.value,
            placeholder: props.placeholder,
            heading: props.heading,
            hasIcon: props.hasIcon,
            shortcut: props.shortcut,
            description: props.description,
            disabled: props.disabled,
            selected: props.selected,
            className: props.className,
            onInput: new Data_Maybe.Just(handler)
        };
    };
};

// | Set close handler
var onClose = function (handler) {
    return function (props) {
        return {
            open: props.open,
            onInput: props.onInput,
            onSelect: props.onSelect,
            onKeyDown: props.onKeyDown,
            value: props.value,
            placeholder: props.placeholder,
            heading: props.heading,
            hasIcon: props.hasIcon,
            shortcut: props.shortcut,
            description: props.description,
            disabled: props.disabled,
            selected: props.selected,
            className: props.className,
            onClose: new Data_Maybe.Just(handler)
        };
    };
};

// | Set group heading
var heading = function (h) {
    return function (props) {
        return {
            open: props.open,
            onClose: props.onClose,
            onInput: props.onInput,
            onSelect: props.onSelect,
            onKeyDown: props.onKeyDown,
            value: props.value,
            placeholder: props.placeholder,
            hasIcon: props.hasIcon,
            shortcut: props.shortcut,
            description: props.description,
            disabled: props.disabled,
            selected: props.selected,
            className: props.className,
            heading: h
        };
    };
};

// | Mark item as having an icon (icon provided as first child)
var hasIcon = function (b) {
    return function (props) {
        return {
            open: props.open,
            onClose: props.onClose,
            onInput: props.onInput,
            onSelect: props.onSelect,
            onKeyDown: props.onKeyDown,
            value: props.value,
            placeholder: props.placeholder,
            heading: props.heading,
            shortcut: props.shortcut,
            description: props.description,
            disabled: props.disabled,
            selected: props.selected,
            className: props.className,
            hasIcon: b
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // fuzzy search
// ═══════════════════════════════════════════════════════════════════════════════
// | Check if query fuzzy matches target string
// |
// | ```purescript
// | fuzzyMatch "ofi" "Open File" == true
// | fuzzyMatch "xyz" "Open File" == false
// | ```
var fuzzyMatch = function (query) {
    return function (target) {
        var matchChars = function ($copy_q$prime) {
            return function ($copy_t$prime) {
                return function ($copy_qi) {
                    return function ($copy_ti) {
                        var $tco_var_q$prime = $copy_q$prime;
                        var $tco_var_t$prime = $copy_t$prime;
                        var $tco_var_qi = $copy_qi;
                        var $tco_done = false;
                        var $tco_result;
                        function $tco_loop(q$prime, t$prime, qi, ti) {
                            if (qi >= Data_String_CodePoints.length(q$prime)) {
                                $tco_done = true;
                                return true;
                            };
                            if (ti >= Data_String_CodePoints.length(t$prime)) {
                                $tco_done = true;
                                return false;
                            };
                            if (Data_Boolean.otherwise) {
                                var tc = Data_String_CodePoints.codePointAt(ti)(t$prime);
                                var qc = Data_String_CodePoints.codePointAt(qi)(q$prime);
                                if (qc instanceof Data_Maybe.Just && (tc instanceof Data_Maybe.Just && eq(qc.value0)(tc.value0))) {
                                    $tco_var_q$prime = q$prime;
                                    $tco_var_t$prime = t$prime;
                                    $tco_var_qi = qi + 1 | 0;
                                    $copy_ti = ti + 1 | 0;
                                    return;
                                };
                                $tco_var_q$prime = q$prime;
                                $tco_var_t$prime = t$prime;
                                $tco_var_qi = qi;
                                $copy_ti = ti + 1 | 0;
                                return;
                            };
                            throw new Error("Failed pattern match at Hydrogen.Primitive.Command (line 484, column 3 - line 484, column 58): " + [ q$prime.constructor.name, t$prime.constructor.name, qi.constructor.name, ti.constructor.name ]);
                        };
                        while (!$tco_done) {
                            $tco_result = $tco_loop($tco_var_q$prime, $tco_var_t$prime, $tco_var_qi, $copy_ti);
                        };
                        return $tco_result;
                    };
                };
            };
        };
        var t = Data_String_Common.toLower(target);
        var q = Data_String_Common.toLower(query);
        return Data_String_CodeUnits.contains(q)(t) || matchChars(q)(t)(0)(0);
    };
};

// | Set disabled state
var disabled = function (d) {
    return function (props) {
        return {
            open: props.open,
            onClose: props.onClose,
            onInput: props.onInput,
            onSelect: props.onSelect,
            onKeyDown: props.onKeyDown,
            value: props.value,
            placeholder: props.placeholder,
            heading: props.heading,
            hasIcon: props.hasIcon,
            shortcut: props.shortcut,
            description: props.description,
            selected: props.selected,
            className: props.className,
            disabled: d
        };
    };
};

// | Set item description
var description = function (d) {
    return function (props) {
        return {
            open: props.open,
            onClose: props.onClose,
            onInput: props.onInput,
            onSelect: props.onSelect,
            onKeyDown: props.onKeyDown,
            value: props.value,
            placeholder: props.placeholder,
            heading: props.heading,
            hasIcon: props.hasIcon,
            shortcut: props.shortcut,
            disabled: props.disabled,
            selected: props.selected,
            className: props.className,
            description: d
        };
    };
};
var defaultProps = /* #__PURE__ */ (function () {
    return {
        open: false,
        onClose: Data_Maybe.Nothing.value,
        onInput: Data_Maybe.Nothing.value,
        onSelect: Data_Maybe.Nothing.value,
        onKeyDown: Data_Maybe.Nothing.value,
        value: "",
        placeholder: "Type a command or search...",
        heading: "",
        hasIcon: false,
        shortcut: "",
        description: "",
        disabled: false,
        selected: false,
        className: ""
    };
})();

// | Keyboard shortcut badge
// |
// | Displays keyboard shortcuts inline with command items.
var commandShortcut = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.kbd([ Hydrogen_UI_Core.cls([ "pointer-events-none ml-auto inline-flex h-5 select-none items-center gap-1 rounded border bg-muted px-1.5 font-mono text-[10px] font-medium text-muted-foreground opacity-100", props.className ]) ])(children);
    };
};

// | Separator between groups
var commandSeparator = function (propMods) {
    var props = Data_Array.foldl(function (p) {
        return function (f) {
            return f(p);
        };
    })(defaultProps)(propMods);
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "-mx-2 h-px bg-border", props.className ]), Halogen_HTML_Properties_ARIA.role("separator") ])([  ]);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // components
// ═══════════════════════════════════════════════════════════════════════════════
// | Command palette root container
// |
// | This is the main container that renders the palette in a fixed overlay.
// | Use `commandDialog` for the inner content area.
var commandPalette = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        if (props.open) {
            return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "fixed inset-0 z-50", props.className ]), Halogen_HTML_Properties_ARIA.role("dialog"), Halogen_HTML_Properties_ARIA.modal("true"), Halogen_HTML_Properties.attr("data-state")("open") ])([ Halogen_HTML_Elements.div(append([ Hydrogen_UI_Core.cls([ "fixed inset-0 bg-black/50 backdrop-blur-sm animate-in fade-in-0" ]) ])((function () {
                if (props.onClose instanceof Data_Maybe.Just) {
                    return [ Halogen_HTML_Events.onClick(props.onClose.value0) ];
                };
                if (props.onClose instanceof Data_Maybe.Nothing) {
                    return [  ];
                };
                throw new Error("Failed pattern match at Hydrogen.Primitive.Command (line 235, column 16 - line 237, column 28): " + [ props.onClose.constructor.name ]);
            })()))([  ]), Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "fixed inset-0 flex items-start justify-center pt-[15vh]" ]) ])(children) ]);
        };
        return Halogen_HTML_Core.text("");
    };
};

// | Loading state for async commands
var commandLoading = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex items-center justify-center py-6 gap-2 text-sm text-muted-foreground", props.className ]) ])([ spinnerIcon, Halogen_HTML_Elements.span_(children) ]);
    };
};

// | Command list container
// |
// | Wraps all command groups and items. Provides scrolling for long lists.
var commandList = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "max-h-[300px] overflow-y-auto overflow-x-hidden p-2", props.className ]), Halogen_HTML_Properties.id("command-list"), Halogen_HTML_Properties_ARIA.role("listbox") ])(children);
    };
};

// | Command item
// |
// | An individual selectable command with optional icon, shortcut, and description.
// | If `hasIcon true` is set, the first child is treated as the icon and wrapped
// | in an icon container.
var commandItem = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        var selectedClasses = (function () {
            if (props.selected) {
                return "bg-accent text-accent-foreground";
            };
            return "";
        })();
        var disabledClasses = (function () {
            if (props.disabled) {
                return "opacity-50 pointer-events-none";
            };
            return "cursor-pointer";
        })();
        return Halogen_HTML_Elements.div(append([ Hydrogen_UI_Core.cls([ "relative flex cursor-default select-none items-center rounded-sm px-2 py-1.5 text-sm outline-none transition-colors hover:bg-accent hover:text-accent-foreground aria-selected:bg-accent aria-selected:text-accent-foreground", disabledClasses, selectedClasses, props.className ]), Halogen_HTML_Properties_ARIA.role("option"), Halogen_HTML_Properties_ARIA.selected((function () {
            if (props.selected) {
                return "true";
            };
            return "false";
        })()), Halogen_HTML_Properties_ARIA.disabled((function () {
            if (props.disabled) {
                return "true";
            };
            return "false";
        })()), Halogen_HTML_Properties.attr("data-disabled")((function () {
            if (props.disabled) {
                return "true";
            };
            return "false";
        })()) ])((function () {
            if (props.onSelect instanceof Data_Maybe.Just && !props.disabled) {
                return [ Halogen_HTML_Events.onClick(props.onSelect.value0) ];
            };
            return [  ];
        })()))(append([ Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "flex items-center flex-1 gap-2" ]) ])(append(children)((function () {
            var $42 = props.description !== "";
            if ($42) {
                return [ Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "ml-2 text-muted-foreground text-xs" ]) ])([ Halogen_HTML_Core.text(props.description) ]) ];
            };
            return [  ];
        })())) ])((function () {
            var $43 = props.shortcut !== "";
            if ($43) {
                return [ commandShortcut([  ])([ Halogen_HTML_Core.text(props.shortcut) ]) ];
            };
            return [  ];
        })()));
    };
};

// | Command search input
// |
// | The search field at the top of the palette.
var commandInput = function (propMods) {
    var props = Data_Array.foldl(function (p) {
        return function (f) {
            return f(p);
        };
    })(defaultProps)(propMods);
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex items-center border-b px-3", props.className ]) ])([ searchIcon, Halogen_HTML_Elements.input(append([ Hydrogen_UI_Core.cls([ "flex h-12 w-full rounded-md bg-transparent py-3 text-sm outline-none placeholder:text-muted-foreground disabled:cursor-not-allowed disabled:opacity-50" ]), type_(DOM_HTML_Indexed_InputType.InputText.value), Halogen_HTML_Properties.placeholder(props.placeholder), value1(props.value), Halogen_HTML_Properties.attr("autocomplete")("off"), Halogen_HTML_Properties.attr("autocorrect")("off"), Halogen_HTML_Properties.attr("spellcheck")("false"), Halogen_HTML_Properties_ARIA.role("combobox"), Halogen_HTML_Properties_ARIA.expanded("true"), Halogen_HTML_Properties_ARIA.controls("command-list"), Halogen_HTML_Properties_ARIA.autoComplete("list") ])((function () {
        if (props.onInput instanceof Data_Maybe.Just) {
            return [ Halogen_HTML_Events.onValueInput(props.onInput.value0) ];
        };
        if (props.onInput instanceof Data_Maybe.Nothing) {
            return [  ];
        };
        throw new Error("Failed pattern match at Hydrogen.Primitive.Command (line 283, column 16 - line 285, column 26): " + [ props.onInput.constructor.name ]);
    })())) ]);
};

// | Command group with heading
// |
// | Groups related commands under a heading.
var commandGroup = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "overflow-hidden py-2", props.className ]), Halogen_HTML_Properties_ARIA.role("group") ])(append((function () {
            var $46 = props.heading !== "";
            if ($46) {
                return [ Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "px-2 py-1.5 text-xs font-medium text-muted-foreground" ]) ])([ Halogen_HTML_Core.text(props.heading) ]) ];
            };
            return [  ];
        })())(children));
    };
};

// | Empty state when no results found
var commandEmpty = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "py-6 text-center text-sm text-muted-foreground", props.className ]) ])(children);
    };
};

// | Command dialog content panel
// |
// | The floating dialog containing the search input and command list.
var commandDialog = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "relative w-full max-w-lg overflow-hidden rounded-xl border bg-popover shadow-2xl animate-in fade-in-0 zoom-in-95 slide-in-from-top-2", props.className ]), Halogen_HTML_Properties_ARIA.role("combobox"), Halogen_HTML_Properties_ARIA.expanded("true"), Halogen_HTML_Properties_ARIA.hasPopup("listbox") ])(children);
    };
};

// | Add custom class
var className = function (c) {
    return function (props) {
        return {
            open: props.open,
            onClose: props.onClose,
            onInput: props.onInput,
            onSelect: props.onSelect,
            onKeyDown: props.onKeyDown,
            value: props.value,
            placeholder: props.placeholder,
            heading: props.heading,
            hasIcon: props.hasIcon,
            shortcut: props.shortcut,
            description: props.description,
            disabled: props.disabled,
            selected: props.selected,
            className: props.className + (" " + c)
        };
    };
};
export {
    registerGlobalShortcut,
    unregisterGlobalShortcut,
    fuzzyScore
} from "./foreign.js";
export {
    commandPalette,
    commandDialog,
    commandInput,
    commandList,
    commandEmpty,
    commandLoading,
    commandGroup,
    commandSeparator,
    commandItem,
    commandShortcut,
    open,
    onClose,
    onInput,
    onSelect,
    onKeyDown,
    value,
    placeholder,
    heading,
    hasIcon,
    shortcut,
    description,
    disabled,
    selected,
    className,
    fuzzyMatch
};
