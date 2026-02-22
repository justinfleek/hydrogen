// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                   // hydrogen // autocomplete
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | AutoComplete/Combobox component
// |
// | A text input with autocomplete suggestions dropdown.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Component.AutoComplete as AC
// |
// | -- Basic autocomplete
// | AC.autoComplete
// |   [ AC.suggestions [ "Apple", "Apricot", "Avocado", "Banana" ]
// |   , AC.value state.query
// |   , AC.onInput HandleInput
// |   , AC.onSelect HandleSelect
// |   ]
// |
// | -- With custom suggestion rendering
// | AC.autoComplete
// |   [ AC.suggestionsWithData users
// |   , AC.renderSuggestion \user -> HH.div_ [ HH.text user.name ]
// |   , AC.onSelectData HandleUserSelect
// |   ]
// |
// | -- Async loading
// | AC.autoComplete
// |   [ AC.suggestions filteredResults
// |   , AC.loading isSearching
// |   , AC.onInput HandleSearch
// |   ]
// | ```
import * as DOM_HTML_Indexed_AutocompleteType from "../DOM.HTML.Indexed.AutocompleteType/index.js";
import * as DOM_HTML_Indexed_InputType from "../DOM.HTML.Indexed.InputType/index.js";
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Semigroup from "../Data.Semigroup/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Data_String_CodePoints from "../Data.String.CodePoints/index.js";
import * as Halogen_HTML_Core from "../Halogen.HTML.Core/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Events from "../Halogen.HTML.Events/index.js";
import * as Halogen_HTML_Properties from "../Halogen.HTML.Properties/index.js";
import * as Halogen_HTML_Properties_ARIA from "../Halogen.HTML.Properties.ARIA/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";
var map = /* #__PURE__ */ Data_Functor.map(Data_Functor.functorArray);
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showBoolean);
var append1 = /* #__PURE__ */ Data_Semigroup.append(Data_Semigroup.semigroupArray);
var type_ = /* #__PURE__ */ Halogen_HTML_Properties.type_(Halogen_HTML_Core.isPropInputType);
var value1 = /* #__PURE__ */ Halogen_HTML_Properties.value(Halogen_HTML_Core.isPropString);

// | Set current input value
var value = function (v) {
    return function (props) {
        return {
            suggestions: props.suggestions,
            placeholder: props.placeholder,
            disabled: props.disabled,
            loading: props.loading,
            open: props.open,
            highlightedIndex: props.highlightedIndex,
            minChars: props.minChars,
            maxSuggestions: props.maxSuggestions,
            debounceMs: props.debounceMs,
            clearOnSelect: props.clearOnSelect,
            className: props.className,
            onInput: props.onInput,
            onSelect: props.onSelect,
            onSelectData: props.onSelectData,
            onOpenChange: props.onOpenChange,
            onHighlightChange: props.onHighlightChange,
            renderSuggestion: props.renderSuggestion,
            noResultsText: props.noResultsText,
            loadingText: props.loadingText,
            value: v
        };
    };
};

// | Set suggestions with custom data
var suggestionsWithData = function (sugs) {
    return function (props) {
        return {
            value: props.value,
            placeholder: props.placeholder,
            disabled: props.disabled,
            loading: props.loading,
            open: props.open,
            highlightedIndex: props.highlightedIndex,
            minChars: props.minChars,
            maxSuggestions: props.maxSuggestions,
            debounceMs: props.debounceMs,
            clearOnSelect: props.clearOnSelect,
            className: props.className,
            onInput: props.onInput,
            onSelect: props.onSelect,
            onSelectData: props.onSelectData,
            onOpenChange: props.onOpenChange,
            onHighlightChange: props.onHighlightChange,
            renderSuggestion: props.renderSuggestion,
            noResultsText: props.noResultsText,
            loadingText: props.loadingText,
            suggestions: sugs
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // prop builders
// ═══════════════════════════════════════════════════════════════════════════════
// | Set suggestions from simple strings
var suggestions = function (strs) {
    return function (props) {
        return {
            value: props.value,
            placeholder: props.placeholder,
            disabled: props.disabled,
            loading: props.loading,
            open: props.open,
            highlightedIndex: props.highlightedIndex,
            minChars: props.minChars,
            maxSuggestions: props.maxSuggestions,
            debounceMs: props.debounceMs,
            clearOnSelect: props.clearOnSelect,
            className: props.className,
            onInput: props.onInput,
            onSelect: props.onSelect,
            onSelectData: props.onSelectData,
            onOpenChange: props.onOpenChange,
            onHighlightChange: props.onHighlightChange,
            renderSuggestion: props.renderSuggestion,
            noResultsText: props.noResultsText,
            loadingText: props.loadingText,
            suggestions: map(function (s) {
                return {
                    value: s,
                    label: s,
                    data: Data_Maybe.Nothing.value,
                    disabled: false
                };
            })(strs)
        };
    };
};

// | Create a suggestion with attached data
var suggestionWithMeta = function (val) {
    return function (lbl) {
        return function (d) {
            return {
                value: val,
                label: lbl,
                data: new Data_Maybe.Just(d),
                disabled: false
            };
        };
    };
};

// | Create a simple string suggestion
var suggestion = function (s) {
    return {
        value: s,
        label: s,
        data: Data_Maybe.Nothing.value,
        disabled: false
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // helpers
// ═══════════════════════════════════════════════════════════════════════════════
// | Small loading spinner
var spinner = /* #__PURE__ */ Halogen_HTML_Elements.element("svg")([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "animate-spin h-4 w-4" ]), /* #__PURE__ */ Halogen_HTML_Properties.attr("xmlns")("http://www.w3.org/2000/svg"), /* #__PURE__ */ Halogen_HTML_Properties.attr("fill")("none"), /* #__PURE__ */ Halogen_HTML_Properties.attr("viewBox")("0 0 24 24") ])([ /* #__PURE__ */ Halogen_HTML_Elements.element("circle")([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "opacity-25" ]), /* #__PURE__ */ Halogen_HTML_Properties.attr("cx")("12"), /* #__PURE__ */ Halogen_HTML_Properties.attr("cy")("12"), /* #__PURE__ */ Halogen_HTML_Properties.attr("r")("10"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke")("currentColor"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke-width")("4") ])([  ]), /* #__PURE__ */ Halogen_HTML_Elements.element("path")([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "opacity-75" ]), /* #__PURE__ */ Halogen_HTML_Properties.attr("fill")("currentColor"), /* #__PURE__ */ Halogen_HTML_Properties.attr("d")("M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4zm2 5.291A7.962 7.962 0 014 12H0c0 3.042 1.135 5.824 3 7.938l3-2.647z") ])([  ]) ]);

// | Set custom suggestion renderer
var renderSuggestion = function (renderer) {
    return function (props) {
        return {
            suggestions: props.suggestions,
            value: props.value,
            placeholder: props.placeholder,
            disabled: props.disabled,
            loading: props.loading,
            open: props.open,
            highlightedIndex: props.highlightedIndex,
            minChars: props.minChars,
            maxSuggestions: props.maxSuggestions,
            debounceMs: props.debounceMs,
            clearOnSelect: props.clearOnSelect,
            className: props.className,
            onInput: props.onInput,
            onSelect: props.onSelect,
            onSelectData: props.onSelectData,
            onOpenChange: props.onOpenChange,
            onHighlightChange: props.onHighlightChange,
            noResultsText: props.noResultsText,
            loadingText: props.loadingText,
            renderSuggestion: new Data_Maybe.Just(renderer)
        };
    };
};

// | Set placeholder text
var placeholder = function (p) {
    return function (props) {
        return {
            suggestions: props.suggestions,
            value: props.value,
            disabled: props.disabled,
            loading: props.loading,
            open: props.open,
            highlightedIndex: props.highlightedIndex,
            minChars: props.minChars,
            maxSuggestions: props.maxSuggestions,
            debounceMs: props.debounceMs,
            clearOnSelect: props.clearOnSelect,
            className: props.className,
            onInput: props.onInput,
            onSelect: props.onSelect,
            onSelectData: props.onSelectData,
            onOpenChange: props.onOpenChange,
            onHighlightChange: props.onHighlightChange,
            renderSuggestion: props.renderSuggestion,
            noResultsText: props.noResultsText,
            loadingText: props.loadingText,
            placeholder: p
        };
    };
};

// | Control open state (controlled mode)
var open = function (o) {
    return function (props) {
        return {
            suggestions: props.suggestions,
            value: props.value,
            placeholder: props.placeholder,
            disabled: props.disabled,
            loading: props.loading,
            highlightedIndex: props.highlightedIndex,
            minChars: props.minChars,
            maxSuggestions: props.maxSuggestions,
            debounceMs: props.debounceMs,
            clearOnSelect: props.clearOnSelect,
            className: props.className,
            onInput: props.onInput,
            onSelect: props.onSelect,
            onSelectData: props.onSelectData,
            onOpenChange: props.onOpenChange,
            onHighlightChange: props.onHighlightChange,
            renderSuggestion: props.renderSuggestion,
            noResultsText: props.noResultsText,
            loadingText: props.loadingText,
            open: new Data_Maybe.Just(o)
        };
    };
};

// | Set selection handler (full suggestion with data)
var onSelectData = function (handler) {
    return function (props) {
        return {
            suggestions: props.suggestions,
            value: props.value,
            placeholder: props.placeholder,
            disabled: props.disabled,
            loading: props.loading,
            open: props.open,
            highlightedIndex: props.highlightedIndex,
            minChars: props.minChars,
            maxSuggestions: props.maxSuggestions,
            debounceMs: props.debounceMs,
            clearOnSelect: props.clearOnSelect,
            className: props.className,
            onInput: props.onInput,
            onSelect: props.onSelect,
            onOpenChange: props.onOpenChange,
            onHighlightChange: props.onHighlightChange,
            renderSuggestion: props.renderSuggestion,
            noResultsText: props.noResultsText,
            loadingText: props.loadingText,
            onSelectData: new Data_Maybe.Just(handler)
        };
    };
};

// | Set selection handler (value only)
var onSelect = function (handler) {
    return function (props) {
        return {
            suggestions: props.suggestions,
            value: props.value,
            placeholder: props.placeholder,
            disabled: props.disabled,
            loading: props.loading,
            open: props.open,
            highlightedIndex: props.highlightedIndex,
            minChars: props.minChars,
            maxSuggestions: props.maxSuggestions,
            debounceMs: props.debounceMs,
            clearOnSelect: props.clearOnSelect,
            className: props.className,
            onInput: props.onInput,
            onSelectData: props.onSelectData,
            onOpenChange: props.onOpenChange,
            onHighlightChange: props.onHighlightChange,
            renderSuggestion: props.renderSuggestion,
            noResultsText: props.noResultsText,
            loadingText: props.loadingText,
            onSelect: new Data_Maybe.Just(handler)
        };
    };
};

// | Set open state change handler
var onOpenChange = function (handler) {
    return function (props) {
        return {
            suggestions: props.suggestions,
            value: props.value,
            placeholder: props.placeholder,
            disabled: props.disabled,
            loading: props.loading,
            open: props.open,
            highlightedIndex: props.highlightedIndex,
            minChars: props.minChars,
            maxSuggestions: props.maxSuggestions,
            debounceMs: props.debounceMs,
            clearOnSelect: props.clearOnSelect,
            className: props.className,
            onInput: props.onInput,
            onSelect: props.onSelect,
            onSelectData: props.onSelectData,
            onHighlightChange: props.onHighlightChange,
            renderSuggestion: props.renderSuggestion,
            noResultsText: props.noResultsText,
            loadingText: props.loadingText,
            onOpenChange: new Data_Maybe.Just(handler)
        };
    };
};

// | Set input change handler
var onInput = function (handler) {
    return function (props) {
        return {
            suggestions: props.suggestions,
            value: props.value,
            placeholder: props.placeholder,
            disabled: props.disabled,
            loading: props.loading,
            open: props.open,
            highlightedIndex: props.highlightedIndex,
            minChars: props.minChars,
            maxSuggestions: props.maxSuggestions,
            debounceMs: props.debounceMs,
            clearOnSelect: props.clearOnSelect,
            className: props.className,
            onSelect: props.onSelect,
            onSelectData: props.onSelectData,
            onOpenChange: props.onOpenChange,
            onHighlightChange: props.onHighlightChange,
            renderSuggestion: props.renderSuggestion,
            noResultsText: props.noResultsText,
            loadingText: props.loadingText,
            onInput: new Data_Maybe.Just(handler)
        };
    };
};

// | Set highlight change handler (for keyboard navigation)
var onHighlightChange = function (handler) {
    return function (props) {
        return {
            suggestions: props.suggestions,
            value: props.value,
            placeholder: props.placeholder,
            disabled: props.disabled,
            loading: props.loading,
            open: props.open,
            highlightedIndex: props.highlightedIndex,
            minChars: props.minChars,
            maxSuggestions: props.maxSuggestions,
            debounceMs: props.debounceMs,
            clearOnSelect: props.clearOnSelect,
            className: props.className,
            onInput: props.onInput,
            onSelect: props.onSelect,
            onSelectData: props.onSelectData,
            onOpenChange: props.onOpenChange,
            renderSuggestion: props.renderSuggestion,
            noResultsText: props.noResultsText,
            loadingText: props.loadingText,
            onHighlightChange: new Data_Maybe.Just(handler)
        };
    };
};

// | Set text shown when no results
var noResultsText = function (t) {
    return function (props) {
        return {
            suggestions: props.suggestions,
            value: props.value,
            placeholder: props.placeholder,
            disabled: props.disabled,
            loading: props.loading,
            open: props.open,
            highlightedIndex: props.highlightedIndex,
            minChars: props.minChars,
            maxSuggestions: props.maxSuggestions,
            debounceMs: props.debounceMs,
            clearOnSelect: props.clearOnSelect,
            className: props.className,
            onInput: props.onInput,
            onSelect: props.onSelect,
            onSelectData: props.onSelectData,
            onOpenChange: props.onOpenChange,
            onHighlightChange: props.onHighlightChange,
            renderSuggestion: props.renderSuggestion,
            loadingText: props.loadingText,
            noResultsText: t
        };
    };
};

// | Set minimum characters before showing suggestions
var minChars = function (n) {
    return function (props) {
        return {
            suggestions: props.suggestions,
            value: props.value,
            placeholder: props.placeholder,
            disabled: props.disabled,
            loading: props.loading,
            open: props.open,
            highlightedIndex: props.highlightedIndex,
            maxSuggestions: props.maxSuggestions,
            debounceMs: props.debounceMs,
            clearOnSelect: props.clearOnSelect,
            className: props.className,
            onInput: props.onInput,
            onSelect: props.onSelect,
            onSelectData: props.onSelectData,
            onOpenChange: props.onOpenChange,
            onHighlightChange: props.onHighlightChange,
            renderSuggestion: props.renderSuggestion,
            noResultsText: props.noResultsText,
            loadingText: props.loadingText,
            minChars: n
        };
    };
};

// | Set maximum suggestions to display
var maxSuggestions = function (n) {
    return function (props) {
        return {
            suggestions: props.suggestions,
            value: props.value,
            placeholder: props.placeholder,
            disabled: props.disabled,
            loading: props.loading,
            open: props.open,
            highlightedIndex: props.highlightedIndex,
            minChars: props.minChars,
            debounceMs: props.debounceMs,
            clearOnSelect: props.clearOnSelect,
            className: props.className,
            onInput: props.onInput,
            onSelect: props.onSelect,
            onSelectData: props.onSelectData,
            onOpenChange: props.onOpenChange,
            onHighlightChange: props.onHighlightChange,
            renderSuggestion: props.renderSuggestion,
            noResultsText: props.noResultsText,
            loadingText: props.loadingText,
            maxSuggestions: n
        };
    };
};

// | Set text shown while loading
var loadingText = function (t) {
    return function (props) {
        return {
            suggestions: props.suggestions,
            value: props.value,
            placeholder: props.placeholder,
            disabled: props.disabled,
            loading: props.loading,
            open: props.open,
            highlightedIndex: props.highlightedIndex,
            minChars: props.minChars,
            maxSuggestions: props.maxSuggestions,
            debounceMs: props.debounceMs,
            clearOnSelect: props.clearOnSelect,
            className: props.className,
            onInput: props.onInput,
            onSelect: props.onSelect,
            onSelectData: props.onSelectData,
            onOpenChange: props.onOpenChange,
            onHighlightChange: props.onHighlightChange,
            renderSuggestion: props.renderSuggestion,
            noResultsText: props.noResultsText,
            loadingText: t
        };
    };
};

// | Set loading state
var loading = function (l) {
    return function (props) {
        return {
            suggestions: props.suggestions,
            value: props.value,
            placeholder: props.placeholder,
            disabled: props.disabled,
            open: props.open,
            highlightedIndex: props.highlightedIndex,
            minChars: props.minChars,
            maxSuggestions: props.maxSuggestions,
            debounceMs: props.debounceMs,
            clearOnSelect: props.clearOnSelect,
            className: props.className,
            onInput: props.onInput,
            onSelect: props.onSelect,
            onSelectData: props.onSelectData,
            onOpenChange: props.onOpenChange,
            onHighlightChange: props.onHighlightChange,
            renderSuggestion: props.renderSuggestion,
            noResultsText: props.noResultsText,
            loadingText: props.loadingText,
            loading: l
        };
    };
};

// | Suggestion item classes
var itemClasses = "relative flex cursor-default select-none items-center rounded-sm px-2 py-1.5 text-sm outline-none";

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // styling
// ═══════════════════════════════════════════════════════════════════════════════
// | Input base classes
var inputClasses = "flex h-10 w-full rounded-md border border-input bg-background px-3 py-2 text-sm ring-offset-background placeholder:text-muted-foreground focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2 disabled:cursor-not-allowed disabled:opacity-50";

// | Set highlighted suggestion index
var highlightedIndex = function (idx) {
    return function (props) {
        return {
            suggestions: props.suggestions,
            value: props.value,
            placeholder: props.placeholder,
            disabled: props.disabled,
            loading: props.loading,
            open: props.open,
            minChars: props.minChars,
            maxSuggestions: props.maxSuggestions,
            debounceMs: props.debounceMs,
            clearOnSelect: props.clearOnSelect,
            className: props.className,
            onInput: props.onInput,
            onSelect: props.onSelect,
            onSelectData: props.onSelectData,
            onOpenChange: props.onOpenChange,
            onHighlightChange: props.onHighlightChange,
            renderSuggestion: props.renderSuggestion,
            noResultsText: props.noResultsText,
            loadingText: props.loadingText,
            highlightedIndex: idx
        };
    };
};

// | Highlighted item classes
var highlightedClasses = "bg-accent text-accent-foreground";

// | Dropdown container classes
var dropdownClasses = "absolute z-50 mt-1 w-full max-h-60 overflow-auto rounded-md border bg-popover text-popover-foreground shadow-md animate-in fade-in-0 zoom-in-95";

// | Suggestions list (standalone)
var suggestionsList = function (children) {
    return Halogen_HTML_Elements.ul([ Hydrogen_UI_Core.cls([ dropdownClasses ]), Halogen_HTML_Properties_ARIA.role("listbox") ])(children);
};

// | Disabled item classes  
var disabledClasses = "pointer-events-none opacity-50";

// | Individual suggestion item (standalone)
var suggestionItem = function (opts) {
    return function (children) {
        var stateClasses = (function () {
            if (opts.highlighted) {
                return highlightedClasses;
            };
            return "";
        })() + (function () {
            if (opts.disabled) {
                return " " + disabledClasses;
            };
            return "";
        })();
        return Halogen_HTML_Elements.li([ Hydrogen_UI_Core.cls([ itemClasses, stateClasses ]), Halogen_HTML_Properties_ARIA.role("option"), Halogen_HTML_Properties_ARIA.selected(show(opts.highlighted)), Halogen_HTML_Properties.tabIndex(-1 | 0) ])(children);
    };
};

// | Set disabled state
var disabled = function (d) {
    return function (props) {
        return {
            suggestions: props.suggestions,
            value: props.value,
            placeholder: props.placeholder,
            loading: props.loading,
            open: props.open,
            highlightedIndex: props.highlightedIndex,
            minChars: props.minChars,
            maxSuggestions: props.maxSuggestions,
            debounceMs: props.debounceMs,
            clearOnSelect: props.clearOnSelect,
            className: props.className,
            onInput: props.onInput,
            onSelect: props.onSelect,
            onSelectData: props.onSelectData,
            onOpenChange: props.onOpenChange,
            onHighlightChange: props.onHighlightChange,
            renderSuggestion: props.renderSuggestion,
            noResultsText: props.noResultsText,
            loadingText: props.loadingText,
            disabled: d
        };
    };
};

// | Default autocomplete properties
var defaultProps = /* #__PURE__ */ (function () {
    return {
        suggestions: [  ],
        value: "",
        placeholder: "Search...",
        disabled: false,
        loading: false,
        open: Data_Maybe.Nothing.value,
        highlightedIndex: 0,
        minChars: 1,
        maxSuggestions: 10,
        debounceMs: 150,
        clearOnSelect: false,
        className: "",
        onInput: Data_Maybe.Nothing.value,
        onSelect: Data_Maybe.Nothing.value,
        onSelectData: Data_Maybe.Nothing.value,
        onOpenChange: Data_Maybe.Nothing.value,
        onHighlightChange: Data_Maybe.Nothing.value,
        renderSuggestion: Data_Maybe.Nothing.value,
        noResultsText: "No results found",
        loadingText: "Loading..."
    };
})();

// | Set debounce delay in milliseconds
var debounceMs = function (ms) {
    return function (props) {
        return {
            suggestions: props.suggestions,
            value: props.value,
            placeholder: props.placeholder,
            disabled: props.disabled,
            loading: props.loading,
            open: props.open,
            highlightedIndex: props.highlightedIndex,
            minChars: props.minChars,
            maxSuggestions: props.maxSuggestions,
            clearOnSelect: props.clearOnSelect,
            className: props.className,
            onInput: props.onInput,
            onSelect: props.onSelect,
            onSelectData: props.onSelectData,
            onOpenChange: props.onOpenChange,
            onHighlightChange: props.onHighlightChange,
            renderSuggestion: props.renderSuggestion,
            noResultsText: props.noResultsText,
            loadingText: props.loadingText,
            debounceMs: ms
        };
    };
};

// | Clear input on selection
var clearOnSelect = function (c) {
    return function (props) {
        return {
            suggestions: props.suggestions,
            value: props.value,
            placeholder: props.placeholder,
            disabled: props.disabled,
            loading: props.loading,
            open: props.open,
            highlightedIndex: props.highlightedIndex,
            minChars: props.minChars,
            maxSuggestions: props.maxSuggestions,
            debounceMs: props.debounceMs,
            className: props.className,
            onInput: props.onInput,
            onSelect: props.onSelect,
            onSelectData: props.onSelectData,
            onOpenChange: props.onOpenChange,
            onHighlightChange: props.onHighlightChange,
            renderSuggestion: props.renderSuggestion,
            noResultsText: props.noResultsText,
            loadingText: props.loadingText,
            clearOnSelect: c
        };
    };
};

// | Add custom class
var className = function (c) {
    return function (props) {
        return {
            suggestions: props.suggestions,
            value: props.value,
            placeholder: props.placeholder,
            disabled: props.disabled,
            loading: props.loading,
            open: props.open,
            highlightedIndex: props.highlightedIndex,
            minChars: props.minChars,
            maxSuggestions: props.maxSuggestions,
            debounceMs: props.debounceMs,
            clearOnSelect: props.clearOnSelect,
            onInput: props.onInput,
            onSelect: props.onSelect,
            onSelectData: props.onSelectData,
            onOpenChange: props.onOpenChange,
            onHighlightChange: props.onHighlightChange,
            renderSuggestion: props.renderSuggestion,
            noResultsText: props.noResultsText,
            loadingText: props.loadingText,
            className: props.className + (" " + c)
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // components
// ═══════════════════════════════════════════════════════════════════════════════
// | AutoComplete input field (standalone)
var autoCompleteInput = function (propMods) {
    var props = Data_Array.foldl(function (p) {
        return function (f) {
            return f(p);
        };
    })(defaultProps)(propMods);
    var inputHandler = (function () {
        if (props.onInput instanceof Data_Maybe.Just) {
            return [ Halogen_HTML_Events.onValueInput(props.onInput.value0) ];
        };
        if (props.onInput instanceof Data_Maybe.Nothing) {
            return [  ];
        };
        throw new Error("Failed pattern match at Hydrogen.Component.AutoComplete (line 290, column 20 - line 292, column 20): " + [ props.onInput.constructor.name ]);
    })();
    return Halogen_HTML_Elements.input(append1([ Hydrogen_UI_Core.cls([ inputClasses, props.className ]), type_(DOM_HTML_Indexed_InputType.InputText.value), Halogen_HTML_Properties.placeholder(props.placeholder), value1(props.value), Halogen_HTML_Properties.disabled(props.disabled), Halogen_HTML_Properties.autocomplete(DOM_HTML_Indexed_AutocompleteType.AutocompleteOff.value), Halogen_HTML_Properties_ARIA.role("combobox"), Halogen_HTML_Properties_ARIA.expanded(show(Data_Maybe.fromMaybe(false)(props.open))), Halogen_HTML_Properties_ARIA.hasPopup("listbox"), Halogen_HTML_Properties_ARIA.autoComplete("list") ])(inputHandler));
};

// | Full AutoComplete component
var autoComplete = function (propMods) {
    var props = Data_Array.foldl(function (p) {
        return function (f) {
            return f(p);
        };
    })(defaultProps)(propMods);
    
    // No results message
var noResults = Halogen_HTML_Elements.li([ Hydrogen_UI_Core.cls([ "px-2 py-1.5 text-sm text-muted-foreground text-center" ]) ])([ Halogen_HTML_Core.text(props.noResultsText) ]);
    
    // Loading indicator
var loadingIndicator = Halogen_HTML_Elements.li([ Hydrogen_UI_Core.cls([ "px-2 py-1.5 text-sm text-muted-foreground" ]) ])([ Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex items-center gap-2" ]) ])([ spinner, Halogen_HTML_Core.text(props.loadingText) ]) ]);
    var isOpen = Data_Maybe.fromMaybe(false)(props.open);
    
    // Determine if dropdown should show
var shouldShowDropdown = isOpen && (Data_String_CodePoints.length(props.value) >= props.minChars && !props.disabled);
    
    // Input event handlers
var inputHandlers = (function () {
        if (props.onInput instanceof Data_Maybe.Just) {
            return [ Halogen_HTML_Events.onValueInput(props.onInput.value0) ];
        };
        if (props.onInput instanceof Data_Maybe.Nothing) {
            return [  ];
        };
        throw new Error("Failed pattern match at Hydrogen.Component.AutoComplete (line 383, column 7 - line 385, column 22): " + [ props.onInput.constructor.name ]);
    })();
    var focusHandlers = (function () {
        if (props.onOpenChange instanceof Data_Maybe.Just) {
            return [ Halogen_HTML_Events.onFocus(function (v) {
                return props.onOpenChange.value0(true);
            }), Halogen_HTML_Events.onBlur(function (v) {
                return props.onOpenChange.value0(false);
            }) ];
        };
        if (props.onOpenChange instanceof Data_Maybe.Nothing) {
            return [  ];
        };
        throw new Error("Failed pattern match at Hydrogen.Component.AutoComplete (line 387, column 21 - line 392, column 20): " + [ props.onOpenChange.constructor.name ]);
    })();
    
    // Filter suggestions based on value
var filteredSuggestions = Data_Array.take(props.maxSuggestions)(props.suggestions);
    
    // Default suggestion renderer
var defaultRenderer = function (sug) {
        return Halogen_HTML_Core.text(sug.label);
    };
    
    // Render a suggestion
var renderSug = function (idx) {
        return function (sug) {
            var isHighlighted = idx === props.highlightedIndex;
            var clickHandler = (function () {
                if (props.onSelectData instanceof Data_Maybe.Just) {
                    return [ Halogen_HTML_Events.onClick(function (v) {
                        return props.onSelectData.value0(sug);
                    }) ];
                };
                if (props.onSelectData instanceof Data_Maybe.Nothing) {
                    if (props.onSelect instanceof Data_Maybe.Just) {
                        return [ Halogen_HTML_Events.onClick(function (v) {
                            return props.onSelect.value0(sug.value);
                        }) ];
                    };
                    if (props.onSelect instanceof Data_Maybe.Nothing) {
                        return [  ];
                    };
                    throw new Error("Failed pattern match at Hydrogen.Component.AutoComplete (line 364, column 22 - line 366, column 26): " + [ props.onSelect.constructor.name ]);
                };
                throw new Error("Failed pattern match at Hydrogen.Component.AutoComplete (line 362, column 24 - line 366, column 26): " + [ props.onSelectData.constructor.name ]);
            })();
            return Halogen_HTML_Elements.li(append1([ Hydrogen_UI_Core.cls([ itemClasses, (function () {
                if (isHighlighted) {
                    return highlightedClasses;
                };
                return "";
            })(), (function () {
                if (sug.disabled) {
                    return disabledClasses;
                };
                return "";
            })() ]), Halogen_HTML_Properties_ARIA.role("option"), Halogen_HTML_Properties_ARIA.selected(show(isHighlighted)), Halogen_HTML_Properties.tabIndex(-1 | 0) ])(clickHandler))([ defaultRenderer(sug) ]);
        };
    };
    
    // Dropdown content
var dropdownContent = (function () {
        if (props.loading) {
            return [ loadingIndicator ];
        };
        var $51 = Data_Array.length(filteredSuggestions) === 0;
        if ($51) {
            return [ noResults ];
        };
        return Data_Array.mapWithIndex(renderSug)(filteredSuggestions);
    })();
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "relative", props.className ]) ])([ Halogen_HTML_Elements.input(append1([ Hydrogen_UI_Core.cls([ inputClasses ]), type_(DOM_HTML_Indexed_InputType.InputText.value), Halogen_HTML_Properties.placeholder(props.placeholder), value1(props.value), Halogen_HTML_Properties.disabled(props.disabled), Halogen_HTML_Properties.autocomplete(DOM_HTML_Indexed_AutocompleteType.AutocompleteOff.value), Halogen_HTML_Properties_ARIA.role("combobox"), Halogen_HTML_Properties_ARIA.expanded(show(shouldShowDropdown)), Halogen_HTML_Properties_ARIA.hasPopup("listbox"), Halogen_HTML_Properties_ARIA.autoComplete("list") ])(append1(inputHandlers)(focusHandlers))), (function () {
        if (shouldShowDropdown) {
            return Halogen_HTML_Elements.ul([ Hydrogen_UI_Core.cls([ dropdownClasses ]), Halogen_HTML_Properties_ARIA.role("listbox") ])(dropdownContent);
        };
        return Halogen_HTML_Core.text("");
    })() ]);
};
export {
    autoComplete,
    autoCompleteInput,
    suggestionsList,
    suggestionItem,
    suggestion,
    suggestionWithMeta,
    defaultProps,
    suggestions,
    suggestionsWithData,
    value,
    placeholder,
    disabled,
    loading,
    open,
    highlightedIndex,
    minChars,
    maxSuggestions,
    debounceMs,
    clearOnSelect,
    className,
    onInput,
    onSelect,
    onSelectData,
    onOpenChange,
    onHighlightChange,
    renderSuggestion,
    noResultsText,
    loadingText
};
