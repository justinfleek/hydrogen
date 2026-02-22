// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                       // hydrogen // taginput
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | TagInput/MultiSelect component
// |
// | A component for selecting and managing multiple tags or items.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Component.TagInput as TagInput
// |
// | -- Basic tag input
// | TagInput.tagInput
// |   [ TagInput.tags state.selectedTags
// |   , TagInput.onAdd HandleAddTag
// |   , TagInput.onRemove HandleRemoveTag
// |   ]
// |
// | -- With suggestions
// | TagInput.tagInput
// |   [ TagInput.tags state.tags
// |   , TagInput.suggestions availableTags
// |   , TagInput.onAdd HandleAdd
// |   , TagInput.onRemove HandleRemove
// |   ]
// |
// | -- With max tags limit
// | TagInput.tagInput
// |   [ TagInput.tags state.tags
// |   , TagInput.maxTags 5
// |   , TagInput.onAdd HandleAdd
// |   , TagInput.onRemove HandleRemove
// |   ]
// |
// | -- Custom tag rendering
// | TagInput.tagInput
// |   [ TagInput.tagsWithData userTags
// |   , TagInput.renderTag \tag -> HH.div_ [ HH.text tag.label ]
// |   ]
// | ```
import * as DOM_HTML_Indexed_ButtonType from "../DOM.HTML.Indexed.ButtonType/index.js";
import * as DOM_HTML_Indexed_InputType from "../DOM.HTML.Indexed.InputType/index.js";
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Semigroup from "../Data.Semigroup/index.js";
import * as Data_String_Common from "../Data.String.Common/index.js";
import * as Halogen_HTML_Core from "../Halogen.HTML.Core/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Events from "../Halogen.HTML.Events/index.js";
import * as Halogen_HTML_Properties from "../Halogen.HTML.Properties/index.js";
import * as Halogen_HTML_Properties_ARIA from "../Halogen.HTML.Properties.ARIA/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";
import * as Web_UIEvent_KeyboardEvent from "../Web.UIEvent.KeyboardEvent/index.js";
var map = /* #__PURE__ */ Data_Functor.map(Data_Functor.functorArray);
var type_ = /* #__PURE__ */ Halogen_HTML_Properties.type_(Halogen_HTML_Core.isPropButtonType);
var append1 = /* #__PURE__ */ Data_Semigroup.append(Data_Semigroup.semigroupArray);
var type_1 = /* #__PURE__ */ Halogen_HTML_Properties.type_(Halogen_HTML_Core.isPropInputType);
var value = /* #__PURE__ */ Halogen_HTML_Properties.value(Halogen_HTML_Core.isPropString);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // variants
// ═══════════════════════════════════════════════════════════════════════════════
// | Tag visual variants
var Default = /* #__PURE__ */ (function () {
    function Default() {

    };
    Default.value = new Default();
    return Default;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // variants
// ═══════════════════════════════════════════════════════════════════════════════
// | Tag visual variants
var Primary = /* #__PURE__ */ (function () {
    function Primary() {

    };
    Primary.value = new Primary();
    return Primary;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // variants
// ═══════════════════════════════════════════════════════════════════════════════
// | Tag visual variants
var Secondary = /* #__PURE__ */ (function () {
    function Secondary() {

    };
    Secondary.value = new Secondary();
    return Secondary;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // variants
// ═══════════════════════════════════════════════════════════════════════════════
// | Tag visual variants
var Destructive = /* #__PURE__ */ (function () {
    function Destructive() {

    };
    Destructive.value = new Destructive();
    return Destructive;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // variants
// ═══════════════════════════════════════════════════════════════════════════════
// | Tag visual variants
var Outline = /* #__PURE__ */ (function () {
    function Outline() {

    };
    Outline.value = new Outline();
    return Outline;
})();

// | Get variant classes
var variantClasses = function (v) {
    if (v instanceof Default) {
        return "bg-secondary text-secondary-foreground hover:bg-secondary/80";
    };
    if (v instanceof Primary) {
        return "bg-primary text-primary-foreground hover:bg-primary/80";
    };
    if (v instanceof Secondary) {
        return "bg-secondary text-secondary-foreground hover:bg-secondary/80";
    };
    if (v instanceof Destructive) {
        return "bg-destructive text-destructive-foreground hover:bg-destructive/80";
    };
    if (v instanceof Outline) {
        return "border border-input bg-background hover:bg-accent hover:text-accent-foreground";
    };
    throw new Error("Failed pattern match at Hydrogen.Component.TagInput (line 129, column 18 - line 139, column 85): " + [ v.constructor.name ]);
};

// | Set tags with custom data
var tagsWithData = function (ts) {
    return function (props) {
        return {
            suggestions: props.suggestions,
            inputValue: props.inputValue,
            placeholder: props.placeholder,
            disabled: props.disabled,
            maxTags: props.maxTags,
            allowDuplicates: props.allowDuplicates,
            allowCustom: props.allowCustom,
            delimiter: props.delimiter,
            className: props.className,
            tagClassName: props.tagClassName,
            tagVariant: props.tagVariant,
            onAdd: props.onAdd,
            onRemove: props.onRemove,
            onChange: props.onChange,
            onInputChange: props.onInputChange,
            renderTag: props.renderTag,
            tags: ts
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // prop builders
// ═══════════════════════════════════════════════════════════════════════════════
// | Set tags from simple strings
var tags = function (strs) {
    return function (props) {
        return {
            suggestions: props.suggestions,
            inputValue: props.inputValue,
            placeholder: props.placeholder,
            disabled: props.disabled,
            maxTags: props.maxTags,
            allowDuplicates: props.allowDuplicates,
            allowCustom: props.allowCustom,
            delimiter: props.delimiter,
            className: props.className,
            tagClassName: props.tagClassName,
            tagVariant: props.tagVariant,
            onAdd: props.onAdd,
            onRemove: props.onRemove,
            onChange: props.onChange,
            onInputChange: props.onInputChange,
            renderTag: props.renderTag,
            tags: map(function (s) {
                return {
                    value: s,
                    label: s,
                    data: Data_Maybe.Nothing.value,
                    removable: true
                };
            })(strs)
        };
    };
};

// | Create a tag with attached data
var tagWithData = function (val) {
    return function (lbl) {
        return function (d) {
            return {
                value: val,
                label: lbl,
                data: new Data_Maybe.Just(d),
                removable: true
            };
        };
    };
};

// | Set tag variant
var tagVariant = function (v) {
    return function (props) {
        return {
            tags: props.tags,
            suggestions: props.suggestions,
            inputValue: props.inputValue,
            placeholder: props.placeholder,
            disabled: props.disabled,
            maxTags: props.maxTags,
            allowDuplicates: props.allowDuplicates,
            allowCustom: props.allowCustom,
            delimiter: props.delimiter,
            className: props.className,
            tagClassName: props.tagClassName,
            onAdd: props.onAdd,
            onRemove: props.onRemove,
            onChange: props.onChange,
            onInputChange: props.onInputChange,
            renderTag: props.renderTag,
            tagVariant: v
        };
    };
};

// | Add custom class to tags
var tagClassName = function (c) {
    return function (props) {
        return {
            tags: props.tags,
            suggestions: props.suggestions,
            inputValue: props.inputValue,
            placeholder: props.placeholder,
            disabled: props.disabled,
            maxTags: props.maxTags,
            allowDuplicates: props.allowDuplicates,
            allowCustom: props.allowCustom,
            delimiter: props.delimiter,
            className: props.className,
            tagVariant: props.tagVariant,
            onAdd: props.onAdd,
            onRemove: props.onRemove,
            onChange: props.onChange,
            onInputChange: props.onInputChange,
            renderTag: props.renderTag,
            tagClassName: props.tagClassName + (" " + c)
        };
    };
};

// | Tag base classes
var tagBaseClasses = "inline-flex items-center gap-1 rounded-md px-2 py-0.5 text-xs font-medium transition-colors";

// | Set available suggestions
var suggestions = function (sugs) {
    return function (props) {
        return {
            tags: props.tags,
            inputValue: props.inputValue,
            placeholder: props.placeholder,
            disabled: props.disabled,
            maxTags: props.maxTags,
            allowDuplicates: props.allowDuplicates,
            allowCustom: props.allowCustom,
            delimiter: props.delimiter,
            className: props.className,
            tagClassName: props.tagClassName,
            tagVariant: props.tagVariant,
            onAdd: props.onAdd,
            onRemove: props.onRemove,
            onChange: props.onChange,
            onInputChange: props.onInputChange,
            renderTag: props.renderTag,
            suggestions: sugs
        };
    };
};

// | Set custom tag renderer
var renderTag = function (renderer) {
    return function (props) {
        return {
            tags: props.tags,
            suggestions: props.suggestions,
            inputValue: props.inputValue,
            placeholder: props.placeholder,
            disabled: props.disabled,
            maxTags: props.maxTags,
            allowDuplicates: props.allowDuplicates,
            allowCustom: props.allowCustom,
            delimiter: props.delimiter,
            className: props.className,
            tagClassName: props.tagClassName,
            tagVariant: props.tagVariant,
            onAdd: props.onAdd,
            onRemove: props.onRemove,
            onChange: props.onChange,
            onInputChange: props.onInputChange,
            renderTag: new Data_Maybe.Just(renderer)
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // icons
// ═══════════════════════════════════════════════════════════════════════════════
// | Small X icon for remove button
var removeIcon = /* #__PURE__ */ Halogen_HTML_Elements.element("svg")([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "h-3 w-3" ]), /* #__PURE__ */ Halogen_HTML_Properties.attr("xmlns")("http://www.w3.org/2000/svg"), /* #__PURE__ */ Halogen_HTML_Properties.attr("viewBox")("0 0 24 24"), /* #__PURE__ */ Halogen_HTML_Properties.attr("fill")("none"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke")("currentColor"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke-width")("2"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke-linecap")("round"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke-linejoin")("round") ])([ /* #__PURE__ */ Halogen_HTML_Elements.element("line")([ /* #__PURE__ */ Halogen_HTML_Properties.attr("x1")("18"), /* #__PURE__ */ Halogen_HTML_Properties.attr("y1")("6"), /* #__PURE__ */ Halogen_HTML_Properties.attr("x2")("6"), /* #__PURE__ */ Halogen_HTML_Properties.attr("y2")("18") ])([  ]), /* #__PURE__ */ Halogen_HTML_Elements.element("line")([ /* #__PURE__ */ Halogen_HTML_Properties.attr("x1")("6"), /* #__PURE__ */ Halogen_HTML_Properties.attr("y1")("6"), /* #__PURE__ */ Halogen_HTML_Properties.attr("x2")("18"), /* #__PURE__ */ Halogen_HTML_Properties.attr("y2")("18") ])([  ]) ]);

// | Remove button classes
var removeButtonClasses = "ml-1 rounded-full hover:bg-foreground/20 focus:outline-none focus:ring-1 focus:ring-ring";

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // components
// ═══════════════════════════════════════════════════════════════════════════════
// | Render a single tag
var tag = function (opts) {
    return Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ tagBaseClasses, variantClasses(opts.variant), opts.className ]) ])([ Halogen_HTML_Core.text(opts.label), (function () {
        if (opts.removable) {
            if (opts.onRemove instanceof Data_Maybe.Just) {
                return Halogen_HTML_Elements.button([ Hydrogen_UI_Core.cls([ removeButtonClasses ]), type_(DOM_HTML_Indexed_ButtonType.ButtonButton.value), Halogen_HTML_Events.onClick(function (v) {
                    return opts.onRemove.value0;
                }), Halogen_HTML_Properties_ARIA.label("Remove tag") ])([ removeIcon ]);
            };
            if (opts.onRemove instanceof Data_Maybe.Nothing) {
                return Halogen_HTML_Core.text("");
            };
            throw new Error("Failed pattern match at Hydrogen.Component.TagInput (line 310, column 14 - line 319, column 32): " + [ opts.onRemove.constructor.name ]);
        };
        return Halogen_HTML_Core.text("");
    })() ]);
};

// | Render a list of tags (standalone)
var tagList = function (opts) {
    return function (tagStrs) {
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex flex-wrap gap-1.5", opts.className ]) ])(map(function (t) {
            return tag({
                label: t,
                variant: opts.variant,
                removable: false,
                onRemove: Data_Maybe.Nothing.value,
                className: ""
            });
        })(tagStrs));
    };
};

// | Set placeholder text
var placeholder = function (p) {
    return function (props) {
        return {
            tags: props.tags,
            suggestions: props.suggestions,
            inputValue: props.inputValue,
            disabled: props.disabled,
            maxTags: props.maxTags,
            allowDuplicates: props.allowDuplicates,
            allowCustom: props.allowCustom,
            delimiter: props.delimiter,
            className: props.className,
            tagClassName: props.tagClassName,
            tagVariant: props.tagVariant,
            onAdd: props.onAdd,
            onRemove: props.onRemove,
            onChange: props.onChange,
            onInputChange: props.onInputChange,
            renderTag: props.renderTag,
            placeholder: p
        };
    };
};

// | Set remove handler
var onRemove = function (handler) {
    return function (props) {
        return {
            tags: props.tags,
            suggestions: props.suggestions,
            inputValue: props.inputValue,
            placeholder: props.placeholder,
            disabled: props.disabled,
            maxTags: props.maxTags,
            allowDuplicates: props.allowDuplicates,
            allowCustom: props.allowCustom,
            delimiter: props.delimiter,
            className: props.className,
            tagClassName: props.tagClassName,
            tagVariant: props.tagVariant,
            onAdd: props.onAdd,
            onChange: props.onChange,
            onInputChange: props.onInputChange,
            renderTag: props.renderTag,
            onRemove: new Data_Maybe.Just(handler)
        };
    };
};

// | Set input change handler
var onInputChange = function (handler) {
    return function (props) {
        return {
            tags: props.tags,
            suggestions: props.suggestions,
            inputValue: props.inputValue,
            placeholder: props.placeholder,
            disabled: props.disabled,
            maxTags: props.maxTags,
            allowDuplicates: props.allowDuplicates,
            allowCustom: props.allowCustom,
            delimiter: props.delimiter,
            className: props.className,
            tagClassName: props.tagClassName,
            tagVariant: props.tagVariant,
            onAdd: props.onAdd,
            onRemove: props.onRemove,
            onChange: props.onChange,
            renderTag: props.renderTag,
            onInputChange: new Data_Maybe.Just(handler)
        };
    };
};

// | Set change handler (receives full tag array)
var onChange = function (handler) {
    return function (props) {
        return {
            tags: props.tags,
            suggestions: props.suggestions,
            inputValue: props.inputValue,
            placeholder: props.placeholder,
            disabled: props.disabled,
            maxTags: props.maxTags,
            allowDuplicates: props.allowDuplicates,
            allowCustom: props.allowCustom,
            delimiter: props.delimiter,
            className: props.className,
            tagClassName: props.tagClassName,
            tagVariant: props.tagVariant,
            onAdd: props.onAdd,
            onRemove: props.onRemove,
            onInputChange: props.onInputChange,
            renderTag: props.renderTag,
            onChange: new Data_Maybe.Just(handler)
        };
    };
};

// | Set add handler
var onAdd = function (handler) {
    return function (props) {
        return {
            tags: props.tags,
            suggestions: props.suggestions,
            inputValue: props.inputValue,
            placeholder: props.placeholder,
            disabled: props.disabled,
            maxTags: props.maxTags,
            allowDuplicates: props.allowDuplicates,
            allowCustom: props.allowCustom,
            delimiter: props.delimiter,
            className: props.className,
            tagClassName: props.tagClassName,
            tagVariant: props.tagVariant,
            onRemove: props.onRemove,
            onChange: props.onChange,
            onInputChange: props.onInputChange,
            renderTag: props.renderTag,
            onAdd: new Data_Maybe.Just(handler)
        };
    };
};

// | Create a simple tag from a string
var mkTag = function (s) {
    return {
        value: s,
        label: s,
        data: Data_Maybe.Nothing.value,
        removable: true
    };
};

// | Set maximum number of tags
var maxTags = function (n) {
    return function (props) {
        return {
            tags: props.tags,
            suggestions: props.suggestions,
            inputValue: props.inputValue,
            placeholder: props.placeholder,
            disabled: props.disabled,
            allowDuplicates: props.allowDuplicates,
            allowCustom: props.allowCustom,
            delimiter: props.delimiter,
            className: props.className,
            tagClassName: props.tagClassName,
            tagVariant: props.tagVariant,
            onAdd: props.onAdd,
            onRemove: props.onRemove,
            onChange: props.onChange,
            onInputChange: props.onInputChange,
            renderTag: props.renderTag,
            maxTags: new Data_Maybe.Just(n)
        };
    };
};

// | Set current input value
var inputValue = function (v) {
    return function (props) {
        return {
            tags: props.tags,
            suggestions: props.suggestions,
            placeholder: props.placeholder,
            disabled: props.disabled,
            maxTags: props.maxTags,
            allowDuplicates: props.allowDuplicates,
            allowCustom: props.allowCustom,
            delimiter: props.delimiter,
            className: props.className,
            tagClassName: props.tagClassName,
            tagVariant: props.tagVariant,
            onAdd: props.onAdd,
            onRemove: props.onRemove,
            onChange: props.onChange,
            onInputChange: props.onInputChange,
            renderTag: props.renderTag,
            inputValue: v
        };
    };
};

// | Input classes
var inputClasses = "flex-1 min-w-[120px] bg-transparent outline-none placeholder:text-muted-foreground disabled:cursor-not-allowed";
var eqTagVariant = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Default && y instanceof Default) {
                return true;
            };
            if (x instanceof Primary && y instanceof Primary) {
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
            return false;
        };
    }
};

// | Set disabled state
var disabled = function (d) {
    return function (props) {
        return {
            tags: props.tags,
            suggestions: props.suggestions,
            inputValue: props.inputValue,
            placeholder: props.placeholder,
            maxTags: props.maxTags,
            allowDuplicates: props.allowDuplicates,
            allowCustom: props.allowCustom,
            delimiter: props.delimiter,
            className: props.className,
            tagClassName: props.tagClassName,
            tagVariant: props.tagVariant,
            onAdd: props.onAdd,
            onRemove: props.onRemove,
            onChange: props.onChange,
            onInputChange: props.onInputChange,
            renderTag: props.renderTag,
            disabled: d
        };
    };
};

// | Set delimiter for splitting input
var delimiter = function (d) {
    return function (props) {
        return {
            tags: props.tags,
            suggestions: props.suggestions,
            inputValue: props.inputValue,
            placeholder: props.placeholder,
            disabled: props.disabled,
            maxTags: props.maxTags,
            allowDuplicates: props.allowDuplicates,
            allowCustom: props.allowCustom,
            className: props.className,
            tagClassName: props.tagClassName,
            tagVariant: props.tagVariant,
            onAdd: props.onAdd,
            onRemove: props.onRemove,
            onChange: props.onChange,
            onInputChange: props.onInputChange,
            renderTag: props.renderTag,
            delimiter: d
        };
    };
};

// | Default properties
var defaultProps = /* #__PURE__ */ (function () {
    return {
        tags: [  ],
        suggestions: [  ],
        inputValue: "",
        placeholder: "Add tags...",
        disabled: false,
        maxTags: Data_Maybe.Nothing.value,
        allowDuplicates: false,
        allowCustom: true,
        delimiter: ",",
        className: "",
        tagClassName: "",
        tagVariant: Default.value,
        onAdd: Data_Maybe.Nothing.value,
        onRemove: Data_Maybe.Nothing.value,
        onChange: Data_Maybe.Nothing.value,
        onInputChange: Data_Maybe.Nothing.value,
        renderTag: Data_Maybe.Nothing.value
    };
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // styling
// ═══════════════════════════════════════════════════════════════════════════════
// | Container classes
var containerClasses = "flex flex-wrap items-center gap-1.5 rounded-md border border-input bg-background px-3 py-2 text-sm ring-offset-background focus-within:ring-2 focus-within:ring-ring focus-within:ring-offset-2";

// | Full TagInput component
var tagInput = function (propMods) {
    var props = Data_Array.foldl(function (p) {
        return function (f) {
            return f(p);
        };
    })(defaultProps)(propMods);
    var keyHandler = (function () {
        if (props.onAdd instanceof Data_Maybe.Just) {
            return [ Halogen_HTML_Events.onKeyDown(function (e) {
                var $40 = Web_UIEvent_KeyboardEvent.key(e) === "Enter" || Web_UIEvent_KeyboardEvent.key(e) === props.delimiter;
                if ($40) {
                    return props.onAdd.value0(Data_String_Common.trim(props.inputValue));
                };
                return props.onAdd.value0("");
            }) ];
        };
        if (props.onAdd instanceof Data_Maybe.Nothing) {
            return [  ];
        };
        throw new Error("Failed pattern match at Hydrogen.Component.TagInput (line 380, column 18 - line 388, column 20): " + [ props.onAdd.constructor.name ]);
    })();
    
    // Input handlers
var inputChangeHandler = (function () {
        if (props.onInputChange instanceof Data_Maybe.Just) {
            return [ Halogen_HTML_Events.onValueInput(props.onInputChange.value0) ];
        };
        if (props.onInputChange instanceof Data_Maybe.Nothing) {
            return [  ];
        };
        throw new Error("Failed pattern match at Hydrogen.Component.TagInput (line 376, column 26 - line 378, column 20): " + [ props.onInputChange.constructor.name ]);
    })();
    
    // Container disabled styling
var disabledClass = (function () {
        if (props.disabled) {
            return "opacity-50 cursor-not-allowed";
        };
        return "";
    })();
    
    // Default tag renderer
var defaultRenderer = function (t) {
        var removeHandler = (function () {
            if (props.onRemove instanceof Data_Maybe.Just) {
                return new Data_Maybe.Just(props.onRemove.value0(t.value));
            };
            if (props.onRemove instanceof Data_Maybe.Nothing) {
                return Data_Maybe.Nothing.value;
            };
            throw new Error("Failed pattern match at Hydrogen.Component.TagInput (line 359, column 25 - line 361, column 29): " + [ props.onRemove.constructor.name ]);
        })();
        return tag({
            label: t.label,
            variant: props.tagVariant,
            removable: t.removable && !props.disabled,
            onRemove: removeHandler,
            className: props.tagClassName
        });
    };
    
    // Render all tags
var renderedTags = map(defaultRenderer)(props.tags);
    
    // Check if max tags reached
var atMaxTags = (function () {
        if (props.maxTags instanceof Data_Maybe.Just) {
            return Data_Array.length(props.tags) >= props.maxTags.value0;
        };
        if (props.maxTags instanceof Data_Maybe.Nothing) {
            return false;
        };
        throw new Error("Failed pattern match at Hydrogen.Component.TagInput (line 348, column 17 - line 350, column 23): " + [ props.maxTags.constructor.name ]);
    })();
    
    // Disabled state (explicit or at max)
var isDisabled = props.disabled || atMaxTags;
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ containerClasses, disabledClass, props.className ]), Halogen_HTML_Properties_ARIA.role("listbox"), Halogen_HTML_Properties_ARIA.label("Selected tags") ])(append1(renderedTags)([ Halogen_HTML_Elements.input(append1([ Hydrogen_UI_Core.cls([ inputClasses ]), type_1(DOM_HTML_Indexed_InputType.InputText.value), Halogen_HTML_Properties.placeholder((function () {
        if (atMaxTags) {
            return "Max tags reached";
        };
        return props.placeholder;
    })()), value(props.inputValue), Halogen_HTML_Properties.disabled(isDisabled), Halogen_HTML_Properties_ARIA.label("Add tag") ])(append1(inputChangeHandler)(keyHandler))) ]));
};

// | Add custom class to container
var className = function (c) {
    return function (props) {
        return {
            tags: props.tags,
            suggestions: props.suggestions,
            inputValue: props.inputValue,
            placeholder: props.placeholder,
            disabled: props.disabled,
            maxTags: props.maxTags,
            allowDuplicates: props.allowDuplicates,
            allowCustom: props.allowCustom,
            delimiter: props.delimiter,
            tagClassName: props.tagClassName,
            tagVariant: props.tagVariant,
            onAdd: props.onAdd,
            onRemove: props.onRemove,
            onChange: props.onChange,
            onInputChange: props.onInputChange,
            renderTag: props.renderTag,
            className: props.className + (" " + c)
        };
    };
};

// | Allow duplicate tags
var allowDuplicates = function (a) {
    return function (props) {
        return {
            tags: props.tags,
            suggestions: props.suggestions,
            inputValue: props.inputValue,
            placeholder: props.placeholder,
            disabled: props.disabled,
            maxTags: props.maxTags,
            allowCustom: props.allowCustom,
            delimiter: props.delimiter,
            className: props.className,
            tagClassName: props.tagClassName,
            tagVariant: props.tagVariant,
            onAdd: props.onAdd,
            onRemove: props.onRemove,
            onChange: props.onChange,
            onInputChange: props.onInputChange,
            renderTag: props.renderTag,
            allowDuplicates: a
        };
    };
};

// | Allow custom tags (not from suggestions)
var allowCustom = function (a) {
    return function (props) {
        return {
            tags: props.tags,
            suggestions: props.suggestions,
            inputValue: props.inputValue,
            placeholder: props.placeholder,
            disabled: props.disabled,
            maxTags: props.maxTags,
            allowDuplicates: props.allowDuplicates,
            delimiter: props.delimiter,
            className: props.className,
            tagClassName: props.tagClassName,
            tagVariant: props.tagVariant,
            onAdd: props.onAdd,
            onRemove: props.onRemove,
            onChange: props.onChange,
            onInputChange: props.onInputChange,
            renderTag: props.renderTag,
            allowCustom: a
        };
    };
};
export {
    tagInput,
    tag,
    tagList,
    mkTag,
    tagWithData,
    defaultProps,
    tags,
    tagsWithData,
    suggestions,
    inputValue,
    placeholder,
    disabled,
    maxTags,
    allowDuplicates,
    allowCustom,
    delimiter,
    className,
    tagClassName,
    onAdd,
    onRemove,
    onChange,
    onInputChange,
    renderTag,
    Default,
    Primary,
    Secondary,
    Destructive,
    Outline,
    tagVariant,
    eqTagVariant
};
