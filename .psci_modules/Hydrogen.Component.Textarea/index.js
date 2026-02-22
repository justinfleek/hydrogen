// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                       // hydrogen // textarea
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Enhanced Textarea component
// |
// | A feature-rich textarea with auto-resize, character counting,
// | and validation states.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Component.Textarea as Textarea
// |
// | -- Basic textarea
// | Textarea.textarea [ Textarea.placeholder "Enter your message..." ]
// |
// | -- With auto-resize
// | Textarea.textarea
// |   [ Textarea.autoResize true
// |   , Textarea.minRows 3
// |   , Textarea.maxRows 10
// |   ]
// |
// | -- With character limit
// | Textarea.textareaWithCounter
// |   [ Textarea.maxLength 500
// |   , Textarea.value state.message
// |   ]
// |
// | -- With label and error state
// | Textarea.textareaWithLabel "Description"
// |   [ Textarea.error true
// |   , Textarea.errorMessage "Description is required"
// |   , Textarea.required true
// |   ]
// |
// | -- Disabled/readonly states
// | Textarea.textarea [ Textarea.disabled true ]
// | Textarea.textarea [ Textarea.readOnly true ]
// | ```
import * as Data_Array from "../Data.Array/index.js";
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
var append1 = /* #__PURE__ */ Data_Semigroup.append(Data_Semigroup.semigroupArray);
var value1 = /* #__PURE__ */ Halogen_HTML_Properties.value(Halogen_HTML_Core.isPropString);
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // prop builders
// ═══════════════════════════════════════════════════════════════════════════════
// | Set value
var value = function (v) {
    return function (props) {
        return {
            placeholder: props.placeholder,
            disabled: props.disabled,
            readOnly: props.readOnly,
            required: props.required,
            autoResize: props.autoResize,
            minRows: props.minRows,
            maxRows: props.maxRows,
            maxLength: props.maxLength,
            error: props.error,
            errorMessage: props.errorMessage,
            className: props.className,
            id: props.id,
            name: props.name,
            onInput: props.onInput,
            onChange: props.onChange,
            onFocus: props.onFocus,
            onBlur: props.onBlur,
            value: v
        };
    };
};

// | Set required state
var required = function (r) {
    return function (props) {
        return {
            value: props.value,
            placeholder: props.placeholder,
            disabled: props.disabled,
            readOnly: props.readOnly,
            autoResize: props.autoResize,
            minRows: props.minRows,
            maxRows: props.maxRows,
            maxLength: props.maxLength,
            error: props.error,
            errorMessage: props.errorMessage,
            className: props.className,
            id: props.id,
            name: props.name,
            onInput: props.onInput,
            onChange: props.onChange,
            onFocus: props.onFocus,
            onBlur: props.onBlur,
            required: r
        };
    };
};

// | Set read-only state
var readOnly = function (r) {
    return function (props) {
        return {
            value: props.value,
            placeholder: props.placeholder,
            disabled: props.disabled,
            required: props.required,
            autoResize: props.autoResize,
            minRows: props.minRows,
            maxRows: props.maxRows,
            maxLength: props.maxLength,
            error: props.error,
            errorMessage: props.errorMessage,
            className: props.className,
            id: props.id,
            name: props.name,
            onInput: props.onInput,
            onChange: props.onChange,
            onFocus: props.onFocus,
            onBlur: props.onBlur,
            readOnly: r
        };
    };
};

// | Set placeholder
var placeholder = function (p) {
    return function (props) {
        return {
            value: props.value,
            disabled: props.disabled,
            readOnly: props.readOnly,
            required: props.required,
            autoResize: props.autoResize,
            minRows: props.minRows,
            maxRows: props.maxRows,
            maxLength: props.maxLength,
            error: props.error,
            errorMessage: props.errorMessage,
            className: props.className,
            id: props.id,
            name: props.name,
            onInput: props.onInput,
            onChange: props.onChange,
            onFocus: props.onFocus,
            onBlur: props.onBlur,
            placeholder: p
        };
    };
};

// | Set input handler
var onInput = function (handler) {
    return function (props) {
        return {
            value: props.value,
            placeholder: props.placeholder,
            disabled: props.disabled,
            readOnly: props.readOnly,
            required: props.required,
            autoResize: props.autoResize,
            minRows: props.minRows,
            maxRows: props.maxRows,
            maxLength: props.maxLength,
            error: props.error,
            errorMessage: props.errorMessage,
            className: props.className,
            id: props.id,
            name: props.name,
            onChange: props.onChange,
            onFocus: props.onFocus,
            onBlur: props.onBlur,
            onInput: new Data_Maybe.Just(handler)
        };
    };
};

// | Set focus handler
var onFocus = function (handler) {
    return function (props) {
        return {
            value: props.value,
            placeholder: props.placeholder,
            disabled: props.disabled,
            readOnly: props.readOnly,
            required: props.required,
            autoResize: props.autoResize,
            minRows: props.minRows,
            maxRows: props.maxRows,
            maxLength: props.maxLength,
            error: props.error,
            errorMessage: props.errorMessage,
            className: props.className,
            id: props.id,
            name: props.name,
            onInput: props.onInput,
            onChange: props.onChange,
            onBlur: props.onBlur,
            onFocus: new Data_Maybe.Just(handler)
        };
    };
};

// | Set change handler
var onChange = function (handler) {
    return function (props) {
        return {
            value: props.value,
            placeholder: props.placeholder,
            disabled: props.disabled,
            readOnly: props.readOnly,
            required: props.required,
            autoResize: props.autoResize,
            minRows: props.minRows,
            maxRows: props.maxRows,
            maxLength: props.maxLength,
            error: props.error,
            errorMessage: props.errorMessage,
            className: props.className,
            id: props.id,
            name: props.name,
            onInput: props.onInput,
            onFocus: props.onFocus,
            onBlur: props.onBlur,
            onChange: new Data_Maybe.Just(handler)
        };
    };
};

// | Set blur handler
var onBlur = function (handler) {
    return function (props) {
        return {
            value: props.value,
            placeholder: props.placeholder,
            disabled: props.disabled,
            readOnly: props.readOnly,
            required: props.required,
            autoResize: props.autoResize,
            minRows: props.minRows,
            maxRows: props.maxRows,
            maxLength: props.maxLength,
            error: props.error,
            errorMessage: props.errorMessage,
            className: props.className,
            id: props.id,
            name: props.name,
            onInput: props.onInput,
            onChange: props.onChange,
            onFocus: props.onFocus,
            onBlur: new Data_Maybe.Just(handler)
        };
    };
};

// | Set name
var name = function (n) {
    return function (props) {
        return {
            value: props.value,
            placeholder: props.placeholder,
            disabled: props.disabled,
            readOnly: props.readOnly,
            required: props.required,
            autoResize: props.autoResize,
            minRows: props.minRows,
            maxRows: props.maxRows,
            maxLength: props.maxLength,
            error: props.error,
            errorMessage: props.errorMessage,
            className: props.className,
            id: props.id,
            onInput: props.onInput,
            onChange: props.onChange,
            onFocus: props.onFocus,
            onBlur: props.onBlur,
            name: new Data_Maybe.Just(n)
        };
    };
};

// | Set minimum rows (for auto-resize)
var minRows = function (r) {
    return function (props) {
        return {
            value: props.value,
            placeholder: props.placeholder,
            disabled: props.disabled,
            readOnly: props.readOnly,
            required: props.required,
            autoResize: props.autoResize,
            maxRows: props.maxRows,
            maxLength: props.maxLength,
            error: props.error,
            errorMessage: props.errorMessage,
            className: props.className,
            id: props.id,
            name: props.name,
            onInput: props.onInput,
            onChange: props.onChange,
            onFocus: props.onFocus,
            onBlur: props.onBlur,
            minRows: r
        };
    };
};
var maybeHandler = function (v) {
    return function (v1) {
        if (v1 instanceof Data_Maybe.Nothing) {
            return [  ];
        };
        if (v1 instanceof Data_Maybe.Just) {
            return [ v(v1.value0) ];
        };
        throw new Error("Failed pattern match at Hydrogen.Component.Textarea (line 369, column 1 - line 369, column 105): " + [ v.constructor.name, v1.constructor.name ]);
    };
};
var maybeFocusHandler = function (v) {
    return function (v1) {
        if (v1 instanceof Data_Maybe.Nothing) {
            return [  ];
        };
        if (v1 instanceof Data_Maybe.Just) {
            return [ v(v1.value0) ];
        };
        throw new Error("Failed pattern match at Hydrogen.Component.Textarea (line 373, column 1 - line 373, column 120): " + [ v.constructor.name, v1.constructor.name ]);
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // helpers
// ═══════════════════════════════════════════════════════════════════════════════
var maybeAttr = function (v) {
    return function (v1) {
        if (v1 instanceof Data_Maybe.Nothing) {
            return [  ];
        };
        if (v1 instanceof Data_Maybe.Just) {
            return [ v(v1.value0) ];
        };
        throw new Error("Failed pattern match at Hydrogen.Component.Textarea (line 365, column 1 - line 365, column 82): " + [ v.constructor.name, v1.constructor.name ]);
    };
};

// | Set maximum rows (for auto-resize)
var maxRows = function (r) {
    return function (props) {
        return {
            value: props.value,
            placeholder: props.placeholder,
            disabled: props.disabled,
            readOnly: props.readOnly,
            required: props.required,
            autoResize: props.autoResize,
            minRows: props.minRows,
            maxLength: props.maxLength,
            error: props.error,
            errorMessage: props.errorMessage,
            className: props.className,
            id: props.id,
            name: props.name,
            onInput: props.onInput,
            onChange: props.onChange,
            onFocus: props.onFocus,
            onBlur: props.onBlur,
            maxRows: r
        };
    };
};

// | Set maximum character length
var maxLength = function (l) {
    return function (props) {
        return {
            value: props.value,
            placeholder: props.placeholder,
            disabled: props.disabled,
            readOnly: props.readOnly,
            required: props.required,
            autoResize: props.autoResize,
            minRows: props.minRows,
            maxRows: props.maxRows,
            error: props.error,
            errorMessage: props.errorMessage,
            className: props.className,
            id: props.id,
            name: props.name,
            onInput: props.onInput,
            onChange: props.onChange,
            onFocus: props.onFocus,
            onBlur: props.onBlur,
            maxLength: new Data_Maybe.Just(l)
        };
    };
};

// | Set id
var id = function (i) {
    return function (props) {
        return {
            value: props.value,
            placeholder: props.placeholder,
            disabled: props.disabled,
            readOnly: props.readOnly,
            required: props.required,
            autoResize: props.autoResize,
            minRows: props.minRows,
            maxRows: props.maxRows,
            maxLength: props.maxLength,
            error: props.error,
            errorMessage: props.errorMessage,
            className: props.className,
            name: props.name,
            onInput: props.onInput,
            onChange: props.onChange,
            onFocus: props.onFocus,
            onBlur: props.onBlur,
            id: new Data_Maybe.Just(i)
        };
    };
};

// | Set error message
var errorMessage = function (msg) {
    return function (props) {
        return {
            value: props.value,
            placeholder: props.placeholder,
            disabled: props.disabled,
            readOnly: props.readOnly,
            required: props.required,
            autoResize: props.autoResize,
            minRows: props.minRows,
            maxRows: props.maxRows,
            maxLength: props.maxLength,
            className: props.className,
            id: props.id,
            name: props.name,
            onInput: props.onInput,
            onChange: props.onChange,
            onFocus: props.onFocus,
            onBlur: props.onBlur,
            errorMessage: msg,
            error: true
        };
    };
};

// | Error state classes
var errorClasses = "border-destructive focus-visible:ring-destructive";

// | Set error state
var error = function (e) {
    return function (props) {
        return {
            value: props.value,
            placeholder: props.placeholder,
            disabled: props.disabled,
            readOnly: props.readOnly,
            required: props.required,
            autoResize: props.autoResize,
            minRows: props.minRows,
            maxRows: props.maxRows,
            maxLength: props.maxLength,
            errorMessage: props.errorMessage,
            className: props.className,
            id: props.id,
            name: props.name,
            onInput: props.onInput,
            onChange: props.onChange,
            onFocus: props.onFocus,
            onBlur: props.onBlur,
            error: e
        };
    };
};

// | Set disabled state
var disabled = function (d) {
    return function (props) {
        return {
            value: props.value,
            placeholder: props.placeholder,
            readOnly: props.readOnly,
            required: props.required,
            autoResize: props.autoResize,
            minRows: props.minRows,
            maxRows: props.maxRows,
            maxLength: props.maxLength,
            error: props.error,
            errorMessage: props.errorMessage,
            className: props.className,
            id: props.id,
            name: props.name,
            onInput: props.onInput,
            onChange: props.onChange,
            onFocus: props.onFocus,
            onBlur: props.onBlur,
            disabled: d
        };
    };
};

// | Default textarea properties
var defaultProps = /* #__PURE__ */ (function () {
    return {
        value: "",
        placeholder: "",
        disabled: false,
        readOnly: false,
        required: false,
        autoResize: false,
        minRows: 3,
        maxRows: 10,
        maxLength: Data_Maybe.Nothing.value,
        error: false,
        errorMessage: "",
        className: "",
        id: Data_Maybe.Nothing.value,
        name: Data_Maybe.Nothing.value,
        onInput: Data_Maybe.Nothing.value,
        onChange: Data_Maybe.Nothing.value,
        onFocus: Data_Maybe.Nothing.value,
        onBlur: Data_Maybe.Nothing.value
    };
})();

// | Add custom class
var className = function (c) {
    return function (props) {
        return {
            value: props.value,
            placeholder: props.placeholder,
            disabled: props.disabled,
            readOnly: props.readOnly,
            required: props.required,
            autoResize: props.autoResize,
            minRows: props.minRows,
            maxRows: props.maxRows,
            maxLength: props.maxLength,
            error: props.error,
            errorMessage: props.errorMessage,
            id: props.id,
            name: props.name,
            onInput: props.onInput,
            onChange: props.onChange,
            onFocus: props.onFocus,
            onBlur: props.onBlur,
            className: props.className + (" " + c)
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // components
// ═══════════════════════════════════════════════════════════════════════════════
// | Base textarea classes
var baseClasses = "flex min-h-[80px] w-full rounded-md border border-input bg-background px-3 py-2 text-sm ring-offset-background placeholder:text-muted-foreground focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2 disabled:cursor-not-allowed disabled:opacity-50";

// | Render a textarea
var textarea = function (propMods) {
    var props = Data_Array.foldl(function (p) {
        return function (f) {
            return f(p);
        };
    })(defaultProps)(propMods);
    var resizeClass = (function () {
        if (props.autoResize) {
            return "resize-none overflow-hidden";
        };
        return "resize-y";
    })();
    var errorClass = (function () {
        if (props.error) {
            return errorClasses;
        };
        return "";
    })();
    return Halogen_HTML_Elements.textarea(append1([ Hydrogen_UI_Core.cls([ baseClasses, errorClass, resizeClass, props.className ]), Halogen_HTML_Properties.placeholder(props.placeholder), value1(props.value), Halogen_HTML_Properties.disabled(props.disabled), Halogen_HTML_Properties.readOnly(props.readOnly), Halogen_HTML_Properties.required(props.required), Halogen_HTML_Properties.rows(props.minRows) ])(append1(maybeAttr(Halogen_HTML_Properties.id)(props.id))(append1(maybeAttr(Halogen_HTML_Properties.name)(props.name))(append1((function () {
        if (props.maxLength instanceof Data_Maybe.Just) {
            return [ Halogen_HTML_Properties.attr("maxlength")(show(props.maxLength.value0)) ];
        };
        if (props.maxLength instanceof Data_Maybe.Nothing) {
            return [  ];
        };
        throw new Error("Failed pattern match at Hydrogen.Component.Textarea (line 247, column 12 - line 249, column 26): " + [ props.maxLength.constructor.name ]);
    })())(append1((function () {
        if (props.error) {
            return [ Halogen_HTML_Properties_ARIA.invalid("true") ];
        };
        if (!props.error) {
            return [  ];
        };
        throw new Error("Failed pattern match at Hydrogen.Component.Textarea (line 250, column 12 - line 252, column 24): " + [ props.error.constructor.name ]);
    })())(append1(maybeHandler(Halogen_HTML_Events.onInput)(props.onInput))(append1(maybeHandler(Halogen_HTML_Events.onChange)(props.onChange))(append1(maybeFocusHandler(Halogen_HTML_Events.onFocus)(props.onFocus))(maybeFocusHandler(Halogen_HTML_Events.onBlur)(props.onBlur))))))))));
};

// | Full textarea field (label + textarea + counter + error)
var textareaField = function (labelText) {
    return function (propMods) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        var inputId = (function () {
            if (props.id instanceof Data_Maybe.Just) {
                return props.id.value0;
            };
            if (props.id instanceof Data_Maybe.Nothing) {
                return "textarea-" + labelText;
            };
            throw new Error("Failed pattern match at Hydrogen.Component.Textarea (line 318, column 15 - line 320, column 42): " + [ props.id.constructor.name ]);
        })();
        var propsWithId = append1(propMods)([ id(inputId) ]);
        var currentLength = Data_String_CodePoints.length(props.value);
        var isOverLimit = (function () {
            if (props.maxLength instanceof Data_Maybe.Just) {
                return currentLength > props.maxLength.value0;
            };
            if (props.maxLength instanceof Data_Maybe.Nothing) {
                return false;
            };
            throw new Error("Failed pattern match at Hydrogen.Component.Textarea (line 326, column 19 - line 328, column 23): " + [ props.maxLength.constructor.name ]);
        })();
        var counterText = (function () {
            if (props.maxLength instanceof Data_Maybe.Just) {
                return show(currentLength) + (" / " + show(props.maxLength.value0));
            };
            if (props.maxLength instanceof Data_Maybe.Nothing) {
                return "";
            };
            throw new Error("Failed pattern match at Hydrogen.Component.Textarea (line 323, column 19 - line 325, column 20): " + [ props.maxLength.constructor.name ]);
        })();
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "space-y-2" ]) ])([ Halogen_HTML_Elements.label([ Hydrogen_UI_Core.cls([ "text-sm font-medium leading-none peer-disabled:cursor-not-allowed peer-disabled:opacity-70" ]), Halogen_HTML_Properties["for"](inputId) ])([ Halogen_HTML_Core.text(labelText), (function () {
            if (props.required) {
                return Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "text-destructive ml-1" ]) ])([ Halogen_HTML_Core.text("*") ]);
            };
            return Halogen_HTML_Core.text("");
        })() ]), textarea(propsWithId), Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex justify-between" ]) ])([ (function () {
            var $52 = props.error && props.errorMessage !== "";
            if ($52) {
                return Halogen_HTML_Elements.p([ Hydrogen_UI_Core.cls([ "text-sm text-destructive" ]) ])([ Halogen_HTML_Core.text(props.errorMessage) ]);
            };
            return Halogen_HTML_Core.text("");
        })(), (function () {
            if (props.maxLength instanceof Data_Maybe.Just) {
                return Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "text-xs", (function () {
                    if (isOverLimit) {
                        return "text-destructive";
                    };
                    return "text-muted-foreground";
                })() ]) ])([ Halogen_HTML_Core.text(counterText) ]);
            };
            if (props.maxLength instanceof Data_Maybe.Nothing) {
                return Halogen_HTML_Core.text("");
            };
            throw new Error("Failed pattern match at Hydrogen.Component.Textarea (line 352, column 13 - line 357, column 36): " + [ props.maxLength.constructor.name ]);
        })() ]) ]);
    };
};

// | Textarea with character counter
var textareaWithCounter = function (propMods) {
    var props = Data_Array.foldl(function (p) {
        return function (f) {
            return f(p);
        };
    })(defaultProps)(propMods);
    var currentLength = Data_String_CodePoints.length(props.value);
    var isOverLimit = (function () {
        if (props.maxLength instanceof Data_Maybe.Just) {
            return currentLength > props.maxLength.value0;
        };
        if (props.maxLength instanceof Data_Maybe.Nothing) {
            return false;
        };
        throw new Error("Failed pattern match at Hydrogen.Component.Textarea (line 297, column 19 - line 299, column 23): " + [ props.maxLength.constructor.name ]);
    })();
    var counterText = (function () {
        if (props.maxLength instanceof Data_Maybe.Just) {
            return show(currentLength) + (" / " + show(props.maxLength.value0));
        };
        if (props.maxLength instanceof Data_Maybe.Nothing) {
            return show(currentLength) + " characters";
        };
        throw new Error("Failed pattern match at Hydrogen.Component.Textarea (line 294, column 19 - line 296, column 53): " + [ props.maxLength.constructor.name ]);
    })();
    var counterClass = (function () {
        if (isOverLimit) {
            return "text-destructive";
        };
        return "text-muted-foreground";
    })();
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "space-y-1" ]) ])([ textarea(propMods), Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex justify-end" ]) ])([ Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "text-xs", counterClass ]) ])([ Halogen_HTML_Core.text(counterText) ]) ]) ]);
};

// | Textarea with label
var textareaWithLabel = function (labelText) {
    return function (propMods) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        var inputId = (function () {
            if (props.id instanceof Data_Maybe.Just) {
                return props.id.value0;
            };
            if (props.id instanceof Data_Maybe.Nothing) {
                return "textarea-" + labelText;
            };
            throw new Error("Failed pattern match at Hydrogen.Component.Textarea (line 264, column 15 - line 266, column 42): " + [ props.id.constructor.name ]);
        })();
        var propsWithId = append1(propMods)([ id(inputId) ]);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "space-y-2" ]) ])([ Halogen_HTML_Elements.label([ Hydrogen_UI_Core.cls([ "text-sm font-medium leading-none peer-disabled:cursor-not-allowed peer-disabled:opacity-70" ]), Halogen_HTML_Properties["for"](inputId) ])([ Halogen_HTML_Core.text(labelText), (function () {
            if (props.required) {
                return Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "text-destructive ml-1" ]) ])([ Halogen_HTML_Core.text("*") ]);
            };
            return Halogen_HTML_Core.text("");
        })() ]), textarea(propsWithId), (function () {
            var $64 = props.error && props.errorMessage !== "";
            if ($64) {
                return Halogen_HTML_Elements.p([ Hydrogen_UI_Core.cls([ "text-sm text-destructive" ]) ])([ Halogen_HTML_Core.text(props.errorMessage) ]);
            };
            return Halogen_HTML_Core.text("");
        })() ]);
    };
};

// | Enable auto-resize to content
var autoResize = function (a) {
    return function (props) {
        return {
            value: props.value,
            placeholder: props.placeholder,
            disabled: props.disabled,
            readOnly: props.readOnly,
            required: props.required,
            minRows: props.minRows,
            maxRows: props.maxRows,
            maxLength: props.maxLength,
            error: props.error,
            errorMessage: props.errorMessage,
            className: props.className,
            id: props.id,
            name: props.name,
            onInput: props.onInput,
            onChange: props.onChange,
            onFocus: props.onFocus,
            onBlur: props.onBlur,
            autoResize: a
        };
    };
};
export {
    textarea,
    textareaWithLabel,
    textareaWithCounter,
    textareaField,
    defaultProps,
    value,
    placeholder,
    disabled,
    readOnly,
    required,
    autoResize,
    minRows,
    maxRows,
    maxLength,
    error,
    errorMessage,
    className,
    id,
    name,
    onInput,
    onChange,
    onFocus,
    onBlur
};
