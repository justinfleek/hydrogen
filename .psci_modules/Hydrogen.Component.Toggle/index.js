// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                         // hydrogen // toggle
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Toggle button component
// |
// | Toggle buttons for binary or multi-selection states with
// | visual feedback for pressed state.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Component.Toggle as Toggle
// |
// | -- Single toggle button
// | Toggle.toggle
// |   [ Toggle.pressed state.isBold
// |   , Toggle.onPressedChange HandleBoldToggle
// |   ]
// |   [ Icon.bold [], HH.text "Bold" ]
// |
// | -- Toggle with variants
// | Toggle.toggle
// |   [ Toggle.variant Outline
// |   , Toggle.size Lg
// |   ]
// |   [ HH.text "Option" ]
// |
// | -- Toggle group (single selection)
// | Toggle.toggleGroup
// |   [ Toggle.groupType Single
// |   , Toggle.groupValue "left"
// |   , Toggle.onGroupValueChange HandleAlignment
// |   ]
// |   [ Toggle.toggleItem "left" [ Icon.alignLeft [] ]
// |   , Toggle.toggleItem "center" [ Icon.alignCenter [] ]
// |   , Toggle.toggleItem "right" [ Icon.alignRight [] ]
// |   ]
// |
// | -- Toggle group (multiple selection)
// | Toggle.toggleGroup
// |   [ Toggle.groupType Multiple
// |   , Toggle.groupValues ["bold", "italic"]
// |   , Toggle.onGroupValuesChange HandleFormatting
// |   ]
// |   [ Toggle.toggleItem "bold" [ Icon.bold [] ]
// |   , Toggle.toggleItem "italic" [ Icon.italic [] ]
// |   , Toggle.toggleItem "underline" [ Icon.underline [] ]
// |   ]
// | ```
import * as DOM_HTML_Indexed_ButtonType from "../DOM.HTML.Indexed.ButtonType/index.js";
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
var append1 = /* #__PURE__ */ Data_Semigroup.append(Data_Semigroup.semigroupArray);
var type_ = /* #__PURE__ */ Halogen_HTML_Properties.type_(Halogen_HTML_Core.isPropButtonType);
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showBoolean);
var value = /* #__PURE__ */ Halogen_HTML_Properties.value(Halogen_HTML_Core.isPropString);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Toggle visual variant
var Default = /* #__PURE__ */ (function () {
    function Default() {

    };
    Default.value = new Default();
    return Default;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Toggle visual variant
var Outline = /* #__PURE__ */ (function () {
    function Outline() {

    };
    Outline.value = new Outline();
    return Outline;
})();

// | Toggle size
var Sm = /* #__PURE__ */ (function () {
    function Sm() {

    };
    Sm.value = new Sm();
    return Sm;
})();

// | Toggle size
var Md = /* #__PURE__ */ (function () {
    function Md() {

    };
    Md.value = new Md();
    return Md;
})();

// | Toggle size
var Lg = /* #__PURE__ */ (function () {
    function Lg() {

    };
    Lg.value = new Lg();
    return Lg;
})();

// | Toggle group selection type
var Single = /* #__PURE__ */ (function () {
    function Single() {

    };
    Single.value = new Single();
    return Single;
})();

// | Toggle group selection type
var Multiple = /* #__PURE__ */ (function () {
    function Multiple() {

    };
    Multiple.value = new Multiple();
    return Multiple;
})();

// | Get variant classes
var variantClasses = function (v) {
    if (v instanceof Default) {
        return "bg-transparent hover:bg-muted hover:text-muted-foreground data-[state=on]:bg-accent data-[state=on]:text-accent-foreground";
    };
    if (v instanceof Outline) {
        return "border border-input bg-transparent hover:bg-accent hover:text-accent-foreground data-[state=on]:bg-accent data-[state=on]:text-accent-foreground";
    };
    throw new Error("Failed pattern match at Hydrogen.Component.Toggle (line 121, column 18 - line 125, column 151): " + [ v.constructor.name ]);
};

// | Set visual variant
var variant = function (v) {
    return function (props) {
        return {
            pressed: props.pressed,
            size: props.size,
            disabled: props.disabled,
            className: props.className,
            onPressedChange: props.onPressedChange,
            variant: v
        };
    };
};

// | Get size classes
var sizeClasses = function (v) {
    if (v instanceof Sm) {
        return "h-9 px-2.5";
    };
    if (v instanceof Md) {
        return "h-10 px-3";
    };
    if (v instanceof Lg) {
        return "h-11 px-5";
    };
    throw new Error("Failed pattern match at Hydrogen.Component.Toggle (line 129, column 15 - line 132, column 20): " + [ v.constructor.name ]);
};

// | Set size
var size = function (s) {
    return function (props) {
        return {
            pressed: props.pressed,
            variant: props.variant,
            disabled: props.disabled,
            className: props.className,
            onPressedChange: props.onPressedChange,
            size: s
        };
    };
};

// | Set pressed state
var pressed = function (p) {
    return function (props) {
        return {
            variant: props.variant,
            size: props.size,
            disabled: props.disabled,
            className: props.className,
            onPressedChange: props.onPressedChange,
            pressed: p
        };
    };
};

// | Set pressed change handler
var onPressedChange = function (handler) {
    return function (props) {
        return {
            pressed: props.pressed,
            variant: props.variant,
            size: props.size,
            disabled: props.disabled,
            className: props.className,
            onPressedChange: new Data_Maybe.Just(handler)
        };
    };
};

// | Set values change handler (multiple selection)
var onGroupValuesChange = function (handler) {
    return function (props) {
        return {
            type_: props.type_,
            value: props.value,
            values: props.values,
            variant: props.variant,
            size: props.size,
            disabled: props.disabled,
            className: props.className,
            onValueChange: props.onValueChange,
            onValuesChange: new Data_Maybe.Just(handler)
        };
    };
};

// | Set value change handler (single selection)
var onGroupValueChange = function (handler) {
    return function (props) {
        return {
            type_: props.type_,
            value: props.value,
            values: props.values,
            variant: props.variant,
            size: props.size,
            disabled: props.disabled,
            className: props.className,
            onValuesChange: props.onValuesChange,
            onValueChange: new Data_Maybe.Just(handler)
        };
    };
};

// | Set variant for all items
var groupVariant = function (v) {
    return function (props) {
        return {
            type_: props.type_,
            value: props.value,
            values: props.values,
            size: props.size,
            disabled: props.disabled,
            className: props.className,
            onValueChange: props.onValueChange,
            onValuesChange: props.onValuesChange,
            variant: v
        };
    };
};

// | Set selected values (multiple selection)
var groupValues = function (vs) {
    return function (props) {
        return {
            type_: props.type_,
            value: props.value,
            variant: props.variant,
            size: props.size,
            disabled: props.disabled,
            className: props.className,
            onValueChange: props.onValueChange,
            onValuesChange: props.onValuesChange,
            values: vs
        };
    };
};

// | Set selected value (single selection)
var groupValue = function (v) {
    return function (props) {
        return {
            type_: props.type_,
            values: props.values,
            variant: props.variant,
            size: props.size,
            disabled: props.disabled,
            className: props.className,
            onValueChange: props.onValueChange,
            onValuesChange: props.onValuesChange,
            value: new Data_Maybe.Just(v)
        };
    };
};

// | Set selection type
var groupType = function (t) {
    return function (props) {
        return {
            value: props.value,
            values: props.values,
            variant: props.variant,
            size: props.size,
            disabled: props.disabled,
            className: props.className,
            onValueChange: props.onValueChange,
            onValuesChange: props.onValuesChange,
            type_: t
        };
    };
};

// | Set size for all items
var groupSize = function (s) {
    return function (props) {
        return {
            type_: props.type_,
            value: props.value,
            values: props.values,
            variant: props.variant,
            disabled: props.disabled,
            className: props.className,
            onValueChange: props.onValueChange,
            onValuesChange: props.onValuesChange,
            size: s
        };
    };
};

// | Set disabled state for entire group
var groupDisabled = function (d) {
    return function (props) {
        return {
            type_: props.type_,
            value: props.value,
            values: props.values,
            variant: props.variant,
            size: props.size,
            className: props.className,
            onValueChange: props.onValueChange,
            onValuesChange: props.onValuesChange,
            disabled: d
        };
    };
};

// | Add custom class
var groupClassName = function (c) {
    return function (props) {
        return {
            type_: props.type_,
            value: props.value,
            values: props.values,
            variant: props.variant,
            size: props.size,
            disabled: props.disabled,
            onValueChange: props.onValueChange,
            onValuesChange: props.onValuesChange,
            className: props.className + (" " + c)
        };
    };
};
var eqToggleVariant = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Default && y instanceof Default) {
                return true;
            };
            if (x instanceof Outline && y instanceof Outline) {
                return true;
            };
            return false;
        };
    }
};
var eqToggleSize = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Sm && y instanceof Sm) {
                return true;
            };
            if (x instanceof Md && y instanceof Md) {
                return true;
            };
            if (x instanceof Lg && y instanceof Lg) {
                return true;
            };
            return false;
        };
    }
};
var eqToggleGroupType = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Single && y instanceof Single) {
                return true;
            };
            if (x instanceof Multiple && y instanceof Multiple) {
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
            pressed: props.pressed,
            variant: props.variant,
            size: props.size,
            className: props.className,
            onPressedChange: props.onPressedChange,
            disabled: d
        };
    };
};

// | Default toggle properties
var defaultProps = /* #__PURE__ */ (function () {
    return {
        pressed: false,
        variant: Default.value,
        size: Md.value,
        disabled: false,
        className: "",
        onPressedChange: Data_Maybe.Nothing.value
    };
})();

// | Default toggle group properties
var defaultGroupProps = /* #__PURE__ */ (function () {
    return {
        type_: Single.value,
        value: Data_Maybe.Nothing.value,
        values: [  ],
        variant: Default.value,
        size: Md.value,
        disabled: false,
        className: "",
        onValueChange: Data_Maybe.Nothing.value,
        onValuesChange: Data_Maybe.Nothing.value
    };
})();

// | Toggle group container
var toggleGroup = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultGroupProps)(propMods);
        var disabledClass = (function () {
            if (props.disabled) {
                return "opacity-50 pointer-events-none";
            };
            return "";
        })();
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex items-center gap-1", disabledClass, props.className ]), Halogen_HTML_Properties_ARIA.role("group") ])(children);
    };
};

// | Add custom class
var className = function (c) {
    return function (props) {
        return {
            pressed: props.pressed,
            variant: props.variant,
            size: props.size,
            disabled: props.disabled,
            onPressedChange: props.onPressedChange,
            className: props.className + (" " + c)
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // components
// ═══════════════════════════════════════════════════════════════════════════════
// | Base toggle classes
var baseClasses = "inline-flex items-center justify-center rounded-md text-sm font-medium ring-offset-background transition-colors focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2 disabled:pointer-events-none disabled:opacity-50";

// | Single toggle button
var toggle = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        var stateAttr = Halogen_HTML_Properties.attr("data-state")((function () {
            if (props.pressed) {
                return "on";
            };
            return "off";
        })());
        return Halogen_HTML_Elements.button(append1([ Hydrogen_UI_Core.cls([ baseClasses, variantClasses(props.variant), sizeClasses(props.size), props.className ]), type_(DOM_HTML_Indexed_ButtonType.ButtonButton.value), Halogen_HTML_Properties.disabled(props.disabled), Halogen_HTML_Properties_ARIA.pressed(show(props.pressed)), stateAttr ])((function () {
            if (props.onPressedChange instanceof Data_Maybe.Just) {
                return [ Halogen_HTML_Events.onClick(function (v) {
                    return props.onPressedChange.value0(!props.pressed);
                }) ];
            };
            if (props.onPressedChange instanceof Data_Maybe.Nothing) {
                return [  ];
            };
            throw new Error("Failed pattern match at Hydrogen.Component.Toggle (line 278, column 14 - line 280, column 24): " + [ props.onPressedChange.constructor.name ]);
        })()))(children);
    };
};

// | Toggle item within a group
var toggleItem = function (itemValue) {
    return function (children) {
        return Halogen_HTML_Elements.button([ Hydrogen_UI_Core.cls([ baseClasses, variantClasses(Default.value), sizeClasses(Md.value) ]), type_(DOM_HTML_Indexed_ButtonType.ButtonButton.value), value(itemValue), Halogen_HTML_Properties.attr("data-state")("off") ])(children);
    };
};
export {
    toggle,
    toggleGroup,
    toggleItem,
    Default,
    Outline,
    Sm,
    Md,
    Lg,
    Single,
    Multiple,
    pressed,
    variant,
    size,
    disabled,
    className,
    onPressedChange,
    groupType,
    groupValue,
    groupValues,
    groupVariant,
    groupSize,
    groupDisabled,
    groupClassName,
    onGroupValueChange,
    onGroupValuesChange,
    eqToggleVariant,
    eqToggleSize,
    eqToggleGroupType
};
