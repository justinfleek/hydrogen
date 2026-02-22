// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                     // hydrogen // collapsible
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Collapsible/expandable content component
// |
// | Animated expand/collapse panels with trigger elements.
// |
// | ## Features
// |
// | - Trigger element (clickable)
// | - Animated expand/collapse
// | - Open/closed state
// | - Controlled mode
// | - Lazy render content option
// | - Icon rotation animation
// | - Disabled state
// | - Accessible (ARIA expanded)
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Component.Collapsible as Collapsible
// |
// | -- Basic collapsible
// | Collapsible.collapsible
// |   [ Collapsible.onToggle HandleToggle ]
// |   (Collapsible.trigger [] [ HH.text "Click to expand" ])
// |   (Collapsible.content [] [ HH.text "Hidden content here" ])
// |
// | -- Controlled collapsible
// | Collapsible.collapsible
// |   [ Collapsible.isOpen state.expanded
// |   , Collapsible.onToggle ToggleExpanded
// |   ]
// |   (Collapsible.trigger [] [ HH.text "Settings" ])
// |   (Collapsible.content [] settingsContent)
// |
// | -- With icon
// | Collapsible.collapsible
// |   [ Collapsible.isOpen true
// |   , Collapsible.showIcon true
// |   ]
// |   (Collapsible.triggerWithIcon [] "Advanced Options")
// |   (Collapsible.content [] advancedContent)
// |
// | -- Disabled
// | Collapsible.collapsible
// |   [ Collapsible.disabled true ]
// |   trigger
// |   content
// | ```
import * as $foreign from "./foreign.js";
import * as Control_Applicative from "../Control.Applicative/index.js";
import * as DOM_HTML_Indexed_ButtonType from "../DOM.HTML.Indexed.ButtonType/index.js";
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
import * as Effect from "../Effect/index.js";
import * as Halogen_HTML_Core from "../Halogen.HTML.Core/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Properties from "../Halogen.HTML.Properties/index.js";
import * as Halogen_HTML_Properties_ARIA from "../Halogen.HTML.Properties.ARIA/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";
var pure = /* #__PURE__ */ Control_Applicative.pure(Effect.applicativeEffect);
var type_ = /* #__PURE__ */ Halogen_HTML_Properties.type_(Halogen_HTML_Core.isPropButtonType);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Icon position relative to trigger text
var IconLeft = /* #__PURE__ */ (function () {
    function IconLeft() {

    };
    IconLeft.value = new IconLeft();
    return IconLeft;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Icon position relative to trigger text
var IconRight = /* #__PURE__ */ (function () {
    function IconRight() {

    };
    IconRight.value = new IconRight();
    return IconRight;
})();

// | Add custom class to trigger
var triggerClassName = function (c) {
    return function (props) {
        return {
            className: props.className + (" " + c)
        };
    };
};

// | Toggle state
var toggle = function (v) {
    return pure(false);
};

// | Show expand/collapse icon
var showIcon = function (s) {
    return function (props) {
        return {
            isOpen: props.isOpen,
            onToggle: props.onToggle,
            disabled: props.disabled,
            iconPosition: props.iconPosition,
            lazyRender: props.lazyRender,
            animationDuration: props.animationDuration,
            className: props.className,
            showIcon: s
        };
    };
};

// | Open
var open = function (v) {
    return pure(Data_Unit.unit);
};

// | Set toggle handler
var onToggle = function (handler) {
    return function (props) {
        return {
            isOpen: props.isOpen,
            disabled: props.disabled,
            showIcon: props.showIcon,
            iconPosition: props.iconPosition,
            lazyRender: props.lazyRender,
            animationDuration: props.animationDuration,
            className: props.className,
            onToggle: new Data_Maybe.Just(handler)
        };
    };
};

// | Enable lazy rendering of content
var lazyRender = function (l) {
    return function (props) {
        return {
            isOpen: props.isOpen,
            onToggle: props.onToggle,
            disabled: props.disabled,
            showIcon: props.showIcon,
            iconPosition: props.iconPosition,
            animationDuration: props.animationDuration,
            className: props.className,
            lazyRender: l
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // prop builders
// ═══════════════════════════════════════════════════════════════════════════════
// | Set open state
var isOpen = function (o) {
    return function (props) {
        return {
            onToggle: props.onToggle,
            disabled: props.disabled,
            showIcon: props.showIcon,
            iconPosition: props.iconPosition,
            lazyRender: props.lazyRender,
            animationDuration: props.animationDuration,
            className: props.className,
            isOpen: o
        };
    };
};

// | Initialize collapsible
var initCollapsible = function (opts) {
    return function (callbacks) {
        return pure($foreign.unsafeCollapsibleElement);
    };
};

// | Set icon position
var iconPosition = function (p) {
    return function (props) {
        return {
            isOpen: props.isOpen,
            onToggle: props.onToggle,
            disabled: props.disabled,
            showIcon: props.showIcon,
            lazyRender: props.lazyRender,
            animationDuration: props.animationDuration,
            className: props.className,
            iconPosition: p
        };
    };
};
var eqIconPosition = {
    eq: function (x) {
        return function (y) {
            if (x instanceof IconLeft && y instanceof IconLeft) {
                return true;
            };
            if (x instanceof IconRight && y instanceof IconRight) {
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
            isOpen: props.isOpen,
            onToggle: props.onToggle,
            showIcon: props.showIcon,
            iconPosition: props.iconPosition,
            lazyRender: props.lazyRender,
            animationDuration: props.animationDuration,
            className: props.className,
            disabled: d
        };
    };
};

// | Destroy collapsible
var destroyCollapsible = function (v) {
    return pure(Data_Unit.unit);
};

// | Default trigger properties
var defaultTriggerProps = {
    className: ""
};

// | Trigger element
// |
// | Clickable element that toggles the collapsible
var trigger = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultTriggerProps)(propMods);
        return Halogen_HTML_Elements.button([ Hydrogen_UI_Core.cls([ "collapsible-trigger flex items-center justify-between w-full py-2 px-3 text-left font-medium transition-colors hover:bg-accent rounded-md cursor-pointer focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring", props.className ]), type_(DOM_HTML_Indexed_ButtonType.ButtonButton.value), Halogen_HTML_Properties_ARIA.expanded("false") ])(children);
    };
};

// | Default collapsible properties
var defaultProps = /* #__PURE__ */ (function () {
    return {
        isOpen: false,
        onToggle: Data_Maybe.Nothing.value,
        disabled: false,
        showIcon: true,
        iconPosition: IconRight.value,
        lazyRender: false,
        animationDuration: 200,
        className: ""
    };
})();

// | Default content properties
var defaultContentProps = {
    className: ""
};

// | Add custom class to content
var contentClassName = function (c) {
    return function (props) {
        return {
            className: props.className + (" " + c)
        };
    };
};

// | Content element
// |
// | Collapsible content that expands/collapses
var content = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultContentProps)(propMods);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "collapsible-content overflow-hidden transition-all data-[state=closed]:h-0 data-[state=closed]:opacity-0 data-[state=open]:opacity-100", props.className ]), Halogen_HTML_Properties.attr("data-state")("closed"), Halogen_HTML_Properties_ARIA.hidden("true") ])([ Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "collapsible-content-inner py-2 px-3" ]) ])(children) ]);
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // components
// ═══════════════════════════════════════════════════════════════════════════════
// | Collapsible container
// |
// | Wraps trigger and content with expand/collapse behavior
var collapsible = function (propMods) {
    return function (triggerEl) {
        return function (contentEl) {
            var props = Data_Array.foldl(function (p) {
                return function (f) {
                    return f(p);
                };
            })(defaultProps)(propMods);
            var openClass = (function () {
                if (props.isOpen) {
                    return "collapsible-open";
                };
                return "collapsible-closed";
            })();
            var disabledClass = (function () {
                if (props.disabled) {
                    return "collapsible-disabled opacity-50";
                };
                return "";
            })();
            return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "collapsible", openClass, disabledClass, props.className ]), Halogen_HTML_Properties.attr("data-state")((function () {
                if (props.isOpen) {
                    return "open";
                };
                return "closed";
            })()), Halogen_HTML_Properties.attr("data-disabled")((function () {
                if (props.disabled) {
                    return "true";
                };
                return "false";
            })()) ])([ triggerEl, contentEl ]);
        };
    };
};

// | Close
var close = function (v) {
    return pure(Data_Unit.unit);
};

// | Add custom class to container
var className = function (c) {
    return function (props) {
        return {
            isOpen: props.isOpen,
            onToggle: props.onToggle,
            disabled: props.disabled,
            showIcon: props.showIcon,
            iconPosition: props.iconPosition,
            lazyRender: props.lazyRender,
            animationDuration: props.animationDuration,
            className: props.className + (" " + c)
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // icons
// ═══════════════════════════════════════════════════════════════════════════════
// | Chevron icon (rotates on expand)
var chevronIcon = /* #__PURE__ */ Halogen_HTML_Elements.element("svg")([ /* #__PURE__ */ Halogen_HTML_Properties.attr("xmlns")("http://www.w3.org/2000/svg"), /* #__PURE__ */ Halogen_HTML_Properties.attr("width")("16"), /* #__PURE__ */ Halogen_HTML_Properties.attr("height")("16"), /* #__PURE__ */ Halogen_HTML_Properties.attr("viewBox")("0 0 24 24"), /* #__PURE__ */ Halogen_HTML_Properties.attr("fill")("none"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke")("currentColor"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke-width")("2"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke-linecap")("round"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke-linejoin")("round"), /* #__PURE__ */ Hydrogen_UI_Core.cls([ "collapsible-chevron transition-transform duration-200 data-[state=open]:rotate-180" ]) ])([ /* #__PURE__ */ Halogen_HTML_Elements.element("polyline")([ /* #__PURE__ */ Halogen_HTML_Properties.attr("points")("6 9 12 15 18 9") ])([  ]) ]);

// | Trigger with icon
// |
// | Trigger element with chevron icon that rotates
var triggerWithIcon = function (propMods) {
    return function (label) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultTriggerProps)(propMods);
        return Halogen_HTML_Elements.button([ Hydrogen_UI_Core.cls([ "collapsible-trigger flex items-center justify-between w-full py-2 px-3 text-left font-medium transition-colors hover:bg-accent rounded-md cursor-pointer focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring", props.className ]), type_(DOM_HTML_Indexed_ButtonType.ButtonButton.value), Halogen_HTML_Properties_ARIA.expanded("false") ])([ Halogen_HTML_Elements.span([  ])([ Halogen_HTML_Core.text(label) ]), chevronIcon ]);
    };
};

// | Set animation duration (ms)
var animationDuration = function (d) {
    return function (props) {
        return {
            isOpen: props.isOpen,
            onToggle: props.onToggle,
            disabled: props.disabled,
            showIcon: props.showIcon,
            iconPosition: props.iconPosition,
            lazyRender: props.lazyRender,
            className: props.className,
            animationDuration: d
        };
    };
};
export {
    collapsible,
    trigger,
    triggerWithIcon,
    content,
    defaultProps,
    defaultTriggerProps,
    defaultContentProps,
    isOpen,
    onToggle,
    disabled,
    showIcon,
    iconPosition,
    lazyRender,
    animationDuration,
    className,
    triggerClassName,
    contentClassName,
    IconLeft,
    IconRight,
    initCollapsible,
    destroyCollapsible,
    toggle,
    open,
    close,
    eqIconPosition
};
