// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                          // hydrogen // focus
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Focus management utilities
// |
// | Type-safe focus management for accessibility.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.A11y.Focus as Focus
// |
// | -- Focus ring styles
// | Focus.focusRing          -- "focus:outline-none focus:ring-2..."
// | Focus.focusRingInset     -- With inset ring
// |
// | -- Focus trap container
// | Focus.focusTrap []
// |   [ dialogContent ]
// |
// | -- Skip link
// | Focus.skipLink "Skip to content" "#main"
// | ```
import * as Data_Array from "../Data.Array/index.js";
import * as Halogen_HTML_Core from "../Halogen.HTML.Core/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Properties from "../Halogen.HTML.Properties/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // tab index
// ═══════════════════════════════════════════════════════════════════════════════
// | Tab index values
var TabIndexAuto = /* #__PURE__ */ (function () {
    function TabIndexAuto() {

    };
    TabIndexAuto.value = new TabIndexAuto();
    return TabIndexAuto;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // tab index
// ═══════════════════════════════════════════════════════════════════════════════
// | Tab index values
var TabIndexFocusable = /* #__PURE__ */ (function () {
    function TabIndexFocusable() {

    };
    TabIndexFocusable.value = new TabIndexFocusable();
    return TabIndexFocusable;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // tab index
// ═══════════════════════════════════════════════════════════════════════════════
// | Tab index values
var TabIndexNot = /* #__PURE__ */ (function () {
    function TabIndexNot() {

    };
    TabIndexNot.value = new TabIndexNot();
    return TabIndexNot;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // tab index
// ═══════════════════════════════════════════════════════════════════════════════
// | Tab index values
var TabIndexCustom = /* #__PURE__ */ (function () {
    function TabIndexCustom(value0) {
        this.value0 = value0;
    };
    TabIndexCustom.create = function (value0) {
        return new TabIndexCustom(value0);
    };
    return TabIndexCustom;
})();

// | Convert to Halogen property
var tabIndex = function (v) {
    if (v instanceof TabIndexAuto) {
        return Halogen_HTML_Properties.tabIndex(0);
    };
    if (v instanceof TabIndexFocusable) {
        return Halogen_HTML_Properties.tabIndex(0);
    };
    if (v instanceof TabIndexNot) {
        return Halogen_HTML_Properties.tabIndex(-1 | 0);
    };
    if (v instanceof TabIndexCustom) {
        return Halogen_HTML_Properties.tabIndex(v.value0);
    };
    throw new Error("Failed pattern match at Hydrogen.A11y.Focus (line 130, column 12 - line 134, column 36): " + [ v.constructor.name ]);
};

// | Props to make an element focusable
// |
// | Returns an array of properties that can be spread onto elements
// | to make them keyboard-focusable.
var focusableProps = function (children) {
    return Halogen_HTML_Elements.div([ Halogen_HTML_Properties.tabIndex(0), Halogen_HTML_Properties.attr("role")("button") ])(children);
};

// | Focus within (child has focus)
var focusWithin = "focus-within:outline-none focus-within:ring-2 focus-within:ring-ring focus-within:ring-offset-2";

// | Focus visible only (keyboard focus)
var focusVisible = "focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2";

// | Inset focus ring (inside element)
var focusRingInset = "focus:outline-none focus:ring-2 focus:ring-ring focus:ring-inset";

// ═══════════════════════════════════════════════════════════════════════════════
//                                                             // focus ring styles
// ═══════════════════════════════════════════════════════════════════════════════
// | Standard focus ring classes
// |
// | Includes ring color, offset, and outline removal
var focusRing = "focus:outline-none focus:ring-2 focus:ring-ring focus:ring-offset-2 focus:ring-offset-background";

// | Skip link for keyboard navigation
// |
// | Allows keyboard users to skip navigation and jump to main content.
var skipLink = function (label) {
    return function (href) {
        return Halogen_HTML_Elements.a([ Hydrogen_UI_Core.cls([ "sr-only focus:not-sr-only focus:absolute focus:z-50 focus:top-4 focus:left-4 focus:px-4 focus:py-2 focus:bg-background focus:text-foreground focus:rounded-md", focusRing ]), Halogen_HTML_Properties.href(href) ])([ Halogen_HTML_Core.text(label) ]);
    };
};
var eqTabIndex = {
    eq: function (x) {
        return function (y) {
            if (x instanceof TabIndexAuto && y instanceof TabIndexAuto) {
                return true;
            };
            if (x instanceof TabIndexFocusable && y instanceof TabIndexFocusable) {
                return true;
            };
            if (x instanceof TabIndexNot && y instanceof TabIndexNot) {
                return true;
            };
            if (x instanceof TabIndexCustom && y instanceof TabIndexCustom) {
                return x.value0 === y.value0;
            };
            return false;
        };
    }
};
var defaultFocusTrapProps = {
    className: ""
};

// | Focus trap container
// |
// | Note: Actual focus trapping requires JavaScript.
// | This provides the semantic container with proper ARIA attributes.
var focusTrap = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultFocusTrapProps)(propMods);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ props.className ]), Halogen_HTML_Properties.attr("data-focus-trap")("true") ])(children);
    };
};
export {
    focusRing,
    focusRingInset,
    focusVisible,
    focusWithin,
    focusTrap,
    skipLink,
    focusableProps,
    TabIndexAuto,
    TabIndexFocusable,
    TabIndexNot,
    TabIndexCustom,
    tabIndex,
    eqTabIndex
};
