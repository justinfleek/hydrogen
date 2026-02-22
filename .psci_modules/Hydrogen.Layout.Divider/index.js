// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                        // hydrogen // divider
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Content divider component
// |
// | Visual separators for content sections with support for
// | horizontal/vertical orientation and text labels.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Layout.Divider as Divider
// |
// | -- Horizontal divider (default)
// | Divider.divider []
// |
// | -- Vertical divider
// | Divider.divider [ Divider.orientation Divider.Vertical ]
// |
// | -- Divider with label
// | Divider.dividerWithLabel [] [ HH.text "OR" ]
// |
// | -- Dashed divider
// | Divider.divider [ Divider.variant Divider.Dashed ]
// | ```
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Properties from "../Halogen.HTML.Properties/index.js";
import * as Halogen_HTML_Properties_ARIA from "../Halogen.HTML.Properties.ARIA/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // variant
// ═══════════════════════════════════════════════════════════════════════════════
// | Divider style variants
var Solid = /* #__PURE__ */ (function () {
    function Solid() {

    };
    Solid.value = new Solid();
    return Solid;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // variant
// ═══════════════════════════════════════════════════════════════════════════════
// | Divider style variants
var Dashed = /* #__PURE__ */ (function () {
    function Dashed() {

    };
    Dashed.value = new Dashed();
    return Dashed;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // variant
// ═══════════════════════════════════════════════════════════════════════════════
// | Divider style variants
var Dotted = /* #__PURE__ */ (function () {
    function Dotted() {

    };
    Dotted.value = new Dotted();
    return Dotted;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // thickness
// ═══════════════════════════════════════════════════════════════════════════════
// | Divider thickness
var Thin = /* #__PURE__ */ (function () {
    function Thin() {

    };
    Thin.value = new Thin();
    return Thin;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // thickness
// ═══════════════════════════════════════════════════════════════════════════════
// | Divider thickness
var Medium = /* #__PURE__ */ (function () {
    function Medium() {

    };
    Medium.value = new Medium();
    return Medium;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // thickness
// ═══════════════════════════════════════════════════════════════════════════════
// | Divider thickness
var Thick = /* #__PURE__ */ (function () {
    function Thick() {

    };
    Thick.value = new Thick();
    return Thick;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // spacing
// ═══════════════════════════════════════════════════════════════════════════════
// | Spacing around the divider
var SpaceNone = /* #__PURE__ */ (function () {
    function SpaceNone() {

    };
    SpaceNone.value = new SpaceNone();
    return SpaceNone;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // spacing
// ═══════════════════════════════════════════════════════════════════════════════
// | Spacing around the divider
var SpaceSm = /* #__PURE__ */ (function () {
    function SpaceSm() {

    };
    SpaceSm.value = new SpaceSm();
    return SpaceSm;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // spacing
// ═══════════════════════════════════════════════════════════════════════════════
// | Spacing around the divider
var SpaceMd = /* #__PURE__ */ (function () {
    function SpaceMd() {

    };
    SpaceMd.value = new SpaceMd();
    return SpaceMd;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // spacing
// ═══════════════════════════════════════════════════════════════════════════════
// | Spacing around the divider
var SpaceLg = /* #__PURE__ */ (function () {
    function SpaceLg() {

    };
    SpaceLg.value = new SpaceLg();
    return SpaceLg;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // spacing
// ═══════════════════════════════════════════════════════════════════════════════
// | Spacing around the divider
var SpaceXl = /* #__PURE__ */ (function () {
    function SpaceXl() {

    };
    SpaceXl.value = new SpaceXl();
    return SpaceXl;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // orientation
// ═══════════════════════════════════════════════════════════════════════════════
// | Divider orientation
var Horizontal = /* #__PURE__ */ (function () {
    function Horizontal() {

    };
    Horizontal.value = new Horizontal();
    return Horizontal;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // orientation
// ═══════════════════════════════════════════════════════════════════════════════
// | Divider orientation
var Vertical = /* #__PURE__ */ (function () {
    function Vertical() {

    };
    Vertical.value = new Vertical();
    return Vertical;
})();
var variantClass = function (v) {
    if (v instanceof Solid) {
        return "";
    };
    if (v instanceof Dashed) {
        return "border-dashed";
    };
    if (v instanceof Dotted) {
        return "border-dotted";
    };
    throw new Error("Failed pattern match at Hydrogen.Layout.Divider (line 83, column 16 - line 86, column 28): " + [ v.constructor.name ]);
};

// | Set variant
var variant = function (v) {
    return function (props) {
        return {
            orientation: props.orientation,
            spacing: props.spacing,
            color: props.color,
            thickness: props.thickness,
            className: props.className,
            variant: v
        };
    };
};
var thicknessValue = function (v) {
    if (v instanceof Thin) {
        return "1px";
    };
    if (v instanceof Medium) {
        return "2px";
    };
    if (v instanceof Thick) {
        return "4px";
    };
    throw new Error("Failed pattern match at Hydrogen.Layout.Divider (line 128, column 18 - line 131, column 17): " + [ v.constructor.name ]);
};

// | Set thickness
var thickness = function (t) {
    return function (props) {
        return {
            orientation: props.orientation,
            variant: props.variant,
            spacing: props.spacing,
            color: props.color,
            className: props.className,
            thickness: t
        };
    };
};
var spacingClass = function (orient) {
    return function (space) {
        if (orient instanceof Horizontal && space instanceof SpaceNone) {
            return "";
        };
        if (orient instanceof Horizontal && space instanceof SpaceSm) {
            return "my-2";
        };
        if (orient instanceof Horizontal && space instanceof SpaceMd) {
            return "my-4";
        };
        if (orient instanceof Horizontal && space instanceof SpaceLg) {
            return "my-6";
        };
        if (orient instanceof Horizontal && space instanceof SpaceXl) {
            return "my-8";
        };
        if (orient instanceof Vertical && space instanceof SpaceNone) {
            return "";
        };
        if (orient instanceof Vertical && space instanceof SpaceSm) {
            return "mx-2";
        };
        if (orient instanceof Vertical && space instanceof SpaceMd) {
            return "mx-4";
        };
        if (orient instanceof Vertical && space instanceof SpaceLg) {
            return "mx-6";
        };
        if (orient instanceof Vertical && space instanceof SpaceXl) {
            return "mx-8";
        };
        throw new Error("Failed pattern match at Hydrogen.Layout.Divider (line 103, column 29 - line 113, column 30): " + [ orient.constructor.name, space.constructor.name ]);
    };
};

// | Set spacing
var spacing = function (s) {
    return function (props) {
        return {
            orientation: props.orientation,
            variant: props.variant,
            color: props.color,
            thickness: props.thickness,
            className: props.className,
            spacing: s
        };
    };
};

// | Set orientation
var orientation = function (o) {
    return function (props) {
        return {
            variant: props.variant,
            spacing: props.spacing,
            color: props.color,
            thickness: props.thickness,
            className: props.className,
            orientation: o
        };
    };
};
var eqVariant = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Solid && y instanceof Solid) {
                return true;
            };
            if (x instanceof Dashed && y instanceof Dashed) {
                return true;
            };
            if (x instanceof Dotted && y instanceof Dotted) {
                return true;
            };
            return false;
        };
    }
};
var eqThickness = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Thin && y instanceof Thin) {
                return true;
            };
            if (x instanceof Medium && y instanceof Medium) {
                return true;
            };
            if (x instanceof Thick && y instanceof Thick) {
                return true;
            };
            return false;
        };
    }
};
var eqSpacing = {
    eq: function (x) {
        return function (y) {
            if (x instanceof SpaceNone && y instanceof SpaceNone) {
                return true;
            };
            if (x instanceof SpaceSm && y instanceof SpaceSm) {
                return true;
            };
            if (x instanceof SpaceMd && y instanceof SpaceMd) {
                return true;
            };
            if (x instanceof SpaceLg && y instanceof SpaceLg) {
                return true;
            };
            if (x instanceof SpaceXl && y instanceof SpaceXl) {
                return true;
            };
            return false;
        };
    }
};
var eqOrientation = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Horizontal && y instanceof Horizontal) {
                return true;
            };
            if (x instanceof Vertical && y instanceof Vertical) {
                return true;
            };
            return false;
        };
    }
};
var defaultProps = /* #__PURE__ */ (function () {
    return {
        orientation: Horizontal.value,
        variant: Solid.value,
        spacing: SpaceMd.value,
        color: Data_Maybe.Nothing.value,
        thickness: Thin.value,
        className: ""
    };
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // components
// ═══════════════════════════════════════════════════════════════════════════════
// | Simple divider line
var divider = function (propMods) {
    var props = Data_Array.foldl(function (p) {
        return function (f) {
            return f(p);
        };
    })(defaultProps)(propMods);
    var spaceCls = spacingClass(props.orientation)(props.spacing);
    var thicknessStyle = (function () {
        if (props.orientation instanceof Horizontal) {
            return "border-top-width: " + thicknessValue(props.thickness);
        };
        if (props.orientation instanceof Vertical) {
            return "border-left-width: " + thicknessValue(props.thickness);
        };
        throw new Error("Failed pattern match at Hydrogen.Layout.Divider (line 203, column 22 - line 205, column 74): " + [ props.orientation.constructor.name ]);
    })();
    var variantCls = variantClass(props.variant);
    var orientClasses = (function () {
        if (props.orientation instanceof Horizontal) {
            return "w-full h-0 border-t";
        };
        if (props.orientation instanceof Vertical) {
            return "h-full w-0 border-l self-stretch";
        };
        throw new Error("Failed pattern match at Hydrogen.Layout.Divider (line 192, column 21 - line 194, column 53): " + [ props.orientation.constructor.name ]);
    })();
    var colorClass = (function () {
        if (props.color instanceof Data_Maybe.Just) {
            return props.color.value0;
        };
        if (props.color instanceof Data_Maybe.Nothing) {
            return "border-border";
        };
        throw new Error("Failed pattern match at Hydrogen.Layout.Divider (line 196, column 18 - line 198, column 33): " + [ props.color.constructor.name ]);
    })();
    return Halogen_HTML_Elements.hr([ Hydrogen_UI_Core.cls([ "shrink-0", orientClasses, colorClass, spaceCls, variantCls, props.className ]), Halogen_HTML_Properties_ARIA.role("separator"), Halogen_HTML_Properties.style(thicknessStyle) ]);
};

// | Divider with centered label
var dividerWithLabel = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        var spaceCls = spacingClass(props.orientation)(props.spacing);
        var variantCls = variantClass(props.variant);
        var colorClass = (function () {
            if (props.color instanceof Data_Maybe.Just) {
                return props.color.value0;
            };
            if (props.color instanceof Data_Maybe.Nothing) {
                return "bg-border";
            };
            throw new Error("Failed pattern match at Hydrogen.Layout.Divider (line 220, column 18 - line 222, column 29): " + [ props.color.constructor.name ]);
        })();
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex items-center", spaceCls, props.className ]), Halogen_HTML_Properties_ARIA.role("separator") ])([ Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex-1 h-px", colorClass, variantCls ]) ])([  ]), Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "px-3 text-sm text-muted-foreground shrink-0" ]) ])(children), Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex-1 h-px", colorClass, variantCls ]) ])([  ]) ]);
    };
};

// | Set custom color class
var color = function (c) {
    return function (props) {
        return {
            orientation: props.orientation,
            variant: props.variant,
            spacing: props.spacing,
            thickness: props.thickness,
            className: props.className,
            color: new Data_Maybe.Just(c)
        };
    };
};

// | Add custom class
var className = function (c) {
    return function (props) {
        return {
            orientation: props.orientation,
            variant: props.variant,
            spacing: props.spacing,
            color: props.color,
            thickness: props.thickness,
            className: props.className + (" " + c)
        };
    };
};
export {
    divider,
    dividerWithLabel,
    orientation,
    variant,
    spacing,
    color,
    thickness,
    className,
    Horizontal,
    Vertical,
    Solid,
    Dashed,
    Dotted,
    SpaceNone,
    SpaceSm,
    SpaceMd,
    SpaceLg,
    SpaceXl,
    Thin,
    Medium,
    Thick,
    eqOrientation,
    eqVariant,
    eqSpacing,
    eqThickness
};
