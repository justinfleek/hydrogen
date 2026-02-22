// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                           // hydrogen // icon
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Base icon component and utilities
// |
// | This module provides the foundation for rendering SVG icons:
// | - IconProps for consistent icon configuration
// | - Helper functions for creating icon components
// | - Size and color utilities
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Icon.Icon as Icon
// | import Hydrogen.Icon.Icons as Icons
// |
// | -- Render an icon with default size
// | Icons.check []
// |
// | -- With custom size
// | Icons.check [ Icon.size Icon.Lg ]
// |
// | -- With custom class
// | Icons.check [ Icon.className "text-primary" ]
// | ```
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Semigroup from "../Data.Semigroup/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Properties from "../Halogen.HTML.Properties/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";
var append = /* #__PURE__ */ Data_Semigroup.append(Data_Semigroup.semigroupArray);
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showNumber);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // icon sizes
// ═══════════════════════════════════════════════════════════════════════════════
// | Standard icon sizes
var Xs = /* #__PURE__ */ (function () {
    function Xs() {

    };
    Xs.value = new Xs();
    return Xs;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // icon sizes
// ═══════════════════════════════════════════════════════════════════════════════
// | Standard icon sizes
var Sm = /* #__PURE__ */ (function () {
    function Sm() {

    };
    Sm.value = new Sm();
    return Sm;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // icon sizes
// ═══════════════════════════════════════════════════════════════════════════════
// | Standard icon sizes
var Md = /* #__PURE__ */ (function () {
    function Md() {

    };
    Md.value = new Md();
    return Md;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // icon sizes
// ═══════════════════════════════════════════════════════════════════════════════
// | Standard icon sizes
var Lg = /* #__PURE__ */ (function () {
    function Lg() {

    };
    Lg.value = new Lg();
    return Lg;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // icon sizes
// ═══════════════════════════════════════════════════════════════════════════════
// | Standard icon sizes
var Xl = /* #__PURE__ */ (function () {
    function Xl() {

    };
    Xl.value = new Xl();
    return Xl;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // icon sizes
// ═══════════════════════════════════════════════════════════════════════════════
// | Standard icon sizes
var Xxl = /* #__PURE__ */ (function () {
    function Xxl() {

    };
    Xxl.value = new Xxl();
    return Xxl;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // icon sizes
// ═══════════════════════════════════════════════════════════════════════════════
// | Standard icon sizes
var Custom = /* #__PURE__ */ (function () {
    function Custom(value0) {
        this.value0 = value0;
    };
    Custom.create = function (value0) {
        return new Custom(value0);
    };
    return Custom;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // svg helpers
// ═══════════════════════════════════════════════════════════════════════════════
// | Create an SVG element
var svgElement = function (name) {
    return function (props) {
        return Halogen_HTML_Elements.elementNS(Hydrogen_UI_Core.svgNS)(name)(props);
    };
};

// | Set stroke width
var strokeWidth = function (w) {
    return function (props) {
        return {
            size: props.size,
            className: props.className,
            ariaLabel: props.ariaLabel,
            ariaHidden: props.ariaHidden,
            strokeWidth: w
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // prop builders
// ═══════════════════════════════════════════════════════════════════════════════
// | Set icon size
var size = function (s) {
    return function (props) {
        return {
            className: props.className,
            strokeWidth: props.strokeWidth,
            ariaLabel: props.ariaLabel,
            ariaHidden: props.ariaHidden,
            size: s
        };
    };
};

// | Create a rect element
var rectElement = function (r) {
    return svgElement("rect")(append([ Halogen_HTML_Properties.attr("x")(show(r.x)), Halogen_HTML_Properties.attr("y")(show(r.y)), Halogen_HTML_Properties.attr("width")(show(r.width)), Halogen_HTML_Properties.attr("height")(show(r.height)) ])((function () {
        if (r.rx instanceof Data_Maybe.Just) {
            return [ Halogen_HTML_Properties.attr("rx")(show(r.rx.value0)) ];
        };
        if (r.rx instanceof Data_Maybe.Nothing) {
            return [  ];
        };
        throw new Error("Failed pattern match at Hydrogen.Icon.Icon (line 217, column 10 - line 219, column 20): " + [ r.rx.constructor.name ]);
    })()))([  ]);
};

// | Create a polyline element
var polylineElement = function (points) {
    return svgElement("polyline")([ Halogen_HTML_Properties.attr("points")(points) ])([  ]);
};

// | Create a polygon element
var polygonElement = function (points) {
    return svgElement("polygon")([ Halogen_HTML_Properties.attr("points")(points) ])([  ]);
};

// | Create a path element
var pathElement = function (d) {
    return svgElement("path")([ Halogen_HTML_Properties.attr("d")(d) ])([  ]);
};

// | Create a line element
var lineElement = function (x1) {
    return function (y1) {
        return function (x2) {
            return function (y2) {
                return svgElement("line")([ Halogen_HTML_Properties.attr("x1")(show(x1)), Halogen_HTML_Properties.attr("y1")(show(y1)), Halogen_HTML_Properties.attr("x2")(show(x2)), Halogen_HTML_Properties.attr("y2")(show(y2)) ])([  ]);
            };
        };
    };
};

// | Get size in pixels
var iconSizePx = function (v) {
    if (v instanceof Xs) {
        return 12;
    };
    if (v instanceof Sm) {
        return 16;
    };
    if (v instanceof Md) {
        return 20;
    };
    if (v instanceof Lg) {
        return 24;
    };
    if (v instanceof Xl) {
        return 32;
    };
    if (v instanceof Xxl) {
        return 40;
    };
    if (v instanceof Custom) {
        return 24;
    };
    throw new Error("Failed pattern match at Hydrogen.Icon.Icon (line 143, column 14 - line 150, column 17): " + [ v.constructor.name ]);
};

// | Get Tailwind size class for icon
var iconSizeClass = function (v) {
    if (v instanceof Xs) {
        return "w-3 h-3";
    };
    if (v instanceof Sm) {
        return "w-4 h-4";
    };
    if (v instanceof Md) {
        return "w-5 h-5";
    };
    if (v instanceof Lg) {
        return "w-6 h-6";
    };
    if (v instanceof Xl) {
        return "w-8 h-8";
    };
    if (v instanceof Xxl) {
        return "w-10 h-10";
    };
    if (v instanceof Custom) {
        return v.value0;
    };
    throw new Error("Failed pattern match at Hydrogen.Icon.Icon (line 132, column 17 - line 139, column 20): " + [ v.constructor.name ]);
};

// | Render an SVG icon with props
var svgIcon = function (props) {
    return function (children) {
        return Halogen_HTML_Elements.elementNS(Hydrogen_UI_Core.svgNS)("svg")([ Hydrogen_UI_Core.svgCls([ iconSizeClass(props.size), props.className ]), Halogen_HTML_Properties.attr("viewBox")("0 0 24 24"), Halogen_HTML_Properties.attr("fill")("none"), Halogen_HTML_Properties.attr("stroke")("currentColor"), Halogen_HTML_Properties.attr("stroke-width")(show(props.strokeWidth)), Halogen_HTML_Properties.attr("stroke-linecap")("round"), Halogen_HTML_Properties.attr("stroke-linejoin")("round"), Halogen_HTML_Properties.attr("aria-hidden")((function () {
            if (props.ariaHidden) {
                return "true";
            };
            return "false";
        })()) ])(children);
    };
};
var eqIconSize = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Xs && y instanceof Xs) {
                return true;
            };
            if (x instanceof Sm && y instanceof Sm) {
                return true;
            };
            if (x instanceof Md && y instanceof Md) {
                return true;
            };
            if (x instanceof Lg && y instanceof Lg) {
                return true;
            };
            if (x instanceof Xl && y instanceof Xl) {
                return true;
            };
            if (x instanceof Xxl && y instanceof Xxl) {
                return true;
            };
            if (x instanceof Custom && y instanceof Custom) {
                return x.value0 === y.value0;
            };
            return false;
        };
    }
};

// | Default icon properties
var defaultProps = /* #__PURE__ */ (function () {
    return {
        size: Md.value,
        className: "",
        strokeWidth: 2.0,
        ariaLabel: Data_Maybe.Nothing.value,
        ariaHidden: true
    };
})();

// | Create an icon from multiple SVG children
var iconWith = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return svgIcon(props)(children);
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // icon rendering
// ═══════════════════════════════════════════════════════════════════════════════
// | Create an icon from SVG path data
// |
// | ```purescript
// | checkIcon :: forall w i. Array IconProp -> HH.HTML w i
// | checkIcon props = icon props "M20 6L9 17l-5-5"
// | ```
var icon = function (propMods) {
    return function (pathData) {
        return iconWith(propMods)([ pathElement(pathData) ]);
    };
};

// | Add custom class
var className = function (cls) {
    return function (props) {
        return {
            size: props.size,
            strokeWidth: props.strokeWidth,
            ariaLabel: props.ariaLabel,
            ariaHidden: props.ariaHidden,
            className: props.className + (" " + cls)
        };
    };
};

// | Create a circle element
var circleElement = function (cx) {
    return function (cy) {
        return function (r) {
            return svgElement("circle")([ Halogen_HTML_Properties.attr("cx")(show(cx)), Halogen_HTML_Properties.attr("cy")(show(cy)), Halogen_HTML_Properties.attr("r")(show(r)) ])([  ]);
        };
    };
};

// | Set aria-label (makes icon accessible)
var ariaLabel = function (label) {
    return function (props) {
        return {
            size: props.size,
            className: props.className,
            strokeWidth: props.strokeWidth,
            ariaLabel: new Data_Maybe.Just(label),
            ariaHidden: false
        };
    };
};

// | Set aria-hidden
var ariaHidden = function (hidden) {
    return function (props) {
        return {
            size: props.size,
            className: props.className,
            strokeWidth: props.strokeWidth,
            ariaLabel: props.ariaLabel,
            ariaHidden: hidden
        };
    };
};
export {
    defaultProps,
    size,
    className,
    strokeWidth,
    ariaLabel,
    ariaHidden,
    Xs,
    Sm,
    Md,
    Lg,
    Xl,
    Xxl,
    Custom,
    iconSizeClass,
    iconSizePx,
    icon,
    iconWith,
    svgIcon,
    svgElement,
    pathElement,
    circleElement,
    rectElement,
    lineElement,
    polylineElement,
    polygonElement,
    eqIconSize
};
