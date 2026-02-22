// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                      // hydrogen // container
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Responsive container component
// |
// | Provides max-width constrained containers with responsive padding
// | and optional fluid mode. Based on common layout patterns.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Layout.Container as Container
// |
// | -- Default container (centered, max-width, responsive padding)
// | Container.container []
// |   [ pageContent ]
// |
// | -- Narrow container for readable content
// | Container.container [ Container.size Container.Narrow ]
// |   [ articleContent ]
// |
// | -- Fluid container (full width with padding)
// | Container.container [ Container.fluid true ]
// |   [ fullWidthContent ]
// |
// | -- Custom padding
// | Container.container [ Container.padding Container.PaddingLg ]
// |   [ content ]
// | ```
import * as Data_Array from "../Data.Array/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                        // size
// ═══════════════════════════════════════════════════════════════════════════════
// | Container size presets
var ExtraSmall = /* #__PURE__ */ (function () {
    function ExtraSmall() {

    };
    ExtraSmall.value = new ExtraSmall();
    return ExtraSmall;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                        // size
// ═══════════════════════════════════════════════════════════════════════════════
// | Container size presets
var Small = /* #__PURE__ */ (function () {
    function Small() {

    };
    Small.value = new Small();
    return Small;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                        // size
// ═══════════════════════════════════════════════════════════════════════════════
// | Container size presets
var Medium = /* #__PURE__ */ (function () {
    function Medium() {

    };
    Medium.value = new Medium();
    return Medium;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                        // size
// ═══════════════════════════════════════════════════════════════════════════════
// | Container size presets
var Large = /* #__PURE__ */ (function () {
    function Large() {

    };
    Large.value = new Large();
    return Large;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                        // size
// ═══════════════════════════════════════════════════════════════════════════════
// | Container size presets
var ExtraLarge = /* #__PURE__ */ (function () {
    function ExtraLarge() {

    };
    ExtraLarge.value = new ExtraLarge();
    return ExtraLarge;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                        // size
// ═══════════════════════════════════════════════════════════════════════════════
// | Container size presets
var TwoXL = /* #__PURE__ */ (function () {
    function TwoXL() {

    };
    TwoXL.value = new TwoXL();
    return TwoXL;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                        // size
// ═══════════════════════════════════════════════════════════════════════════════
// | Container size presets
var Full = /* #__PURE__ */ (function () {
    function Full() {

    };
    Full.value = new Full();
    return Full;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                        // size
// ═══════════════════════════════════════════════════════════════════════════════
// | Container size presets
var Narrow = /* #__PURE__ */ (function () {
    function Narrow() {

    };
    Narrow.value = new Narrow();
    return Narrow;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                        // size
// ═══════════════════════════════════════════════════════════════════════════════
// | Container size presets
var Wide = /* #__PURE__ */ (function () {
    function Wide() {

    };
    Wide.value = new Wide();
    return Wide;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // padding
// ═══════════════════════════════════════════════════════════════════════════════
// | Padding presets with responsive values
var PaddingNone = /* #__PURE__ */ (function () {
    function PaddingNone() {

    };
    PaddingNone.value = new PaddingNone();
    return PaddingNone;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // padding
// ═══════════════════════════════════════════════════════════════════════════════
// | Padding presets with responsive values
var PaddingSm = /* #__PURE__ */ (function () {
    function PaddingSm() {

    };
    PaddingSm.value = new PaddingSm();
    return PaddingSm;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // padding
// ═══════════════════════════════════════════════════════════════════════════════
// | Padding presets with responsive values
var PaddingMd = /* #__PURE__ */ (function () {
    function PaddingMd() {

    };
    PaddingMd.value = new PaddingMd();
    return PaddingMd;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // padding
// ═══════════════════════════════════════════════════════════════════════════════
// | Padding presets with responsive values
var PaddingLg = /* #__PURE__ */ (function () {
    function PaddingLg() {

    };
    PaddingLg.value = new PaddingLg();
    return PaddingLg;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // padding
// ═══════════════════════════════════════════════════════════════════════════════
// | Padding presets with responsive values
var PaddingXl = /* #__PURE__ */ (function () {
    function PaddingXl() {

    };
    PaddingXl.value = new PaddingXl();
    return PaddingXl;
})();
var sizeClass = function (v) {
    if (v instanceof ExtraSmall) {
        return "max-w-screen-sm";
    };
    if (v instanceof Small) {
        return "max-w-screen-sm";
    };
    if (v instanceof Medium) {
        return "max-w-screen-md";
    };
    if (v instanceof Large) {
        return "max-w-screen-lg";
    };
    if (v instanceof ExtraLarge) {
        return "max-w-screen-xl";
    };
    if (v instanceof TwoXL) {
        return "max-w-screen-2xl";
    };
    if (v instanceof Full) {
        return "";
    };
    if (v instanceof Narrow) {
        return "max-w-2xl";
    };
    if (v instanceof Wide) {
        return "max-w-7xl";
    };
    throw new Error("Failed pattern match at Hydrogen.Layout.Container (line 73, column 13 - line 82, column 22): " + [ v.constructor.name ]);
};

// | Set the container size
var size = function (s) {
    return function (props) {
        return {
            padding: props.padding,
            fluid: props.fluid,
            centered: props.centered,
            className: props.className,
            size: s
        };
    };
};
var paddingClass = function (v) {
    if (v instanceof PaddingNone) {
        return "";
    };
    if (v instanceof PaddingSm) {
        return "px-2 sm:px-3";
    };
    if (v instanceof PaddingMd) {
        return "px-4 sm:px-6 lg:px-8";
    };
    if (v instanceof PaddingLg) {
        return "px-6 sm:px-8 lg:px-12";
    };
    if (v instanceof PaddingXl) {
        return "px-8 sm:px-12 lg:px-16";
    };
    throw new Error("Failed pattern match at Hydrogen.Layout.Container (line 99, column 16 - line 104, column 40): " + [ v.constructor.name ]);
};

// | Set padding
var padding = function (p) {
    return function (props) {
        return {
            size: props.size,
            fluid: props.fluid,
            centered: props.centered,
            className: props.className,
            padding: p
        };
    };
};

// | Enable fluid mode (full width)
var fluid = function (f) {
    return function (props) {
        return {
            size: props.size,
            padding: props.padding,
            centered: props.centered,
            className: props.className,
            fluid: f
        };
    };
};
var eqSize = {
    eq: function (x) {
        return function (y) {
            if (x instanceof ExtraSmall && y instanceof ExtraSmall) {
                return true;
            };
            if (x instanceof Small && y instanceof Small) {
                return true;
            };
            if (x instanceof Medium && y instanceof Medium) {
                return true;
            };
            if (x instanceof Large && y instanceof Large) {
                return true;
            };
            if (x instanceof ExtraLarge && y instanceof ExtraLarge) {
                return true;
            };
            if (x instanceof TwoXL && y instanceof TwoXL) {
                return true;
            };
            if (x instanceof Full && y instanceof Full) {
                return true;
            };
            if (x instanceof Narrow && y instanceof Narrow) {
                return true;
            };
            if (x instanceof Wide && y instanceof Wide) {
                return true;
            };
            return false;
        };
    }
};
var eqPadding = {
    eq: function (x) {
        return function (y) {
            if (x instanceof PaddingNone && y instanceof PaddingNone) {
                return true;
            };
            if (x instanceof PaddingSm && y instanceof PaddingSm) {
                return true;
            };
            if (x instanceof PaddingMd && y instanceof PaddingMd) {
                return true;
            };
            if (x instanceof PaddingLg && y instanceof PaddingLg) {
                return true;
            };
            if (x instanceof PaddingXl && y instanceof PaddingXl) {
                return true;
            };
            return false;
        };
    }
};
var defaultProps = /* #__PURE__ */ (function () {
    return {
        size: Wide.value,
        padding: PaddingMd.value,
        fluid: false,
        centered: true,
        className: ""
    };
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // component
// ═══════════════════════════════════════════════════════════════════════════════
// | Responsive container
// |
// | Provides a centered, max-width constrained container with responsive
// | horizontal padding. The container adapts to different screen sizes.
var container = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        var sizeCls = (function () {
            if (props.fluid) {
                return "";
            };
            return sizeClass(props.size);
        })();
        var widthCls = (function () {
            if (props.fluid) {
                return "w-full";
            };
            return "w-full";
        })();
        var paddingCls = paddingClass(props.padding);
        var centerCls = (function () {
            if (props.centered) {
                return "mx-auto";
            };
            return "";
        })();
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ widthCls, sizeCls, paddingCls, centerCls, props.className ]) ])(children);
    };
};

// | Add custom class
var className = function (c) {
    return function (props) {
        return {
            size: props.size,
            padding: props.padding,
            fluid: props.fluid,
            centered: props.centered,
            className: props.className + (" " + c)
        };
    };
};

// | Center the container
var centered = function (c) {
    return function (props) {
        return {
            size: props.size,
            padding: props.padding,
            fluid: props.fluid,
            className: props.className,
            centered: c
        };
    };
};
export {
    container,
    size,
    padding,
    fluid,
    centered,
    className,
    ExtraSmall,
    Small,
    Medium,
    Large,
    ExtraLarge,
    TwoXL,
    Full,
    Narrow,
    Wide,
    PaddingNone,
    PaddingSm,
    PaddingMd,
    PaddingLg,
    PaddingXl,
    eqSize,
    eqPadding
};
