// | Core UI utilities and primitives
// |
// | This module provides foundational UI utilities:
// | - Class name handling
// | - Layout primitives (flex, grid)
// | - Common patterns for Tailwind CSS
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Monoid from "../Data.Monoid/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Properties from "../Halogen.HTML.Properties/index.js";
import * as Web_HTML_Common from "../Web.HTML.Common/index.js";

// ============================================================
// SVG NAMESPACE
// ============================================================
// | SVG namespace for creating SVG elements
var svgNS = "http://www.w3.org/2000/svg";

// ============================================================
// CLASS UTILITIES
// ============================================================
// | Combine class names, filtering empty strings
// |
// | ```purescript
// | classes ["foo", "", "bar"] == "foo bar"
// | classes [] == ""
// | ```
var classes = /* #__PURE__ */ (function () {
    var $7 = Data_Array.intercalate(Data_Monoid.monoidString)(" ");
    var $8 = Data_Array.filter(function (v) {
        return v !== "";
    });
    return function ($9) {
        return $7($8($9));
    };
})();

// | Create HP.class_ from array of class strings
// |
// | NOTE: This uses the DOM property `className` which does NOT work on SVG elements.
// | For SVG elements, use `svgCls` instead.
// |
// | ```purescript
// | HH.div [ cls ["container", "mx-auto"] ] [ ... ]
// | ```
var cls = function ($10) {
    return Halogen_HTML_Properties.class_(Web_HTML_Common.ClassName(classes($10)));
};

// | Max-width centered container
// |
// | ```purescript
// | container "py-8" [ pageContent ]
// | ```
var container = function (className) {
    return Halogen_HTML_Elements.div([ cls([ "max-w-7xl mx-auto px-4 sm:px-6 lg:px-8", className ]) ]);
};

// ============================================================
// LAYOUT PRIMITIVES
// ============================================================
// | Configurable flex container
// |
// | ```purescript
// | flex 
// |   { direction: "column"
// |   , gap: "gap-4"
// |   , align: "center"
// |   , justify: "between"
// |   , className: "p-4"
// |   }
// |   [ child1, child2 ]
// | ```
var flex = function (opts) {
    return function (children) {
        return Halogen_HTML_Elements.div([ cls([ "flex", (function () {
            if (opts.direction === "column") {
                return "flex-col";
            };
            if (opts.direction === "col") {
                return "flex-col";
            };
            return "flex-row";
        })(), opts.gap, (function () {
            if (opts.align === "center") {
                return "items-center";
            };
            if (opts.align === "end") {
                return "items-end";
            };
            if (opts.align === "stretch") {
                return "items-stretch";
            };
            if (opts.align === "baseline") {
                return "items-baseline";
            };
            return "items-start";
        })(), (function () {
            if (opts.justify === "center") {
                return "justify-center";
            };
            if (opts.justify === "end") {
                return "justify-end";
            };
            if (opts.justify === "between") {
                return "justify-between";
            };
            if (opts.justify === "around") {
                return "justify-around";
            };
            if (opts.justify === "evenly") {
                return "justify-evenly";
            };
            return "justify-start";
        })(), opts.className ]) ])(children);
    };
};

// | Simple flex column with gap
// |
// | ```purescript
// | column "gap-2" [ heading, paragraph, button ]
// | ```
var column = function (gap) {
    return flex({
        direction: "column",
        gap: gap,
        align: "start",
        justify: "start",
        className: ""
    });
};

// | Simple flex row with gap
// |
// | ```purescript
// | row "gap-4" [ item1, item2, item3 ]
// | ```
var row = function (gap) {
    return flex({
        direction: "row",
        gap: gap,
        align: "center",
        justify: "start",
        className: ""
    });
};

// | Section wrapper
// |
// | ```purescript
// | section "py-16 bg-muted" [ sectionContent ]
// | ```
var section = function (className) {
    return Halogen_HTML_Elements.section([ cls([ className ]) ]);
};

// | Create class attribute for SVG elements
// |
// | SVG elements have `className` as a read-only SVGAnimatedString, so we must
// | use the `class` attribute instead of the `className` property.
// |
// | ```purescript
// | HH.elementNS svgNS "svg" [ svgCls ["w-6", "h-6"] ] [ ... ]
// | ```
var svgCls = function (arr) {
    return Halogen_HTML_Properties.attr("class")(classes(arr));
};

// | Generic box container with class name
// |
// | ```purescript
// | box "p-4 bg-card rounded" [ content ]
// | ```
var box = function (className) {
    return Halogen_HTML_Elements.div([ cls([ className ]) ]);
};
export {
    classes,
    cls,
    svgCls,
    flex,
    row,
    column,
    box,
    container,
    section,
    svgNS
};
