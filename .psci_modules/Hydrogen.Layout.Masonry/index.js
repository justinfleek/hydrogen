// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                        // hydrogen // masonry
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Masonry grid layout component
// |
// | Column-based masonry layout for variable-height content like
// | image galleries, cards, and pinterest-style layouts.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Layout.Masonry as Masonry
// |
// | -- Basic masonry with 3 columns
// | Masonry.masonry [ Masonry.columns 3 ]
// |   [ item1, item2, item3, item4, item5 ]
// |
// | -- Responsive columns
// | Masonry.masonry
// |   [ Masonry.columnsSm 1
// |   , Masonry.columnsMd 2
// |   , Masonry.columnsLg 3
// |   , Masonry.gap Masonry.G4
// |   ]
// |   [ items ]
// |
// | -- With custom gap
// | Masonry.masonry [ Masonry.columns 4, Masonry.gap Masonry.G6 ]
// |   [ galleryItems ]
// | ```
import * as $foreign from "./foreign.js";
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Semigroup from "../Data.Semigroup/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Effect_Uncurried from "../Effect.Uncurried/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Properties from "../Halogen.HTML.Properties/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);
var append1 = /* #__PURE__ */ Data_Semigroup.append(Data_Semigroup.semigroupArray);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                         // gap
// ═══════════════════════════════════════════════════════════════════════════════
// | Gap sizes
var G0 = /* #__PURE__ */ (function () {
    function G0() {

    };
    G0.value = new G0();
    return G0;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                         // gap
// ═══════════════════════════════════════════════════════════════════════════════
// | Gap sizes
var G1 = /* #__PURE__ */ (function () {
    function G1() {

    };
    G1.value = new G1();
    return G1;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                         // gap
// ═══════════════════════════════════════════════════════════════════════════════
// | Gap sizes
var G2 = /* #__PURE__ */ (function () {
    function G2() {

    };
    G2.value = new G2();
    return G2;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                         // gap
// ═══════════════════════════════════════════════════════════════════════════════
// | Gap sizes
var G3 = /* #__PURE__ */ (function () {
    function G3() {

    };
    G3.value = new G3();
    return G3;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                         // gap
// ═══════════════════════════════════════════════════════════════════════════════
// | Gap sizes
var G4 = /* #__PURE__ */ (function () {
    function G4() {

    };
    G4.value = new G4();
    return G4;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                         // gap
// ═══════════════════════════════════════════════════════════════════════════════
// | Gap sizes
var G5 = /* #__PURE__ */ (function () {
    function G5() {

    };
    G5.value = new G5();
    return G5;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                         // gap
// ═══════════════════════════════════════════════════════════════════════════════
// | Gap sizes
var G6 = /* #__PURE__ */ (function () {
    function G6() {

    };
    G6.value = new G6();
    return G6;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                         // gap
// ═══════════════════════════════════════════════════════════════════════════════
// | Gap sizes
var G8 = /* #__PURE__ */ (function () {
    function G8() {

    };
    G8.value = new G8();
    return G8;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                         // gap
// ═══════════════════════════════════════════════════════════════════════════════
// | Gap sizes
var G10 = /* #__PURE__ */ (function () {
    function G10() {

    };
    G10.value = new G10();
    return G10;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                         // gap
// ═══════════════════════════════════════════════════════════════════════════════
// | Gap sizes
var G12 = /* #__PURE__ */ (function () {
    function G12() {

    };
    G12.value = new G12();
    return G12;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                         // gap
// ═══════════════════════════════════════════════════════════════════════════════
// | Gap sizes
var G16 = /* #__PURE__ */ (function () {
    function G16() {

    };
    G16.value = new G16();
    return G16;
})();

// | Hook for masonry initialization
var useMasonry = function (selector) {
    return function () {
        return $foreign.initMasonry(selector);
    };
};

// | Trigger relayout
var relayout = /* #__PURE__ */ Effect_Uncurried.runEffectFn1($foreign.relayoutImpl);

// | Set item order mode
var order = function (o) {
    return function (props) {
        return {
            columns: props.columns,
            columnsSm: props.columnsSm,
            columnsMd: props.columnsMd,
            columnsLg: props.columnsLg,
            columnsXl: props.columnsXl,
            gap: props.gap,
            className: props.className,
            order: o
        };
    };
};

// | Item column span
var itemSpan = function (n) {
    return function (props) {
        return {
            order: props.order,
            className: props.className,
            span: n
        };
    };
};

// | Item order
var itemOrder = function (n) {
    return function (props) {
        return {
            span: props.span,
            className: props.className,
            order: new Data_Maybe.Just(n)
        };
    };
};

// | Add custom class to item
var itemClassName = function (c) {
    return function (props) {
        return {
            span: props.span,
            order: props.order,
            className: props.className + (" " + c)
        };
    };
};
var gapClass = function (v) {
    if (v instanceof G0) {
        return "gap-0";
    };
    if (v instanceof G1) {
        return "gap-1";
    };
    if (v instanceof G2) {
        return "gap-2";
    };
    if (v instanceof G3) {
        return "gap-3";
    };
    if (v instanceof G4) {
        return "gap-4";
    };
    if (v instanceof G5) {
        return "gap-5";
    };
    if (v instanceof G6) {
        return "gap-6";
    };
    if (v instanceof G8) {
        return "gap-8";
    };
    if (v instanceof G10) {
        return "gap-10";
    };
    if (v instanceof G12) {
        return "gap-12";
    };
    if (v instanceof G16) {
        return "gap-16";
    };
    throw new Error("Failed pattern match at Hydrogen.Layout.Masonry (line 92, column 12 - line 103, column 18): " + [ v.constructor.name ]);
};

// | Set gap
var gap = function (g) {
    return function (props) {
        return {
            columns: props.columns,
            columnsSm: props.columnsSm,
            columnsMd: props.columnsMd,
            columnsLg: props.columnsLg,
            columnsXl: props.columnsXl,
            order: props.order,
            className: props.className,
            gap: g
        };
    };
};
var eqGap = {
    eq: function (x) {
        return function (y) {
            if (x instanceof G0 && y instanceof G0) {
                return true;
            };
            if (x instanceof G1 && y instanceof G1) {
                return true;
            };
            if (x instanceof G2 && y instanceof G2) {
                return true;
            };
            if (x instanceof G3 && y instanceof G3) {
                return true;
            };
            if (x instanceof G4 && y instanceof G4) {
                return true;
            };
            if (x instanceof G5 && y instanceof G5) {
                return true;
            };
            if (x instanceof G6 && y instanceof G6) {
                return true;
            };
            if (x instanceof G8 && y instanceof G8) {
                return true;
            };
            if (x instanceof G10 && y instanceof G10) {
                return true;
            };
            if (x instanceof G12 && y instanceof G12) {
                return true;
            };
            if (x instanceof G16 && y instanceof G16) {
                return true;
            };
            return false;
        };
    }
};
var defaultProps = /* #__PURE__ */ (function () {
    return {
        columns: 3,
        columnsSm: Data_Maybe.Nothing.value,
        columnsMd: Data_Maybe.Nothing.value,
        columnsLg: Data_Maybe.Nothing.value,
        columnsXl: Data_Maybe.Nothing.value,
        gap: G4.value,
        order: "default",
        className: ""
    };
})();
var defaultItemProps = /* #__PURE__ */ (function () {
    return {
        span: 1,
        order: Data_Maybe.Nothing.value,
        className: ""
    };
})();

// | Masonry item wrapper
// |
// | Prevents items from being split across columns and adds
// | proper spacing.
var masonryItem = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultItemProps)(propMods);
        var orderStyle = (function () {
            if (props.order instanceof Data_Maybe.Just) {
                return [ Halogen_HTML_Properties.style("order: " + show(props.order.value0)) ];
            };
            if (props.order instanceof Data_Maybe.Nothing) {
                return [  ];
            };
            throw new Error("Failed pattern match at Hydrogen.Layout.Masonry (line 267, column 18 - line 269, column 20): " + [ props.order.constructor.name ]);
        })();
        return Halogen_HTML_Elements.div(append1([ Hydrogen_UI_Core.cls([ "break-inside-avoid mb-4", props.className ]) ])(orderStyle))(children);
    };
};

// | Columns at extra-large breakpoint
var columnsXl = function (n) {
    return function (props) {
        return {
            columns: props.columns,
            columnsSm: props.columnsSm,
            columnsMd: props.columnsMd,
            columnsLg: props.columnsLg,
            gap: props.gap,
            order: props.order,
            className: props.className,
            columnsXl: new Data_Maybe.Just(n)
        };
    };
};

// | Columns at small breakpoint
var columnsSm = function (n) {
    return function (props) {
        return {
            columns: props.columns,
            columnsMd: props.columnsMd,
            columnsLg: props.columnsLg,
            columnsXl: props.columnsXl,
            gap: props.gap,
            order: props.order,
            className: props.className,
            columnsSm: new Data_Maybe.Just(n)
        };
    };
};

// | Columns at medium breakpoint
var columnsMd = function (n) {
    return function (props) {
        return {
            columns: props.columns,
            columnsSm: props.columnsSm,
            columnsLg: props.columnsLg,
            columnsXl: props.columnsXl,
            gap: props.gap,
            order: props.order,
            className: props.className,
            columnsMd: new Data_Maybe.Just(n)
        };
    };
};

// | Columns at large breakpoint
var columnsLg = function (n) {
    return function (props) {
        return {
            columns: props.columns,
            columnsSm: props.columnsSm,
            columnsMd: props.columnsMd,
            columnsXl: props.columnsXl,
            gap: props.gap,
            order: props.order,
            className: props.className,
            columnsLg: new Data_Maybe.Just(n)
        };
    };
};

// | Set number of columns
var columns = function (n) {
    return function (props) {
        return {
            columnsSm: props.columnsSm,
            columnsMd: props.columnsMd,
            columnsLg: props.columnsLg,
            columnsXl: props.columnsXl,
            gap: props.gap,
            order: props.order,
            className: props.className,
            columns: n
        };
    };
};

// | Add custom class
var className = function (c) {
    return function (props) {
        return {
            columns: props.columns,
            columnsSm: props.columnsSm,
            columnsMd: props.columnsMd,
            columnsLg: props.columnsLg,
            columnsXl: props.columnsXl,
            gap: props.gap,
            order: props.order,
            className: props.className + (" " + c)
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // components
// ═══════════════════════════════════════════════════════════════════════════════
// | Build column classes for CSS columns masonry
var buildColumnClasses = function (props) {
    var xl = (function () {
        if (props.columnsXl instanceof Data_Maybe.Just) {
            return "xl:columns-" + show(props.columnsXl.value0);
        };
        if (props.columnsXl instanceof Data_Maybe.Nothing) {
            return "";
        };
        throw new Error("Failed pattern match at Hydrogen.Layout.Masonry (line 236, column 10 - line 238, column 20): " + [ props.columnsXl.constructor.name ]);
    })();
    var sm = (function () {
        if (props.columnsSm instanceof Data_Maybe.Just) {
            return "sm:columns-" + show(props.columnsSm.value0);
        };
        if (props.columnsSm instanceof Data_Maybe.Nothing) {
            return "";
        };
        throw new Error("Failed pattern match at Hydrogen.Layout.Masonry (line 227, column 10 - line 229, column 20): " + [ props.columnsSm.constructor.name ]);
    })();
    var md = (function () {
        if (props.columnsMd instanceof Data_Maybe.Just) {
            return "md:columns-" + show(props.columnsMd.value0);
        };
        if (props.columnsMd instanceof Data_Maybe.Nothing) {
            return "";
        };
        throw new Error("Failed pattern match at Hydrogen.Layout.Masonry (line 230, column 10 - line 232, column 20): " + [ props.columnsMd.constructor.name ]);
    })();
    var lg = (function () {
        if (props.columnsLg instanceof Data_Maybe.Just) {
            return "lg:columns-" + show(props.columnsLg.value0);
        };
        if (props.columnsLg instanceof Data_Maybe.Nothing) {
            return "";
        };
        throw new Error("Failed pattern match at Hydrogen.Layout.Masonry (line 233, column 10 - line 235, column 20): " + [ props.columnsLg.constructor.name ]);
    })();
    var base = "columns-" + show(props.columns);
    return base + (" " + (sm + (" " + (md + (" " + (lg + (" " + xl)))))));
};

// | Masonry grid container
// |
// | Uses CSS columns for a pure-CSS masonry effect. Items flow
// | top-to-bottom within each column. For true JS-based masonry
// | with horizontal ordering, use `useMasonry` hook.
var masonry = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        var columnClasses = buildColumnClasses(props);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ columnClasses, gapClass(props.gap), props.className ]), Halogen_HTML_Properties.attr("data-masonry")("true") ])(children);
    };
};
export {
    masonry,
    masonryItem,
    columns,
    columnsSm,
    columnsMd,
    columnsLg,
    columnsXl,
    gap,
    order,
    className,
    itemSpan,
    itemOrder,
    itemClassName,
    G0,
    G1,
    G2,
    G3,
    G4,
    G5,
    G6,
    G8,
    G10,
    G12,
    G16,
    useMasonry,
    relayout,
    eqGap
};
