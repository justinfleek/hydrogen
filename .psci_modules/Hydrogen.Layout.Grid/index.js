// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                           // hydrogen // grid
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | CSS Grid layout components
// |
// | Type-safe CSS Grid utilities.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Layout.Grid as Grid
// |
// | -- Simple grid with 3 columns
// | Grid.grid [ Grid.cols 3, Grid.gap Grid.G4 ]
// |   [ item1, item2, item3, item4, item5, item6 ]
// |
// | -- Responsive grid
// | Grid.grid [ Grid.colsSm 1, Grid.colsMd 2, Grid.colsLg 3 ]
// |   [ items ]
// |
// | -- Grid item with span
// | Grid.gridItem [ Grid.colSpan 2 ]
// |   [ content ]
// | ```
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);

// | Set number of rows
var rows = function (n) {
    return function (props) {
        return {
            cols: props.cols,
            gap: props.gap,
            gapX: props.gapX,
            gapY: props.gapY,
            colsSm: props.colsSm,
            colsMd: props.colsMd,
            colsLg: props.colsLg,
            colsXl: props.colsXl,
            className: props.className,
            rows: new Data_Maybe.Just(n)
        };
    };
};

// | Row start
var rowStart = function (n) {
    return function (props) {
        return {
            colSpan: props.colSpan,
            colStart: props.colStart,
            colEnd: props.colEnd,
            rowSpan: props.rowSpan,
            rowEnd: props.rowEnd,
            className: props.className,
            rowStart: new Data_Maybe.Just(n)
        };
    };
};

// | Row span
var rowSpan = function (n) {
    return function (props) {
        return {
            colSpan: props.colSpan,
            colStart: props.colStart,
            colEnd: props.colEnd,
            rowStart: props.rowStart,
            rowEnd: props.rowEnd,
            className: props.className,
            rowSpan: new Data_Maybe.Just(n)
        };
    };
};

// | Row end
var rowEnd = function (n) {
    return function (props) {
        return {
            colSpan: props.colSpan,
            colStart: props.colStart,
            colEnd: props.colEnd,
            rowSpan: props.rowSpan,
            rowStart: props.rowStart,
            className: props.className,
            rowEnd: new Data_Maybe.Just(n)
        };
    };
};
var maybeClass = function (v) {
    return function (v1) {
        if (v1 instanceof Data_Maybe.Nothing) {
            return "";
        };
        if (v1 instanceof Data_Maybe.Just) {
            return v + (show(v1.value0) + " ");
        };
        throw new Error("Failed pattern match at Hydrogen.Layout.Grid (line 237, column 1 - line 237, column 44): " + [ v.constructor.name, v1.constructor.name ]);
    };
};

// | Set vertical gap
var gapY = function (n) {
    return function (props) {
        return {
            cols: props.cols,
            rows: props.rows,
            gap: props.gap,
            gapX: props.gapX,
            colsSm: props.colsSm,
            colsMd: props.colsMd,
            colsLg: props.colsLg,
            colsXl: props.colsXl,
            className: props.className,
            gapY: new Data_Maybe.Just(n)
        };
    };
};

// | Set horizontal gap
var gapX = function (n) {
    return function (props) {
        return {
            cols: props.cols,
            rows: props.rows,
            gap: props.gap,
            gapY: props.gapY,
            colsSm: props.colsSm,
            colsMd: props.colsMd,
            colsLg: props.colsLg,
            colsXl: props.colsXl,
            className: props.className,
            gapX: new Data_Maybe.Just(n)
        };
    };
};

// | Set gap (both x and y)
var gap = function (n) {
    return function (props) {
        return {
            cols: props.cols,
            rows: props.rows,
            gapX: props.gapX,
            gapY: props.gapY,
            colsSm: props.colsSm,
            colsMd: props.colsMd,
            colsLg: props.colsLg,
            colsXl: props.colsXl,
            className: props.className,
            gap: new Data_Maybe.Just(n)
        };
    };
};
var defaultItemProps = /* #__PURE__ */ (function () {
    return {
        colSpan: Data_Maybe.Nothing.value,
        colStart: Data_Maybe.Nothing.value,
        colEnd: Data_Maybe.Nothing.value,
        rowSpan: Data_Maybe.Nothing.value,
        rowStart: Data_Maybe.Nothing.value,
        rowEnd: Data_Maybe.Nothing.value,
        className: ""
    };
})();
var defaultGridProps = /* #__PURE__ */ (function () {
    return {
        cols: Data_Maybe.Nothing.value,
        rows: Data_Maybe.Nothing.value,
        gap: Data_Maybe.Nothing.value,
        gapX: Data_Maybe.Nothing.value,
        gapY: Data_Maybe.Nothing.value,
        colsSm: Data_Maybe.Nothing.value,
        colsMd: Data_Maybe.Nothing.value,
        colsLg: Data_Maybe.Nothing.value,
        colsXl: Data_Maybe.Nothing.value,
        className: ""
    };
})();

// | Columns at extra large breakpoint
var colsXl = function (n) {
    return function (props) {
        return {
            cols: props.cols,
            rows: props.rows,
            gap: props.gap,
            gapX: props.gapX,
            gapY: props.gapY,
            colsSm: props.colsSm,
            colsMd: props.colsMd,
            colsLg: props.colsLg,
            className: props.className,
            colsXl: new Data_Maybe.Just(n)
        };
    };
};

// | Columns at small breakpoint
var colsSm = function (n) {
    return function (props) {
        return {
            cols: props.cols,
            rows: props.rows,
            gap: props.gap,
            gapX: props.gapX,
            gapY: props.gapY,
            colsMd: props.colsMd,
            colsLg: props.colsLg,
            colsXl: props.colsXl,
            className: props.className,
            colsSm: new Data_Maybe.Just(n)
        };
    };
};

// | Columns at medium breakpoint
var colsMd = function (n) {
    return function (props) {
        return {
            cols: props.cols,
            rows: props.rows,
            gap: props.gap,
            gapX: props.gapX,
            gapY: props.gapY,
            colsSm: props.colsSm,
            colsLg: props.colsLg,
            colsXl: props.colsXl,
            className: props.className,
            colsMd: new Data_Maybe.Just(n)
        };
    };
};

// | Columns at large breakpoint
var colsLg = function (n) {
    return function (props) {
        return {
            cols: props.cols,
            rows: props.rows,
            gap: props.gap,
            gapX: props.gapX,
            gapY: props.gapY,
            colsSm: props.colsSm,
            colsMd: props.colsMd,
            colsXl: props.colsXl,
            className: props.className,
            colsLg: new Data_Maybe.Just(n)
        };
    };
};

// | Set number of columns
var cols = function (n) {
    return function (props) {
        return {
            rows: props.rows,
            gap: props.gap,
            gapX: props.gapX,
            gapY: props.gapY,
            colsSm: props.colsSm,
            colsMd: props.colsMd,
            colsLg: props.colsLg,
            colsXl: props.colsXl,
            className: props.className,
            cols: new Data_Maybe.Just(n)
        };
    };
};

// | Column start
var colStart = function (n) {
    return function (props) {
        return {
            colSpan: props.colSpan,
            colEnd: props.colEnd,
            rowSpan: props.rowSpan,
            rowStart: props.rowStart,
            rowEnd: props.rowEnd,
            className: props.className,
            colStart: new Data_Maybe.Just(n)
        };
    };
};

// | Column span
var colSpan = function (n) {
    return function (props) {
        return {
            colStart: props.colStart,
            colEnd: props.colEnd,
            rowSpan: props.rowSpan,
            rowStart: props.rowStart,
            rowEnd: props.rowEnd,
            className: props.className,
            colSpan: new Data_Maybe.Just(n)
        };
    };
};

// | Column end
var colEnd = function (n) {
    return function (props) {
        return {
            colSpan: props.colSpan,
            colStart: props.colStart,
            rowSpan: props.rowSpan,
            rowStart: props.rowStart,
            rowEnd: props.rowEnd,
            className: props.className,
            colEnd: new Data_Maybe.Just(n)
        };
    };
};

// | Add custom class
var className = function (c) {
    return function (props) {
        return {
            cols: props.cols,
            rows: props.rows,
            gap: props.gap,
            gapX: props.gapX,
            gapY: props.gapY,
            colsSm: props.colsSm,
            colsMd: props.colsMd,
            colsLg: props.colsLg,
            colsXl: props.colsXl,
            className: props.className + (" " + c)
        };
    };
};
var buildItemClasses = function (props) {
    return maybeClass("col-span-")(props.colSpan) + (maybeClass("col-start-")(props.colStart) + (maybeClass("col-end-")(props.colEnd) + (maybeClass("row-span-")(props.rowSpan) + (maybeClass("row-start-")(props.rowStart) + maybeClass("row-end-")(props.rowEnd)))));
};

// | Grid item
var gridItem = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultItemProps)(propMods);
        var classes = buildItemClasses(props);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ classes, props.className ]) ])(children);
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // helpers
// ═══════════════════════════════════════════════════════════════════════════════
var buildGridClasses = function (props) {
    return maybeClass("grid-cols-")(props.cols) + (maybeClass("grid-rows-")(props.rows) + (maybeClass("gap-")(props.gap) + (maybeClass("gap-x-")(props.gapX) + (maybeClass("gap-y-")(props.gapY) + (maybeClass("sm:grid-cols-")(props.colsSm) + (maybeClass("md:grid-cols-")(props.colsMd) + (maybeClass("lg:grid-cols-")(props.colsLg) + maybeClass("xl:grid-cols-")(props.colsXl))))))));
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // components
// ═══════════════════════════════════════════════════════════════════════════════
// | Grid container
var grid = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultGridProps)(propMods);
        var classes = buildGridClasses(props);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "grid", classes, props.className ]) ])(children);
    };
};
export {
    grid,
    gridItem,
    cols,
    rows,
    gap,
    gapX,
    gapY,
    className,
    colsSm,
    colsMd,
    colsLg,
    colsXl,
    colSpan,
    colStart,
    colEnd,
    rowSpan,
    rowStart,
    rowEnd
};
