// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                          // hydrogen // table
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Table component
// |
// | Styled data table components.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Component.Table as Table
// |
// | Table.table []
// |   [ Table.tableHeader []
// |       [ Table.tableRow []
// |           [ Table.tableHead [] [ HH.text "Name" ]
// |           , Table.tableHead [] [ HH.text "Status" ]
// |           ]
// |       ]
// |   , Table.tableBody []
// |       [ Table.tableRow []
// |           [ Table.tableCell [] [ HH.text "John" ]
// |           , Table.tableCell [] [ HH.text "Active" ]
// |           ]
// |       ]
// |   ]
// | ```
import * as Data_Array from "../Data.Array/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";
var defaultProps = {
    className: ""
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // components
// ═══════════════════════════════════════════════════════════════════════════════
// | Table container
var table = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "relative w-full overflow-auto" ]) ])([ Halogen_HTML_Elements.table([ Hydrogen_UI_Core.cls([ "w-full caption-bottom text-sm", props.className ]) ])(children) ]);
    };
};

// | Table body
var tableBody = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.tbody([ Hydrogen_UI_Core.cls([ "[&_tr:last-child]:border-0", props.className ]) ])(children);
    };
};

// | Table caption
var tableCaption = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.caption([ Hydrogen_UI_Core.cls([ "mt-4 text-sm text-muted-foreground", props.className ]) ])(children);
    };
};

// | Table cell
var tableCell = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.td([ Hydrogen_UI_Core.cls([ "p-4 align-middle [&:has([role=checkbox])]:pr-0", props.className ]) ])(children);
    };
};

// | Table footer
var tableFooter = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.tfoot([ Hydrogen_UI_Core.cls([ "border-t bg-muted/50 font-medium [&>tr]:last:border-b-0", props.className ]) ])(children);
    };
};

// | Table header cell
var tableHead = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.th([ Hydrogen_UI_Core.cls([ "h-12 px-4 text-left align-middle font-medium text-muted-foreground [&:has([role=checkbox])]:pr-0", props.className ]) ])(children);
    };
};

// | Table header
var tableHeader = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.thead([ Hydrogen_UI_Core.cls([ "[&_tr]:border-b", props.className ]) ])(children);
    };
};

// | Table row
var tableRow = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.tr([ Hydrogen_UI_Core.cls([ "border-b transition-colors hover:bg-muted/50 data-[state=selected]:bg-muted", props.className ]) ])(children);
    };
};

// | Add custom class
var className = function (c) {
    return function (props) {
        return {
            className: props.className + (" " + c)
        };
    };
};
export {
    table,
    tableHeader,
    tableBody,
    tableFooter,
    tableRow,
    tableHead,
    tableCell,
    tableCaption,
    className
};
