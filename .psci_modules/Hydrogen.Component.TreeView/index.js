// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                       // hydrogen // treeview
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Hierarchical TreeView component
// |
// | A feature-rich tree component for displaying hierarchical data with
// | support for expand/collapse, selection, drag-and-drop, and virtualization.
// |
// | ## Features
// |
// | - Tree nodes with expand/collapse
// | - Multiple indentation levels
// | - Custom node icons (folder, file, etc.)
// | - Single and multiple selection
// | - Checkbox selection with indeterminate state
// | - Lazy loading of children
// | - Drag and drop reordering
// | - Keyboard navigation
// | - Search/filter functionality
// | - Virtualized rendering for large trees
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Component.TreeView as TreeView
// |
// | -- Basic tree
// | TreeView.treeView
// |   [ TreeView.onSelect HandleSelect ]
// |   [ TreeView.treeNode
// |       [ TreeView.nodeId "root"
// |       , TreeView.label "Root Folder"
// |       , TreeView.icon TreeView.FolderIcon
// |       , TreeView.expanded true
// |       ]
// |       [ TreeView.treeNode
// |           [ TreeView.nodeId "child1"
// |           , TreeView.label "Document.txt"
// |           , TreeView.icon TreeView.FileIcon
// |           ]
// |           []
// |       ]
// |   ]
// |
// | -- With checkboxes
// | TreeView.treeView
// |   [ TreeView.checkable true
// |   , TreeView.onCheck HandleCheck
// |   ]
// |   nodes
// |
// | -- With search filter
// | TreeView.treeView
// |   [ TreeView.searchable true
// |   , TreeView.searchQuery "document"
// |   , TreeView.onSearchChange HandleSearch
// |   ]
// |   nodes
// |
// | -- Lazy loading
// | TreeView.treeView
// |   [ TreeView.onLoadChildren HandleLoadChildren ]
// |   [ TreeView.treeNode
// |       [ TreeView.nodeId "lazy"
// |       , TreeView.label "Lazy Folder"
// |       , TreeView.hasChildren true
// |       , TreeView.loading false
// |       ]
// |       []
// |   ]
// | ```
import * as $foreign from "./foreign.js";
import * as Control_Applicative from "../Control.Applicative/index.js";
import * as DOM_HTML_Indexed_ButtonType from "../DOM.HTML.Indexed.ButtonType/index.js";
import * as DOM_HTML_Indexed_InputType from "../DOM.HTML.Indexed.InputType/index.js";
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Semigroup from "../Data.Semigroup/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
import * as Effect from "../Effect/index.js";
import * as Halogen_HTML_Core from "../Halogen.HTML.Core/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Properties from "../Halogen.HTML.Properties/index.js";
import * as Halogen_HTML_Properties_ARIA from "../Halogen.HTML.Properties.ARIA/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";
var type_ = /* #__PURE__ */ Halogen_HTML_Properties.type_(Halogen_HTML_Core.isPropButtonType);
var pure = /* #__PURE__ */ Control_Applicative.pure(Effect.applicativeEffect);
var type_1 = /* #__PURE__ */ Halogen_HTML_Properties.type_(Halogen_HTML_Core.isPropInputType);
var value = /* #__PURE__ */ Halogen_HTML_Properties.value(Halogen_HTML_Core.isPropString);
var append1 = /* #__PURE__ */ Data_Semigroup.append(Data_Semigroup.semigroupArray);
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);
var show1 = /* #__PURE__ */ Data_Show.show(Data_Show.showBoolean);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Selection mode for tree
var SingleSelect = /* #__PURE__ */ (function () {
    function SingleSelect() {

    };
    SingleSelect.value = new SingleSelect();
    return SingleSelect;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Selection mode for tree
var MultiSelect = /* #__PURE__ */ (function () {
    function MultiSelect() {

    };
    MultiSelect.value = new MultiSelect();
    return MultiSelect;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Selection mode for tree
var NoSelect = /* #__PURE__ */ (function () {
    function NoSelect() {

    };
    NoSelect.value = new NoSelect();
    return NoSelect;
})();

// | Built-in node icons
var FolderIcon = /* #__PURE__ */ (function () {
    function FolderIcon() {

    };
    FolderIcon.value = new FolderIcon();
    return FolderIcon;
})();

// | Built-in node icons
var FolderOpenIcon = /* #__PURE__ */ (function () {
    function FolderOpenIcon() {

    };
    FolderOpenIcon.value = new FolderOpenIcon();
    return FolderOpenIcon;
})();

// | Built-in node icons
var FileIcon = /* #__PURE__ */ (function () {
    function FileIcon() {

    };
    FileIcon.value = new FileIcon();
    return FileIcon;
})();

// | Built-in node icons
var FileTextIcon = /* #__PURE__ */ (function () {
    function FileTextIcon() {

    };
    FileTextIcon.value = new FileTextIcon();
    return FileTextIcon;
})();

// | Built-in node icons
var FileCodeIcon = /* #__PURE__ */ (function () {
    function FileCodeIcon() {

    };
    FileCodeIcon.value = new FileCodeIcon();
    return FileCodeIcon;
})();

// | Built-in node icons
var CustomIcon = /* #__PURE__ */ (function () {
    function CustomIcon(value0) {
        this.value0 = value0;
    };
    CustomIcon.create = function (value0) {
        return new CustomIcon(value0);
    };
    return CustomIcon;
})();

// | Drop position for drag and drop
var Before = /* #__PURE__ */ (function () {
    function Before() {

    };
    Before.value = new Before();
    return Before;
})();

// | Drop position for drag and drop
var After = /* #__PURE__ */ (function () {
    function After() {

    };
    After.value = new After();
    return After;
})();

// | Drop position for drag and drop
var Inside = /* #__PURE__ */ (function () {
    function Inside() {

    };
    Inside.value = new Inside();
    return Inside;
})();

// | Checkbox state
var Unchecked = /* #__PURE__ */ (function () {
    function Unchecked() {

    };
    Unchecked.value = new Unchecked();
    return Unchecked;
})();

// | Checkbox state
var Checked = /* #__PURE__ */ (function () {
    function Checked() {

    };
    Checked.value = new Checked();
    return Checked;
})();

// | Checkbox state
var Indeterminate = /* #__PURE__ */ (function () {
    function Indeterminate() {

    };
    Indeterminate.value = new Indeterminate();
    return Indeterminate;
})();

// | Calculate depth for nested rendering
var withDepth = function (d) {
    return function (props) {
        return {
            nodeId: props.nodeId,
            label: props.label,
            icon: props.icon,
            expanded: props.expanded,
            selected: props.selected,
            checked: props.checked,
            indeterminate: props.indeterminate,
            disabled: props.disabled,
            hasChildren: props.hasChildren,
            loading: props.loading,
            className: props.className,
            depth: d
        };
    };
};

// | Enable virtualized rendering
var virtualized = function (v) {
    return function (props) {
        return {
            selectionMode: props.selectionMode,
            checkable: props.checkable,
            draggable: props.draggable,
            searchable: props.searchable,
            searchQuery: props.searchQuery,
            className: props.className,
            onSelect: props.onSelect,
            onCheck: props.onCheck,
            onExpand: props.onExpand,
            onDrop: props.onDrop,
            onSearchChange: props.onSearchChange,
            onLoadChildren: props.onLoadChildren,
            virtualized: v
        };
    };
};

// | Tree node content (custom slot)
// |
// | For rendering custom content inside a node
var treeNodeContent = function (customClass) {
    return function (children) {
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "tree-node-content", customClass ]) ])(children);
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // prop builders
// ═══════════════════════════════════════════════════════════════════════════════
// | Set selection mode
var selectionMode = function (m) {
    return function (props) {
        return {
            checkable: props.checkable,
            draggable: props.draggable,
            searchable: props.searchable,
            searchQuery: props.searchQuery,
            virtualized: props.virtualized,
            className: props.className,
            onSelect: props.onSelect,
            onCheck: props.onCheck,
            onExpand: props.onExpand,
            onDrop: props.onDrop,
            onSearchChange: props.onSearchChange,
            onLoadChildren: props.onLoadChildren,
            selectionMode: m
        };
    };
};

// | Set selected state
var selected = function (s) {
    return function (props) {
        return {
            nodeId: props.nodeId,
            label: props.label,
            icon: props.icon,
            expanded: props.expanded,
            checked: props.checked,
            indeterminate: props.indeterminate,
            disabled: props.disabled,
            hasChildren: props.hasChildren,
            loading: props.loading,
            className: props.className,
            depth: props.depth,
            selected: s
        };
    };
};

// | Enable search/filter
var searchable = function (s) {
    return function (props) {
        return {
            selectionMode: props.selectionMode,
            checkable: props.checkable,
            draggable: props.draggable,
            searchQuery: props.searchQuery,
            virtualized: props.virtualized,
            className: props.className,
            onSelect: props.onSelect,
            onCheck: props.onCheck,
            onExpand: props.onExpand,
            onDrop: props.onDrop,
            onSearchChange: props.onSearchChange,
            onLoadChildren: props.onLoadChildren,
            searchable: s
        };
    };
};

// | Set search query
var searchQuery = function (q) {
    return function (props) {
        return {
            selectionMode: props.selectionMode,
            checkable: props.checkable,
            draggable: props.draggable,
            searchable: props.searchable,
            virtualized: props.virtualized,
            className: props.className,
            onSelect: props.onSelect,
            onCheck: props.onCheck,
            onExpand: props.onExpand,
            onDrop: props.onDrop,
            onSearchChange: props.onSearchChange,
            onLoadChildren: props.onLoadChildren,
            searchQuery: q
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // helpers
// ═══════════════════════════════════════════════════════════════════════════════
// | Render checkbox for checkable trees
var renderCheckbox = function (props) {
    var stateClasses = (function () {
        if (props.checked instanceof Checked) {
            return " bg-primary text-primary-foreground";
        };
        if (props.checked instanceof Indeterminate) {
            return " bg-primary text-primary-foreground";
        };
        if (props.checked instanceof Unchecked) {
            return " bg-background";
        };
        throw new Error("Failed pattern match at Hydrogen.Component.TreeView (line 572, column 20 - line 575, column 36): " + [ props.checked.constructor.name ]);
    })();
    var checkMark = (function () {
        if (props.checked instanceof Checked) {
            return Halogen_HTML_Core.text("\u2713");
        };
        if (props.checked instanceof Indeterminate) {
            return Halogen_HTML_Core.text("\u2212");
        };
        if (props.checked instanceof Unchecked) {
            return Halogen_HTML_Core.text("");
        };
        throw new Error("Failed pattern match at Hydrogen.Component.TreeView (line 577, column 17 - line 580, column 30): " + [ props.checked.constructor.name ]);
    })();
    return Halogen_HTML_Elements.button([ Hydrogen_UI_Core.cls([ "h-4 w-4 shrink-0 rounded border border-primary ring-offset-background focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2" + stateClasses ]), type_(DOM_HTML_Indexed_ButtonType.ButtonButton.value), Halogen_HTML_Properties_ARIA.role("checkbox"), Halogen_HTML_Properties_ARIA.checked((function () {
        if (props.checked instanceof Checked) {
            return "true";
        };
        if (props.checked instanceof Indeterminate) {
            return "mixed";
        };
        if (props.checked instanceof Unchecked) {
            return "false";
        };
        throw new Error("Failed pattern match at Hydrogen.Component.TreeView (line 586, column 23 - line 589, column 31): " + [ props.checked.constructor.name ]);
    })()) ])([ checkMark ]);
};

// | Set selection handler
var onSelect = function (handler) {
    return function (props) {
        return {
            selectionMode: props.selectionMode,
            checkable: props.checkable,
            draggable: props.draggable,
            searchable: props.searchable,
            searchQuery: props.searchQuery,
            virtualized: props.virtualized,
            className: props.className,
            onCheck: props.onCheck,
            onExpand: props.onExpand,
            onDrop: props.onDrop,
            onSearchChange: props.onSearchChange,
            onLoadChildren: props.onLoadChildren,
            onSelect: new Data_Maybe.Just(handler)
        };
    };
};

// | Set search change handler
var onSearchChange = function (handler) {
    return function (props) {
        return {
            selectionMode: props.selectionMode,
            checkable: props.checkable,
            draggable: props.draggable,
            searchable: props.searchable,
            searchQuery: props.searchQuery,
            virtualized: props.virtualized,
            className: props.className,
            onSelect: props.onSelect,
            onCheck: props.onCheck,
            onExpand: props.onExpand,
            onDrop: props.onDrop,
            onLoadChildren: props.onLoadChildren,
            onSearchChange: new Data_Maybe.Just(handler)
        };
    };
};

// | Set lazy load handler
var onLoadChildren = function (handler) {
    return function (props) {
        return {
            selectionMode: props.selectionMode,
            checkable: props.checkable,
            draggable: props.draggable,
            searchable: props.searchable,
            searchQuery: props.searchQuery,
            virtualized: props.virtualized,
            className: props.className,
            onSelect: props.onSelect,
            onCheck: props.onCheck,
            onExpand: props.onExpand,
            onDrop: props.onDrop,
            onSearchChange: props.onSearchChange,
            onLoadChildren: new Data_Maybe.Just(handler)
        };
    };
};

// | Set expand handler
var onExpand = function (handler) {
    return function (props) {
        return {
            selectionMode: props.selectionMode,
            checkable: props.checkable,
            draggable: props.draggable,
            searchable: props.searchable,
            searchQuery: props.searchQuery,
            virtualized: props.virtualized,
            className: props.className,
            onSelect: props.onSelect,
            onCheck: props.onCheck,
            onDrop: props.onDrop,
            onSearchChange: props.onSearchChange,
            onLoadChildren: props.onLoadChildren,
            onExpand: new Data_Maybe.Just(handler)
        };
    };
};

// | Set drop handler
var onDrop = function (handler) {
    return function (props) {
        return {
            selectionMode: props.selectionMode,
            checkable: props.checkable,
            draggable: props.draggable,
            searchable: props.searchable,
            searchQuery: props.searchQuery,
            virtualized: props.virtualized,
            className: props.className,
            onSelect: props.onSelect,
            onCheck: props.onCheck,
            onExpand: props.onExpand,
            onSearchChange: props.onSearchChange,
            onLoadChildren: props.onLoadChildren,
            onDrop: new Data_Maybe.Just(handler)
        };
    };
};

// | Set check handler
var onCheck = function (handler) {
    return function (props) {
        return {
            selectionMode: props.selectionMode,
            checkable: props.checkable,
            draggable: props.draggable,
            searchable: props.searchable,
            searchQuery: props.searchQuery,
            virtualized: props.virtualized,
            className: props.className,
            onSelect: props.onSelect,
            onExpand: props.onExpand,
            onDrop: props.onDrop,
            onSearchChange: props.onSearchChange,
            onLoadChildren: props.onLoadChildren,
            onCheck: new Data_Maybe.Just(handler)
        };
    };
};

// | Set node ID
var nodeId = function (id) {
    return function (props) {
        return {
            label: props.label,
            icon: props.icon,
            expanded: props.expanded,
            selected: props.selected,
            checked: props.checked,
            indeterminate: props.indeterminate,
            disabled: props.disabled,
            hasChildren: props.hasChildren,
            loading: props.loading,
            className: props.className,
            depth: props.depth,
            nodeId: id
        };
    };
};

// | Add custom class to node
var nodeClassName = function (c) {
    return function (props) {
        return {
            nodeId: props.nodeId,
            label: props.label,
            icon: props.icon,
            expanded: props.expanded,
            selected: props.selected,
            checked: props.checked,
            indeterminate: props.indeterminate,
            disabled: props.disabled,
            hasChildren: props.hasChildren,
            loading: props.loading,
            depth: props.depth,
            className: props.className + (" " + c)
        };
    };
};

// | Set loading state (for lazy loading)
var loading = function (l) {
    return function (props) {
        return {
            nodeId: props.nodeId,
            label: props.label,
            icon: props.icon,
            expanded: props.expanded,
            selected: props.selected,
            checked: props.checked,
            indeterminate: props.indeterminate,
            disabled: props.disabled,
            hasChildren: props.hasChildren,
            className: props.className,
            depth: props.depth,
            loading: l
        };
    };
};

// | Set node label
var label = function (l) {
    return function (props) {
        return {
            nodeId: props.nodeId,
            icon: props.icon,
            expanded: props.expanded,
            selected: props.selected,
            checked: props.checked,
            indeterminate: props.indeterminate,
            disabled: props.disabled,
            hasChildren: props.hasChildren,
            loading: props.loading,
            className: props.className,
            depth: props.depth,
            label: l
        };
    };
};

// | Initialize drag and drop
var initDragDrop = function (el) {
    return function (callbacks) {
        return function (opts) {
            return pure($foreign.unsafeTreeViewElement);
        };
    };
};

// | Set indeterminate state
var indeterminate = function (ind) {
    return function (props) {
        return {
            nodeId: props.nodeId,
            label: props.label,
            icon: props.icon,
            expanded: props.expanded,
            selected: props.selected,
            checked: props.checked,
            disabled: props.disabled,
            hasChildren: props.hasChildren,
            loading: props.loading,
            className: props.className,
            depth: props.depth,
            indeterminate: ind
        };
    };
};

// | Set node icon
var icon = function (i) {
    return function (props) {
        return {
            nodeId: props.nodeId,
            label: props.label,
            expanded: props.expanded,
            selected: props.selected,
            checked: props.checked,
            indeterminate: props.indeterminate,
            disabled: props.disabled,
            hasChildren: props.hasChildren,
            loading: props.loading,
            className: props.className,
            depth: props.depth,
            icon: new Data_Maybe.Just(i)
        };
    };
};

// | Indicate node has children (for lazy loading)
var hasChildren = function (h) {
    return function (props) {
        return {
            nodeId: props.nodeId,
            label: props.label,
            icon: props.icon,
            expanded: props.expanded,
            selected: props.selected,
            checked: props.checked,
            indeterminate: props.indeterminate,
            disabled: props.disabled,
            loading: props.loading,
            className: props.className,
            depth: props.depth,
            hasChildren: h
        };
    };
};

// | Set expanded state
var expanded = function (e) {
    return function (props) {
        return {
            nodeId: props.nodeId,
            label: props.label,
            icon: props.icon,
            selected: props.selected,
            checked: props.checked,
            indeterminate: props.indeterminate,
            disabled: props.disabled,
            hasChildren: props.hasChildren,
            loading: props.loading,
            className: props.className,
            depth: props.depth,
            expanded: e
        };
    };
};
var eqSelectionMode = {
    eq: function (x) {
        return function (y) {
            if (x instanceof SingleSelect && y instanceof SingleSelect) {
                return true;
            };
            if (x instanceof MultiSelect && y instanceof MultiSelect) {
                return true;
            };
            if (x instanceof NoSelect && y instanceof NoSelect) {
                return true;
            };
            return false;
        };
    }
};
var eqNodeIcon = {
    eq: function (x) {
        return function (y) {
            if (x instanceof FolderIcon && y instanceof FolderIcon) {
                return true;
            };
            if (x instanceof FolderOpenIcon && y instanceof FolderOpenIcon) {
                return true;
            };
            if (x instanceof FileIcon && y instanceof FileIcon) {
                return true;
            };
            if (x instanceof FileTextIcon && y instanceof FileTextIcon) {
                return true;
            };
            if (x instanceof FileCodeIcon && y instanceof FileCodeIcon) {
                return true;
            };
            if (x instanceof CustomIcon && y instanceof CustomIcon) {
                return x.value0 === y.value0;
            };
            return false;
        };
    }
};
var eqDropPosition = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Before && y instanceof Before) {
                return true;
            };
            if (x instanceof After && y instanceof After) {
                return true;
            };
            if (x instanceof Inside && y instanceof Inside) {
                return true;
            };
            return false;
        };
    }
};
var eqCheckState = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Unchecked && y instanceof Unchecked) {
                return true;
            };
            if (x instanceof Checked && y instanceof Checked) {
                return true;
            };
            if (x instanceof Indeterminate && y instanceof Indeterminate) {
                return true;
            };
            return false;
        };
    }
};

// | Enable drag and drop
var draggable = function (d) {
    return function (props) {
        return {
            selectionMode: props.selectionMode,
            checkable: props.checkable,
            searchable: props.searchable,
            searchQuery: props.searchQuery,
            virtualized: props.virtualized,
            className: props.className,
            onSelect: props.onSelect,
            onCheck: props.onCheck,
            onExpand: props.onExpand,
            onDrop: props.onDrop,
            onSearchChange: props.onSearchChange,
            onLoadChildren: props.onLoadChildren,
            draggable: d
        };
    };
};

// | Set disabled state
var disabled = function (d) {
    return function (props) {
        return {
            nodeId: props.nodeId,
            label: props.label,
            icon: props.icon,
            expanded: props.expanded,
            selected: props.selected,
            checked: props.checked,
            indeterminate: props.indeterminate,
            hasChildren: props.hasChildren,
            loading: props.loading,
            className: props.className,
            depth: props.depth,
            disabled: d
        };
    };
};

// | Cleanup tree view
var destroyTreeView = function (v) {
    return pure(Data_Unit.unit);
};

// | Default tree view properties
var defaultProps = /* #__PURE__ */ (function () {
    return {
        selectionMode: SingleSelect.value,
        checkable: false,
        draggable: false,
        searchable: false,
        searchQuery: "",
        virtualized: false,
        className: "",
        onSelect: Data_Maybe.Nothing.value,
        onCheck: Data_Maybe.Nothing.value,
        onExpand: Data_Maybe.Nothing.value,
        onDrop: Data_Maybe.Nothing.value,
        onSearchChange: Data_Maybe.Nothing.value,
        onLoadChildren: Data_Maybe.Nothing.value
    };
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // components
// ═══════════════════════════════════════════════════════════════════════════════
// | TreeView container
// |
// | Root container for tree nodes with search and accessibility
var treeView = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        var searchInput = (function () {
            if (props.searchable) {
                return [ Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "relative mb-2" ]) ])([ Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "absolute left-3 top-1/2 -translate-y-1/2 text-muted-foreground" ]) ])([ Halogen_HTML_Core.text("\ud83d\udd0d") ]), Halogen_HTML_Elements.input([ Hydrogen_UI_Core.cls([ "w-full h-9 pl-9 pr-3 rounded-md border border-input bg-background text-sm placeholder:text-muted-foreground focus:outline-none focus:ring-2 focus:ring-ring" ]), type_1(DOM_HTML_Indexed_InputType.InputText.value), Halogen_HTML_Properties.placeholder("Search..."), value(props.searchQuery) ]) ]) ];
            };
            return [  ];
        })();
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "tree-view", props.className ]) ])(append1(searchInput)([ Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "tree-view-content" ]), Halogen_HTML_Properties_ARIA.role("tree") ])(children) ]));
    };
};

// | Default node properties
var defaultNodeProps = /* #__PURE__ */ (function () {
    return {
        nodeId: "",
        label: "",
        icon: Data_Maybe.Nothing.value,
        expanded: false,
        selected: false,
        checked: Unchecked.value,
        indeterminate: false,
        disabled: false,
        hasChildren: false,
        loading: false,
        className: "",
        depth: 0
    };
})();

// | Tree node
// |
// | Individual tree node with expand/collapse functionality
var treeNode = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultNodeProps)(propMods);
        var nodeIcon = (function () {
            if (props.icon instanceof Data_Maybe.Just && props.icon.value0 instanceof FolderIcon) {
                return Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "text-yellow-500" ]) ])([ Halogen_HTML_Core.text("\ud83d\udcc1") ]);
            };
            if (props.icon instanceof Data_Maybe.Just && props.icon.value0 instanceof FolderOpenIcon) {
                return Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "text-yellow-500" ]) ])([ Halogen_HTML_Core.text("\ud83d\udcc2") ]);
            };
            if (props.icon instanceof Data_Maybe.Just && props.icon.value0 instanceof FileIcon) {
                return Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "text-muted-foreground" ]) ])([ Halogen_HTML_Core.text("\ud83d\udcc4") ]);
            };
            if (props.icon instanceof Data_Maybe.Just && props.icon.value0 instanceof FileTextIcon) {
                return Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "text-blue-500" ]) ])([ Halogen_HTML_Core.text("\ud83d\udcdd") ]);
            };
            if (props.icon instanceof Data_Maybe.Just && props.icon.value0 instanceof FileCodeIcon) {
                return Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "text-green-500" ]) ])([ Halogen_HTML_Core.text("\ud83d\udcdc") ]);
            };
            if (props.icon instanceof Data_Maybe.Just && props.icon.value0 instanceof CustomIcon) {
                return Halogen_HTML_Elements.span_([ Halogen_HTML_Core.text(props.icon.value0.value0) ]);
            };
            if (props.icon instanceof Data_Maybe.Nothing) {
                return Halogen_HTML_Core.text("");
            };
            throw new Error("Failed pattern match at Hydrogen.Component.TreeView (line 496, column 16 - line 510, column 19): " + [ props.icon.constructor.name ]);
        })();
        var loadingSpinner = (function () {
            if (props.loading) {
                return Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "animate-spin text-muted-foreground" ]) ])([ Halogen_HTML_Core.text("\u27f3") ]);
            };
            return Halogen_HTML_Core.text("");
        })();
        var itemClasses = "flex items-center gap-1.5 py-1 px-2 rounded-md cursor-pointer transition-colors hover:bg-muted/50" + ((function () {
            if (props.selected) {
                return " bg-accent text-accent-foreground";
            };
            return "";
        })() + (function () {
            if (props.disabled) {
                return " opacity-50 pointer-events-none";
            };
            return "";
        })());
        var indentPx = props.depth * 20 | 0;
        var indentStyle = "padding-left: " + (show(indentPx) + "px");
        var hasKids = !Data_Array["null"](children) || props.hasChildren;
        var expandIcon = (function () {
            if (hasKids) {
                return Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "w-4 h-4 flex items-center justify-center text-muted-foreground transition-transform", (function () {
                    if (props.expanded) {
                        return "rotate-90";
                    };
                    return "";
                })() ]) ])([ Halogen_HTML_Core.text("\u25b6") ]);
            };
            return Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "w-4 h-4" ]) ])([  ]);
        })();
        var childrenContent = (function () {
            var $76 = props.expanded && !Data_Array["null"](children);
            if ($76) {
                return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "tree-node-children" ]), Halogen_HTML_Properties_ARIA.role("group") ])(children);
            };
            return Halogen_HTML_Core.text("");
        })();
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "tree-node group", props.className ]), Halogen_HTML_Properties.attr("data-node-id")(props.nodeId) ])([ Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ itemClasses ]), Halogen_HTML_Properties.attr("style")(indentStyle), Halogen_HTML_Properties.tabIndex(0), Halogen_HTML_Properties_ARIA.role("treeitem"), Halogen_HTML_Properties_ARIA.expanded((function () {
            if (hasKids) {
                return show1(props.expanded);
            };
            return "";
        })()), Halogen_HTML_Properties_ARIA.selected(show1(props.selected)) ])([ expandIcon, nodeIcon, loadingSpinner, Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "flex-1 truncate text-sm" ]) ])([ Halogen_HTML_Core.text(props.label) ]) ]), childrenContent ]);
    };
};

// | Add custom class
var className = function (c) {
    return function (props) {
        return {
            selectionMode: props.selectionMode,
            checkable: props.checkable,
            draggable: props.draggable,
            searchable: props.searchable,
            searchQuery: props.searchQuery,
            virtualized: props.virtualized,
            onSelect: props.onSelect,
            onCheck: props.onCheck,
            onExpand: props.onExpand,
            onDrop: props.onDrop,
            onSearchChange: props.onSearchChange,
            onLoadChildren: props.onLoadChildren,
            className: props.className + (" " + c)
        };
    };
};

// | Set checked state
var checked = function (c) {
    return function (props) {
        return {
            nodeId: props.nodeId,
            label: props.label,
            icon: props.icon,
            expanded: props.expanded,
            selected: props.selected,
            indeterminate: props.indeterminate,
            disabled: props.disabled,
            hasChildren: props.hasChildren,
            loading: props.loading,
            className: props.className,
            depth: props.depth,
            checked: c
        };
    };
};

// | Enable checkbox selection
var checkable = function (c) {
    return function (props) {
        return {
            selectionMode: props.selectionMode,
            draggable: props.draggable,
            searchable: props.searchable,
            searchQuery: props.searchQuery,
            virtualized: props.virtualized,
            className: props.className,
            onSelect: props.onSelect,
            onCheck: props.onCheck,
            onExpand: props.onExpand,
            onDrop: props.onDrop,
            onSearchChange: props.onSearchChange,
            onLoadChildren: props.onLoadChildren,
            checkable: c
        };
    };
};
export {
    treeView,
    treeNode,
    treeNodeContent,
    defaultProps,
    defaultNodeProps,
    selectionMode,
    checkable,
    draggable,
    searchable,
    searchQuery,
    virtualized,
    className,
    onSelect,
    onCheck,
    onExpand,
    onDrop,
    onSearchChange,
    onLoadChildren,
    nodeId,
    label,
    icon,
    expanded,
    selected,
    checked,
    indeterminate,
    disabled,
    hasChildren,
    loading,
    nodeClassName,
    SingleSelect,
    MultiSelect,
    NoSelect,
    FolderIcon,
    FolderOpenIcon,
    FileIcon,
    FileTextIcon,
    FileCodeIcon,
    CustomIcon,
    Unchecked,
    Checked,
    Indeterminate,
    Before,
    After,
    Inside,
    initDragDrop,
    destroyTreeView,
    eqSelectionMode,
    eqNodeIcon,
    eqCheckState,
    eqDropPosition
};
