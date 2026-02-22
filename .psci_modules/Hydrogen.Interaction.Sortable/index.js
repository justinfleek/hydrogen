// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                       // hydrogen // sortable
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Sortable lists
// |
// | Sortable list components with drag-and-drop reordering, keyboard
// | accessibility, and smooth animations. Supports both vertical and
// | horizontal layouts, and dragging between multiple lists.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Interaction.Sortable as Sortable
// |
// | -- Basic sortable list
// | Sortable.sortableList
// |   [ Sortable.onReorder \e -> HandleReorder e.oldIndex e.newIndex
// |   , Sortable.animate true
// |   ]
// |   [ Sortable.sortableItem [ Sortable.itemId "1" ] [ HH.text "Item 1" ]
// |   , Sortable.sortableItem [ Sortable.itemId "2" ] [ HH.text "Item 2" ]
// |   , Sortable.sortableItem [ Sortable.itemId "3" ] [ HH.text "Item 3" ]
// |   ]
// |
// | -- Horizontal sortable
// | Sortable.sortableList
// |   [ Sortable.direction Sortable.Horizontal
// |   , Sortable.onReorder handleReorder
// |   ]
// |   items
// |
// | -- With drag handles
// | Sortable.sortableItem [ Sortable.itemId "1" ]
// |   [ Sortable.sortableHandle [] [ Icon.gripVertical ]
// |   , HH.span_ [ HH.text "Item 1" ]
// |   ]
// |
// | -- Disabled items
// | Sortable.sortableItem 
// |   [ Sortable.itemId "locked"
// |   , Sortable.itemDisabled true
// |   ]
// |   [ HH.text "Cannot be moved" ]
// |
// | -- Keyboard reordering
// | -- Press Space/Enter to grab, arrow keys to move, Space/Enter to drop
// | ```
import * as $foreign from "./foreign.js";
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Properties from "../Halogen.HTML.Properties/index.js";
import * as Halogen_HTML_Properties_ARIA from "../Halogen.HTML.Properties.ARIA/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                      // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Sort direction
var Vertical = /* #__PURE__ */ (function () {
    function Vertical() {

    };
    Vertical.value = new Vertical();
    return Vertical;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                      // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Sort direction
var Horizontal = /* #__PURE__ */ (function () {
    function Horizontal() {

    };
    Horizontal.value = new Horizontal();
    return Horizontal;
})();

// | Show placeholder in list while dragging
var showPlaceholder = function (show) {
    return function (props) {
        return {
            listId: props.listId,
            direction: props.direction,
            onReorder: props.onReorder,
            onSortStart: props.onSortStart,
            onSortMove: props.onSortMove,
            onSortEnd: props.onSortEnd,
            animate: props.animate,
            showGhost: props.showGhost,
            placeholderClass: props.placeholderClass,
            handleSelector: props.handleSelector,
            className: props.className,
            showPlaceholder: show
        };
    };
};

// | Show ghost element while dragging
var showGhost = function (show) {
    return function (props) {
        return {
            listId: props.listId,
            direction: props.direction,
            onReorder: props.onReorder,
            onSortStart: props.onSortStart,
            onSortMove: props.onSortMove,
            onSortEnd: props.onSortEnd,
            animate: props.animate,
            showPlaceholder: props.showPlaceholder,
            placeholderClass: props.placeholderClass,
            handleSelector: props.handleSelector,
            className: props.className,
            showGhost: show
        };
    };
};
var setItemDisabled = $foreign.setItemDisabledImpl;
var reorderArray = $foreign.reorderArrayImpl;
var removePlaceholder = $foreign.removePlaceholderImpl;

// | CSS classes for placeholder element
var placeholderClass = function (c) {
    return function (props) {
        return {
            listId: props.listId,
            direction: props.direction,
            onReorder: props.onReorder,
            onSortStart: props.onSortStart,
            onSortMove: props.onSortMove,
            onSortEnd: props.onSortEnd,
            animate: props.animate,
            showGhost: props.showGhost,
            showPlaceholder: props.showPlaceholder,
            handleSelector: props.handleSelector,
            className: props.className,
            placeholderClass: c
        };
    };
};

// | Handler for sort start event
var onSortStart = function (handler) {
    return function (props) {
        return {
            listId: props.listId,
            direction: props.direction,
            onReorder: props.onReorder,
            onSortMove: props.onSortMove,
            onSortEnd: props.onSortEnd,
            animate: props.animate,
            showGhost: props.showGhost,
            showPlaceholder: props.showPlaceholder,
            placeholderClass: props.placeholderClass,
            handleSelector: props.handleSelector,
            className: props.className,
            onSortStart: new Data_Maybe.Just(handler)
        };
    };
};

// | Handler for sort move event
var onSortMove = function (handler) {
    return function (props) {
        return {
            listId: props.listId,
            direction: props.direction,
            onReorder: props.onReorder,
            onSortStart: props.onSortStart,
            onSortEnd: props.onSortEnd,
            animate: props.animate,
            showGhost: props.showGhost,
            showPlaceholder: props.showPlaceholder,
            placeholderClass: props.placeholderClass,
            handleSelector: props.handleSelector,
            className: props.className,
            onSortMove: new Data_Maybe.Just(handler)
        };
    };
};

// | Handler for sort end event
var onSortEnd = function (handler) {
    return function (props) {
        return {
            listId: props.listId,
            direction: props.direction,
            onReorder: props.onReorder,
            onSortStart: props.onSortStart,
            onSortMove: props.onSortMove,
            animate: props.animate,
            showGhost: props.showGhost,
            showPlaceholder: props.showPlaceholder,
            placeholderClass: props.placeholderClass,
            handleSelector: props.handleSelector,
            className: props.className,
            onSortEnd: new Data_Maybe.Just(handler)
        };
    };
};

// | Handler for reorder event
var onReorder = function (handler) {
    return function (props) {
        return {
            listId: props.listId,
            direction: props.direction,
            onSortStart: props.onSortStart,
            onSortMove: props.onSortMove,
            onSortEnd: props.onSortEnd,
            animate: props.animate,
            showGhost: props.showGhost,
            showPlaceholder: props.showPlaceholder,
            placeholderClass: props.placeholderClass,
            handleSelector: props.handleSelector,
            className: props.className,
            onReorder: new Data_Maybe.Just(handler)
        };
    };
};

// | Set list identifier (for multi-list support)
var listId = function (id) {
    return function (props) {
        return {
            direction: props.direction,
            onReorder: props.onReorder,
            onSortStart: props.onSortStart,
            onSortMove: props.onSortMove,
            onSortEnd: props.onSortEnd,
            animate: props.animate,
            showGhost: props.showGhost,
            showPlaceholder: props.showPlaceholder,
            placeholderClass: props.placeholderClass,
            handleSelector: props.handleSelector,
            className: props.className,
            listId: id
        };
    };
};

// | Add custom class to list
var listClassName = function (c) {
    return function (props) {
        return {
            listId: props.listId,
            direction: props.direction,
            onReorder: props.onReorder,
            onSortStart: props.onSortStart,
            onSortMove: props.onSortMove,
            onSortEnd: props.onSortEnd,
            animate: props.animate,
            showGhost: props.showGhost,
            showPlaceholder: props.showPlaceholder,
            placeholderClass: props.placeholderClass,
            handleSelector: props.handleSelector,
            className: props.className + (" " + c)
        };
    };
};

// | Set item identifier
var itemId = function (id) {
    return function (props) {
        return {
            disabled: props.disabled,
            className: props.className,
            id: id
        };
    };
};

// | Disable item (cannot be dragged)
var itemDisabled = function (disabled) {
    return function (props) {
        return {
            id: props.id,
            className: props.className,
            disabled: disabled
        };
    };
};

// | Add custom class to item
var itemClassName = function (c) {
    return function (props) {
        return {
            id: props.id,
            disabled: props.disabled,
            className: props.className + (" " + c)
        };
    };
};
var insertPlaceholder = $foreign.insertPlaceholderImpl;

// | CSS selector for drag handles
var handleSelector = function (selector) {
    return function (props) {
        return {
            listId: props.listId,
            direction: props.direction,
            onReorder: props.onReorder,
            onSortStart: props.onSortStart,
            onSortMove: props.onSortMove,
            onSortEnd: props.onSortEnd,
            animate: props.animate,
            showGhost: props.showGhost,
            showPlaceholder: props.showPlaceholder,
            placeholderClass: props.placeholderClass,
            className: props.className,
            handleSelector: new Data_Maybe.Just(selector)
        };
    };
};
var getSortState = $foreign.getSortStateImpl;
var getItems = $foreign.getItemsImpl;
var getItemIndex = $foreign.getItemIndexImpl;
var eqDirection = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Vertical && y instanceof Vertical) {
                return true;
            };
            if (x instanceof Horizontal && y instanceof Horizontal) {
                return true;
            };
            return false;
        };
    }
};
var eq = /* #__PURE__ */ Data_Eq.eq(eqDirection);

// | Set sort direction
var direction = function (dir) {
    return function (props) {
        return {
            listId: props.listId,
            onReorder: props.onReorder,
            onSortStart: props.onSortStart,
            onSortMove: props.onSortMove,
            onSortEnd: props.onSortEnd,
            animate: props.animate,
            showGhost: props.showGhost,
            showPlaceholder: props.showPlaceholder,
            placeholderClass: props.placeholderClass,
            handleSelector: props.handleSelector,
            className: props.className,
            direction: dir
        };
    };
};
var defaultSortableListProps = /* #__PURE__ */ (function () {
    return {
        listId: "sortable-list",
        direction: Vertical.value,
        onReorder: Data_Maybe.Nothing.value,
        onSortStart: Data_Maybe.Nothing.value,
        onSortMove: Data_Maybe.Nothing.value,
        onSortEnd: Data_Maybe.Nothing.value,
        animate: true,
        showGhost: true,
        showPlaceholder: true,
        placeholderClass: "bg-muted/50 border-2 border-dashed border-muted-foreground/30 rounded-md",
        handleSelector: Data_Maybe.Nothing.value,
        className: ""
    };
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // components
// ═══════════════════════════════════════════════════════════════════════════════
// | Sortable list container
// |
// | Contains sortable items that can be reordered via drag and drop
// | or keyboard navigation.
var sortableList = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultSortableListProps)(propMods);
        var dirClass = (function () {
            if (props.direction instanceof Vertical) {
                return "flex flex-col";
            };
            if (props.direction instanceof Horizontal) {
                return "flex flex-row";
            };
            throw new Error("Failed pattern match at Hydrogen.Interaction.Sortable (line 318, column 18 - line 320, column 38): " + [ props.direction.constructor.name ]);
        })();
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ dirClass, "gap-2", props.className ]), Halogen_HTML_Properties.attr("data-sortable-list")(props.listId), Halogen_HTML_Properties.attr("data-direction")((function () {
            var $23 = eq(props.direction)(Horizontal.value);
            if ($23) {
                return "horizontal";
            };
            return "vertical";
        })()), Halogen_HTML_Properties_ARIA.role("listbox"), Halogen_HTML_Properties_ARIA.label("Sortable list. Use arrow keys to reorder items.") ])(children);
    };
};
var defaultSortableItemProps = {
    id: "",
    disabled: false,
    className: ""
};

// | Sortable item wrapper
// |
// | Wrap content in this component to make it sortable within a sortableList.
var sortableItem = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultSortableItemProps)(propMods);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "relative select-none", (function () {
            if (props.disabled) {
                return "opacity-50 cursor-not-allowed";
            };
            return "cursor-grab active:cursor-grabbing";
        })(), "focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2", "[&[data-sorting=true]]:opacity-50", "[&[data-keyboard-sorting=true]]:ring-2 [&[data-keyboard-sorting=true]]:ring-primary", "transition-transform duration-200", props.className ]), Halogen_HTML_Properties.attr("data-sortable-item")(props.id), (function () {
            if (props.disabled) {
                return Halogen_HTML_Properties.attr("data-sortable-disabled")("true");
            };
            return Halogen_HTML_Properties.attr("data-sortable-disabled")("false");
        })(), Halogen_HTML_Properties.tabIndex((function () {
            if (props.disabled) {
                return -1 | 0;
            };
            return 0;
        })()), Halogen_HTML_Properties_ARIA.role("option"), Halogen_HTML_Properties_ARIA.label("Sortable item. Press Space or Enter to grab, arrow keys to reorder, Space or Enter to drop, Escape to cancel.") ])(children);
    };
};
var defaultSortableHandleProps = {
    className: ""
};

// | Sortable handle component
// |
// | When placed inside a sortable item, only this element will initiate dragging.
var sortableHandle = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultSortableHandleProps)(propMods);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "cursor-grab active:cursor-grabbing touch-none", "flex items-center justify-center", "text-muted-foreground hover:text-foreground", "transition-colors", props.className ]), Halogen_HTML_Properties.attr("data-sortable-handle")("true"), Halogen_HTML_Properties_ARIA.role("button"), Halogen_HTML_Properties_ARIA.label("Drag handle") ])(children);
    };
};
var createPlaceholder = $foreign.createPlaceholderImpl;
var clearSortState = $foreign.clearSortStateImpl;

// | Enable/disable animations
var animate = function (enabled) {
    return function (props) {
        return {
            listId: props.listId,
            direction: props.direction,
            onReorder: props.onReorder,
            onSortStart: props.onSortStart,
            onSortMove: props.onSortMove,
            onSortEnd: props.onSortEnd,
            showGhost: props.showGhost,
            showPlaceholder: props.showPlaceholder,
            placeholderClass: props.placeholderClass,
            handleSelector: props.handleSelector,
            className: props.className,
            animate: enabled
        };
    };
};
export {
    sortableList,
    sortableItem,
    sortableHandle,
    listId,
    direction,
    Vertical,
    Horizontal,
    onReorder,
    onSortStart,
    onSortMove,
    onSortEnd,
    animate,
    showGhost,
    showPlaceholder,
    placeholderClass,
    handleSelector,
    listClassName,
    itemId,
    itemDisabled,
    itemClassName,
    reorderArray,
    getItems,
    getItemIndex,
    setItemDisabled,
    getSortState,
    clearSortState,
    createPlaceholder,
    insertPlaceholder,
    removePlaceholder,
    eqDirection
};
