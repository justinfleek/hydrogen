// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                       // hydrogen // dragdrop
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Drag and Drop system
// |
// | A comprehensive drag and drop system with touch support, keyboard
// | accessibility, axis constraints, and customizable visual feedback.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Interaction.DragDrop as DragDrop
// |
// | -- Draggable element
// | DragDrop.draggable
// |   [ DragDrop.dragData { id: "item-1", type: "card" }
// |   , DragDrop.onDragStart \_ -> HandleDragStart
// |   , DragDrop.onDragEnd \_ -> HandleDragEnd
// |   , DragDrop.showGhost true
// |   ]
// |   [ HH.text "Drag me!" ]
// |
// | -- Drop zone
// | DragDrop.droppable
// |   [ DragDrop.onDrop \info -> HandleDrop info.data
// |   , DragDrop.dropHighlight "bg-blue-100 border-blue-500"
// |   ]
// |   [ HH.text "Drop here" ]
// |
// | -- Constrained dragging
// | DragDrop.draggable
// |   [ DragDrop.axis DragDrop.AxisX  -- Horizontal only
// |   , DragDrop.bounds { left: 0, top: 0, right: 500, bottom: 300 }
// |   ]
// |   [ content ]
// |
// | -- Keyboard accessible dragging
// | DragDrop.draggable
// |   [ DragDrop.keyboardDrag true  -- Space to grab, arrows to move
// |   , DragDrop.keyboardStep 10
// |   ]
// |   [ content ]
// | ```
import * as $foreign from "./foreign.js";
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Properties from "../Halogen.HTML.Properties/index.js";
import * as Halogen_HTML_Properties_ARIA from "../Halogen.HTML.Properties.ARIA/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                      // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Axis constraint for dragging
var AxisNone = /* #__PURE__ */ (function () {
    function AxisNone() {

    };
    AxisNone.value = new AxisNone();
    return AxisNone;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                      // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Axis constraint for dragging
var AxisX = /* #__PURE__ */ (function () {
    function AxisX() {

    };
    AxisX.value = new AxisX();
    return AxisX;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                      // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Axis constraint for dragging
var AxisY = /* #__PURE__ */ (function () {
    function AxisY() {

    };
    AxisY.value = new AxisY();
    return AxisY;
})();
var updateGhostPosition = $foreign.updateGhostPositionImpl;
var updateDropIndicator = $foreign.updateDropIndicatorImpl;

// | Show ghost element while dragging
var showGhost = function (show) {
    return function (props) {
        return {
            data: props.data,
            onDragStart: props.onDragStart,
            onDrag: props.onDrag,
            onDragEnd: props.onDragEnd,
            ghostOpacity: props.ghostOpacity,
            axis: props.axis,
            bounds: props.bounds,
            handleSelector: props.handleSelector,
            keyboardDrag: props.keyboardDrag,
            keyboardStep: props.keyboardStep,
            disabled: props.disabled,
            className: props.className,
            showGhost: show
        };
    };
};
var showDropIndicator = $foreign.showDropIndicatorImpl;
var setDragState = $foreign.setDragStateImpl;
var setDragData = $foreign.setDragDataImpl;
var removeGhost = $foreign.removeGhostImpl;
var removeDropIndicator = $foreign.removeDropIndicatorImpl;

// | Handler for drop event
var onDrop = function (handler) {
    return function (props) {
        return {
            onDragOver: props.onDragOver,
            onDragLeave: props.onDragLeave,
            accepts: props.accepts,
            dropHighlight: props.dropHighlight,
            className: props.className,
            onDrop: new Data_Maybe.Just(handler)
        };
    };
};

// | Handler for drag start
var onDragStart = function (handler) {
    return function (props) {
        return {
            data: props.data,
            onDrag: props.onDrag,
            onDragEnd: props.onDragEnd,
            showGhost: props.showGhost,
            ghostOpacity: props.ghostOpacity,
            axis: props.axis,
            bounds: props.bounds,
            handleSelector: props.handleSelector,
            keyboardDrag: props.keyboardDrag,
            keyboardStep: props.keyboardStep,
            disabled: props.disabled,
            className: props.className,
            onDragStart: new Data_Maybe.Just(handler)
        };
    };
};

// | Handler for drag over event
var onDragOver = function (handler) {
    return function (props) {
        return {
            onDrop: props.onDrop,
            onDragLeave: props.onDragLeave,
            accepts: props.accepts,
            dropHighlight: props.dropHighlight,
            className: props.className,
            onDragOver: new Data_Maybe.Just(handler)
        };
    };
};

// | Handler for drag leave event
var onDragLeave = function (handler) {
    return function (props) {
        return {
            onDrop: props.onDrop,
            onDragOver: props.onDragOver,
            accepts: props.accepts,
            dropHighlight: props.dropHighlight,
            className: props.className,
            onDragLeave: new Data_Maybe.Just(handler)
        };
    };
};

// | Handler for drag end
var onDragEnd = function (handler) {
    return function (props) {
        return {
            data: props.data,
            onDragStart: props.onDragStart,
            onDrag: props.onDrag,
            showGhost: props.showGhost,
            ghostOpacity: props.ghostOpacity,
            axis: props.axis,
            bounds: props.bounds,
            handleSelector: props.handleSelector,
            keyboardDrag: props.keyboardDrag,
            keyboardStep: props.keyboardStep,
            disabled: props.disabled,
            className: props.className,
            onDragEnd: new Data_Maybe.Just(handler)
        };
    };
};

// | Handler for drag movement
var onDrag = function (handler) {
    return function (props) {
        return {
            data: props.data,
            onDragStart: props.onDragStart,
            onDragEnd: props.onDragEnd,
            showGhost: props.showGhost,
            ghostOpacity: props.ghostOpacity,
            axis: props.axis,
            bounds: props.bounds,
            handleSelector: props.handleSelector,
            keyboardDrag: props.keyboardDrag,
            keyboardStep: props.keyboardStep,
            disabled: props.disabled,
            className: props.className,
            onDrag: new Data_Maybe.Just(handler)
        };
    };
};

// | Keyboard movement step in pixels
var keyboardStep = function (step) {
    return function (props) {
        return {
            data: props.data,
            onDragStart: props.onDragStart,
            onDrag: props.onDrag,
            onDragEnd: props.onDragEnd,
            showGhost: props.showGhost,
            ghostOpacity: props.ghostOpacity,
            axis: props.axis,
            bounds: props.bounds,
            handleSelector: props.handleSelector,
            keyboardDrag: props.keyboardDrag,
            disabled: props.disabled,
            className: props.className,
            keyboardStep: step
        };
    };
};

// | Enable keyboard dragging
var keyboardDrag = function (enabled) {
    return function (props) {
        return {
            data: props.data,
            onDragStart: props.onDragStart,
            onDrag: props.onDrag,
            onDragEnd: props.onDragEnd,
            showGhost: props.showGhost,
            ghostOpacity: props.ghostOpacity,
            axis: props.axis,
            bounds: props.bounds,
            handleSelector: props.handleSelector,
            keyboardStep: props.keyboardStep,
            disabled: props.disabled,
            className: props.className,
            keyboardDrag: enabled
        };
    };
};

// | CSS selector for drag handle (only this element triggers drag)
var handleSelector = function (selector) {
    return function (props) {
        return {
            data: props.data,
            onDragStart: props.onDragStart,
            onDrag: props.onDrag,
            onDragEnd: props.onDragEnd,
            showGhost: props.showGhost,
            ghostOpacity: props.ghostOpacity,
            axis: props.axis,
            bounds: props.bounds,
            keyboardDrag: props.keyboardDrag,
            keyboardStep: props.keyboardStep,
            disabled: props.disabled,
            className: props.className,
            handleSelector: new Data_Maybe.Just(selector)
        };
    };
};

// | Ghost element opacity (0.0 to 1.0)
var ghostOpacity = function (opacity) {
    return function (props) {
        return {
            data: props.data,
            onDragStart: props.onDragStart,
            onDrag: props.onDrag,
            onDragEnd: props.onDragEnd,
            showGhost: props.showGhost,
            axis: props.axis,
            bounds: props.bounds,
            handleSelector: props.handleSelector,
            keyboardDrag: props.keyboardDrag,
            keyboardStep: props.keyboardStep,
            disabled: props.disabled,
            className: props.className,
            ghostOpacity: opacity
        };
    };
};
var getElementAtPoint = $foreign.getElementAtPointImpl;
var getDragState = $foreign.getDragStateImpl;
var getDragData = $foreign.getDragDataImpl;
var getBoundingRect = $foreign.getBoundingRectImpl;
var eqAxis = {
    eq: function (x) {
        return function (y) {
            if (x instanceof AxisNone && y instanceof AxisNone) {
                return true;
            };
            if (x instanceof AxisX && y instanceof AxisX) {
                return true;
            };
            if (x instanceof AxisY && y instanceof AxisY) {
                return true;
            };
            return false;
        };
    }
};

// | CSS classes for highlight when dragging over
var dropHighlight = function (highlight) {
    return function (props) {
        return {
            onDrop: props.onDrop,
            onDragOver: props.onDragOver,
            onDragLeave: props.onDragLeave,
            accepts: props.accepts,
            className: props.className,
            dropHighlight: highlight
        };
    };
};

// | Add custom class (reusing name for droppable)
var dropClassName = function (c) {
    return function (props) {
        return {
            onDrop: props.onDrop,
            onDragOver: props.onDragOver,
            onDragLeave: props.onDragLeave,
            accepts: props.accepts,
            dropHighlight: props.dropHighlight,
            className: props.className + (" " + c)
        };
    };
};

// | Set drag data (any serializable value)
var dragData = function (d) {
    return function (props) {
        return {
            onDragStart: props.onDragStart,
            onDrag: props.onDrag,
            onDragEnd: props.onDragEnd,
            showGhost: props.showGhost,
            ghostOpacity: props.ghostOpacity,
            axis: props.axis,
            bounds: props.bounds,
            handleSelector: props.handleSelector,
            keyboardDrag: props.keyboardDrag,
            keyboardStep: props.keyboardStep,
            disabled: props.disabled,
            className: props.className,
            data: $foreign.unsafeToForeign(d)
        };
    };
};

// | Disable dragging
var disabled = function (d) {
    return function (props) {
        return {
            data: props.data,
            onDragStart: props.onDragStart,
            onDrag: props.onDrag,
            onDragEnd: props.onDragEnd,
            showGhost: props.showGhost,
            ghostOpacity: props.ghostOpacity,
            axis: props.axis,
            bounds: props.bounds,
            handleSelector: props.handleSelector,
            keyboardDrag: props.keyboardDrag,
            keyboardStep: props.keyboardStep,
            className: props.className,
            disabled: d
        };
    };
};
var defaultDroppableProps = /* #__PURE__ */ (function () {
    return {
        onDrop: Data_Maybe.Nothing.value,
        onDragOver: Data_Maybe.Nothing.value,
        onDragLeave: Data_Maybe.Nothing.value,
        accepts: Data_Maybe.Nothing.value,
        dropHighlight: "ring-2 ring-primary ring-offset-2 bg-primary/10",
        className: ""
    };
})();

// | Droppable zone component
// |
// | Creates a drop target that can receive dragged items.
var droppable = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultDroppableProps)(propMods);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "transition-all duration-150", "[&[data-drag-over=true]]:" + props.dropHighlight, props.className ]), Halogen_HTML_Properties.attr("data-droppable")("true"), Halogen_HTML_Properties_ARIA.role("region"), Halogen_HTML_Properties_ARIA.label("Drop zone") ])(children);
    };
};
var defaultDraggableProps = /* #__PURE__ */ (function () {
    return {
        data: $foreign.unsafeToForeign({}),
        onDragStart: Data_Maybe.Nothing.value,
        onDrag: Data_Maybe.Nothing.value,
        onDragEnd: Data_Maybe.Nothing.value,
        showGhost: true,
        ghostOpacity: 0.7,
        axis: AxisNone.value,
        bounds: Data_Maybe.Nothing.value,
        handleSelector: Data_Maybe.Nothing.value,
        keyboardDrag: true,
        keyboardStep: 10,
        disabled: false,
        className: ""
    };
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // components
// ═══════════════════════════════════════════════════════════════════════════════
// | Draggable wrapper component
// |
// | Makes its children draggable with support for ghost elements,
// | axis constraints, keyboard navigation, and touch devices.
var draggable = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultDraggableProps)(propMods);
        var axisStr = (function () {
            if (props.axis instanceof AxisNone) {
                return "none";
            };
            if (props.axis instanceof AxisX) {
                return "x";
            };
            if (props.axis instanceof AxisY) {
                return "y";
            };
            throw new Error("Failed pattern match at Hydrogen.Interaction.DragDrop (line 384, column 17 - line 387, column 21): " + [ props.axis.constructor.name ]);
        })();
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "select-none", (function () {
            if (props.disabled) {
                return "opacity-50 cursor-not-allowed";
            };
            return "cursor-grab active:cursor-grabbing";
        })(), "focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2", "[&[data-dragging=true]]:cursor-grabbing [&[data-dragging=true]]:opacity-50", props.className ]), Halogen_HTML_Properties.attr("data-draggable")("true"), Halogen_HTML_Properties.attr("data-drag-axis")(axisStr), Halogen_HTML_Properties.attr("data-drag-disabled")((function () {
            if (props.disabled) {
                return "true";
            };
            return "false";
        })()), Halogen_HTML_Properties.tabIndex((function () {
            var $30 = props.keyboardDrag && !props.disabled;
            if ($30) {
                return 0;
            };
            return -1 | 0;
        })()), Halogen_HTML_Properties_ARIA.role("button"), Halogen_HTML_Properties_ARIA.label("Draggable item. Press Space or Enter to grab, arrow keys to move, Escape to cancel.") ])(children);
    };
};
var defaultDragHandleProps = {
    className: ""
};

// | Drag handle component
// |
// | Place inside a draggable to restrict drag initiation to this element.
var dragHandle = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultDragHandleProps)(propMods);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "cursor-grab active:cursor-grabbing touch-none", "flex items-center justify-center", props.className ]), Halogen_HTML_Properties.attr("data-drag-handle")("true"), Halogen_HTML_Properties_ARIA.role("button"), Halogen_HTML_Properties_ARIA.label("Drag handle") ])(children);
    };
};
var createGhost = $foreign.createGhostImpl;
var clearDragState = $foreign.clearDragStateImpl;
var clearDragData = $foreign.clearDragDataImpl;

// | Add custom class
var className = function (c) {
    return function (props) {
        return {
            data: props.data,
            onDragStart: props.onDragStart,
            onDrag: props.onDrag,
            onDragEnd: props.onDragEnd,
            showGhost: props.showGhost,
            ghostOpacity: props.ghostOpacity,
            axis: props.axis,
            bounds: props.bounds,
            handleSelector: props.handleSelector,
            keyboardDrag: props.keyboardDrag,
            keyboardStep: props.keyboardStep,
            disabled: props.disabled,
            className: props.className + (" " + c)
        };
    };
};

// | Constrain dragging within bounds
var bounds = function (b) {
    return function (props) {
        return {
            data: props.data,
            onDragStart: props.onDragStart,
            onDrag: props.onDrag,
            onDragEnd: props.onDragEnd,
            showGhost: props.showGhost,
            ghostOpacity: props.ghostOpacity,
            axis: props.axis,
            handleSelector: props.handleSelector,
            keyboardDrag: props.keyboardDrag,
            keyboardStep: props.keyboardStep,
            disabled: props.disabled,
            className: props.className,
            bounds: new Data_Maybe.Just(b)
        };
    };
};

// | Constrain dragging to axis
var axis = function (a) {
    return function (props) {
        return {
            data: props.data,
            onDragStart: props.onDragStart,
            onDrag: props.onDrag,
            onDragEnd: props.onDragEnd,
            showGhost: props.showGhost,
            ghostOpacity: props.ghostOpacity,
            bounds: props.bounds,
            handleSelector: props.handleSelector,
            keyboardDrag: props.keyboardDrag,
            keyboardStep: props.keyboardStep,
            disabled: props.disabled,
            className: props.className,
            axis: a
        };
    };
};

// | Filter function to accept/reject drops
var accepts = function (fn) {
    return function (props) {
        return {
            onDrop: props.onDrop,
            onDragOver: props.onDragOver,
            onDragLeave: props.onDragLeave,
            dropHighlight: props.dropHighlight,
            className: props.className,
            accepts: new Data_Maybe.Just(fn)
        };
    };
};
export {
    draggable,
    droppable,
    dragHandle,
    dragData,
    onDragStart,
    onDrag,
    onDragEnd,
    showGhost,
    ghostOpacity,
    axis,
    AxisNone,
    AxisX,
    AxisY,
    bounds,
    handleSelector,
    keyboardDrag,
    keyboardStep,
    disabled,
    className,
    onDrop,
    onDragOver,
    onDragLeave,
    accepts,
    dropHighlight,
    dropClassName,
    createGhost,
    updateGhostPosition,
    removeGhost,
    showDropIndicator,
    updateDropIndicator,
    removeDropIndicator,
    getDragState,
    setDragState,
    clearDragState,
    setDragData,
    getDragData,
    clearDragData,
    getBoundingRect,
    getElementAtPoint,
    eqAxis
};
