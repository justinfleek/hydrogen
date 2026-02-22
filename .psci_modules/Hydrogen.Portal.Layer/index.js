// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                         // hydrogen // portal
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Portal system for rendering content outside the component tree
// |
// | Portals allow components to render content into a different part of the
// | DOM, useful for modals, tooltips, dropdowns, and notifications that need
// | to escape overflow:hidden or stacking context issues.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Portal.Layer as Portal
// |
// | -- Initialize the portal system
// | portalRoot <- Portal.createRoot
// |
// | -- Create a layer for modals (high z-index)
// | modalLayer <- Portal.createLayer portalRoot { level: Portal.Modal }
// |
// | -- Render content to the layer
// | Portal.mount modalLayer myModalComponent
// |
// | -- Clean up
// | Portal.unmount modalLayer
// | Portal.destroyRoot portalRoot
// | ```
import * as $foreign from "./foreign.js";
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Data_List_Types from "../Data.List.Types/index.js";
import * as Data_Map_Internal from "../Data.Map.Internal/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Ordering from "../Data.Ordering/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
import * as Effect from "../Effect/index.js";
import * as Effect_Ref from "../Effect.Ref/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Properties from "../Halogen.HTML.Properties/index.js";
var map = /* #__PURE__ */ Data_Functor.map(Effect.functorEffect);
var lookup = /* #__PURE__ */ Data_Map_Internal.lookup(Data_Ord.ordString);
var $$delete = /* #__PURE__ */ Data_Map_Internal["delete"](Data_Ord.ordString);
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);
var insert = /* #__PURE__ */ Data_Map_Internal.insert(Data_Ord.ordString);
var fromFoldable = /* #__PURE__ */ Data_Array.fromFoldable(Data_List_Types.foldableList);
var map1 = /* #__PURE__ */ Data_Functor.map(Data_Functor.functorArray);
var compare = /* #__PURE__ */ Data_Ord.compare(Data_Ord.ordInt);
var $$void = /* #__PURE__ */ Data_Functor["void"](Effect.functorEffect);

// ═══════════════════════════════════════════════════════════════════════════
// Layers
// ═══════════════════════════════════════════════════════════════════════════
// | Predefined layer levels for common use cases
var Dropdown = /* #__PURE__ */ (function () {
    function Dropdown() {

    };
    Dropdown.value = new Dropdown();
    return Dropdown;
})();

// ═══════════════════════════════════════════════════════════════════════════
// Layers
// ═══════════════════════════════════════════════════════════════════════════
// | Predefined layer levels for common use cases
var Sticky = /* #__PURE__ */ (function () {
    function Sticky() {

    };
    Sticky.value = new Sticky();
    return Sticky;
})();

// ═══════════════════════════════════════════════════════════════════════════
// Layers
// ═══════════════════════════════════════════════════════════════════════════
// | Predefined layer levels for common use cases
var Popover = /* #__PURE__ */ (function () {
    function Popover() {

    };
    Popover.value = new Popover();
    return Popover;
})();

// ═══════════════════════════════════════════════════════════════════════════
// Layers
// ═══════════════════════════════════════════════════════════════════════════
// | Predefined layer levels for common use cases
var Modal = /* #__PURE__ */ (function () {
    function Modal() {

    };
    Modal.value = new Modal();
    return Modal;
})();

// ═══════════════════════════════════════════════════════════════════════════
// Layers
// ═══════════════════════════════════════════════════════════════════════════
// | Predefined layer levels for common use cases
var Toast = /* #__PURE__ */ (function () {
    function Toast() {

    };
    Toast.value = new Toast();
    return Toast;
})();

// ═══════════════════════════════════════════════════════════════════════════
// Layers
// ═══════════════════════════════════════════════════════════════════════════
// | Predefined layer levels for common use cases
var Tooltip = /* #__PURE__ */ (function () {
    function Tooltip() {

    };
    Tooltip.value = new Tooltip();
    return Tooltip;
})();

// ═══════════════════════════════════════════════════════════════════════════
// Layers
// ═══════════════════════════════════════════════════════════════════════════
// | Predefined layer levels for common use cases
var Custom = /* #__PURE__ */ (function () {
    function Custom(value0) {
        this.value0 = value0;
    };
    Custom.create = function (value0) {
        return new Custom(value0);
    };
    return Custom;
})();
var unmountAll = function (layer) {
    return function __do() {
        $foreign.unmountAllImpl(layer.element)();
        return Effect_Ref.write(Data_Map_Internal.empty)(layer.mounted)();
    };
};
var unmount = function (layer) {
    return function (key) {
        return function __do() {
            var existing = map(lookup(key))(Effect_Ref.read(layer.mounted))();
            if (existing instanceof Data_Maybe.Just) {
                $foreign.unmountNodeImpl(layer.element)(existing.value0)();
                return Effect_Ref.modify_($$delete(key))(layer.mounted)();
            };
            if (existing instanceof Data_Maybe.Nothing) {
                return Data_Unit.unit;
            };
            throw new Error("Failed pattern match at Hydrogen.Portal.Layer (line 254, column 3 - line 258, column 25): " + [ existing.constructor.name ]);
        };
    };
};
var trapFocus = function (layer) {
    return $foreign.trapFocusImpl(layer.element);
};

// ═══════════════════════════════════════════════════════════════════════════
// Show Instance
// ═══════════════════════════════════════════════════════════════════════════
var showLayerLevel = {
    show: function (v) {
        if (v instanceof Dropdown) {
            return "Dropdown";
        };
        if (v instanceof Sticky) {
            return "Sticky";
        };
        if (v instanceof Popover) {
            return "Popover";
        };
        if (v instanceof Modal) {
            return "Modal";
        };
        if (v instanceof Toast) {
            return "Toast";
        };
        if (v instanceof Tooltip) {
            return "Tooltip";
        };
        if (v instanceof Custom) {
            return "Custom " + show(v.value0);
        };
        throw new Error("Failed pattern match at Hydrogen.Portal.Layer (line 374, column 10 - line 381, column 36): " + [ v.constructor.name ]);
    }
};
var restoreFocus = $foreign.restoreFocusImpl;
var releaseFocus = function (layer) {
    return $foreign.releaseFocusImpl(layer.element);
};

// | Portal with explicit layer reference
var portalWithLayer = function (layer) {
    return function (children) {
        return Halogen_HTML_Elements.div([ Halogen_HTML_Properties.attr("data-portal")("true"), Halogen_HTML_Properties.attr("data-portal-layer")(layer.id) ])(children);
    };
};

// | Mount a DOM node with a specific key (for updates)
var mountWithKey = function (layer) {
    return function (key) {
        return function (node) {
            return function __do() {
                var existing = map(lookup(key))(Effect_Ref.read(layer.mounted))();
                (function () {
                    if (existing instanceof Data_Maybe.Just) {
                        return $foreign.unmountNodeImpl(layer.element)(existing.value0)();
                    };
                    if (existing instanceof Data_Maybe.Nothing) {
                        return Data_Unit.unit;
                    };
                    throw new Error("Failed pattern match at Hydrogen.Portal.Layer (line 241, column 3 - line 243, column 25): " + [ existing.constructor.name ]);
                })();
                $foreign.mountImpl(layer.element)(node)();
                return Effect_Ref.modify_(insert(key)(node))(layer.mounted)();
            };
        };
    };
};
var mount = function (layer) {
    return function (node) {
        return function __do() {
            var n = map(Data_Map_Internal.size)(Effect_Ref.read(layer.mounted))();
            var key = "portal-content-" + show(n);
            mountWithKey(layer)(key)(node)();
            return key;
        };
    };
};

// | Get the z-index for a layer level
var layerLevelToZIndex = function (v) {
    if (v instanceof Dropdown) {
        return 1000;
    };
    if (v instanceof Sticky) {
        return 1100;
    };
    if (v instanceof Popover) {
        return 1200;
    };
    if (v instanceof Modal) {
        return 1300;
    };
    if (v instanceof Toast) {
        return 1400;
    };
    if (v instanceof Tooltip) {
        return 1500;
    };
    if (v instanceof Custom) {
        return v.value0;
    };
    throw new Error("Failed pattern match at Hydrogen.Portal.Layer (line 144, column 22 - line 151, column 16): " + [ v.constructor.name ]);
};

// ═══════════════════════════════════════════════════════════════════════════
// Portal Component
// ═══════════════════════════════════════════════════════════════════════════
// | A simple portal wrapper for Halogen components
// | Renders children into a portal layer
var portal = function (level) {
    return function (children) {
        return Halogen_HTML_Elements.div([ Halogen_HTML_Properties.attr("data-portal")("true"), Halogen_HTML_Properties.attr("data-portal-level")(show(layerLevelToZIndex(level))) ])(children);
    };
};
var sendToBack = function (layer) {
    return $foreign.sendToBackImpl(layer.element)(layerLevelToZIndex(layer.level));
};
var getZIndex = function (layer) {
    return $foreign.getZIndexImpl(layer.element);
};

// | Get the current stacking context
var getStackingContext = function (root) {
    return function __do() {
        var layers = Effect_Ref.read(root.layers)();
        var layerArray = fromFoldable(Data_Map_Internal.values(layers));
        var layerList = map1(function (layer) {
            return {
                id: layer.id,
                level: layer.level,
                zIndex: layerLevelToZIndex(layer.level)
            };
        })(layerArray);
        var sorted = $foreign.sortByImpl(function (v) {
            return v.zIndex;
        })(layerList);
        var topLayer = (function () {
            var v = $foreign.lastImpl(sorted);
            if (v instanceof Data_Maybe.Just) {
                return new Data_Maybe.Just(v.value0.id);
            };
            if (v instanceof Data_Maybe.Nothing) {
                return Data_Maybe.Nothing.value;
            };
            throw new Error("Failed pattern match at Hydrogen.Portal.Layer (line 290, column 16 - line 292, column 25): " + [ v.constructor.name ]);
        })();
        return {
            layers: sorted,
            topLayer: topLayer
        };
    };
};
var eqLayerLevel = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Dropdown && y instanceof Dropdown) {
                return true;
            };
            if (x instanceof Sticky && y instanceof Sticky) {
                return true;
            };
            if (x instanceof Popover && y instanceof Popover) {
                return true;
            };
            if (x instanceof Modal && y instanceof Modal) {
                return true;
            };
            if (x instanceof Toast && y instanceof Toast) {
                return true;
            };
            if (x instanceof Tooltip && y instanceof Tooltip) {
                return true;
            };
            if (x instanceof Custom && y instanceof Custom) {
                return x.value0 === y.value0;
            };
            return false;
        };
    }
};
var ordLayerLevel = {
    compare: function (x) {
        return function (y) {
            if (x instanceof Dropdown && y instanceof Dropdown) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof Dropdown) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof Dropdown) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof Sticky && y instanceof Sticky) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof Sticky) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof Sticky) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof Popover && y instanceof Popover) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof Popover) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof Popover) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof Modal && y instanceof Modal) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof Modal) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof Modal) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof Toast && y instanceof Toast) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof Toast) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof Toast) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof Tooltip && y instanceof Tooltip) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof Tooltip) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof Tooltip) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof Custom && y instanceof Custom) {
                return compare(x.value0)(y.value0);
            };
            throw new Error("Failed pattern match at Hydrogen.Portal.Layer (line 0, column 0 - line 0, column 0): " + [ x.constructor.name, y.constructor.name ]);
        };
    },
    Eq0: function () {
        return eqLayerLevel;
    }
};
var destroyLayer = function (layer) {
    return function __do() {
        unmountAll(layer)();
        return $foreign.destroyLayerImpl(layer.element)();
    };
};
var destroyRoot = function (root) {
    var traverse_ = function (f) {
        return function (arr) {
            return $$void($foreign.traverseImpl(f)(arr));
        };
    };
    return function __do() {
        var layers = Effect_Ref.read(root.layers)();
        var layerArray = fromFoldable(Data_Map_Internal.values(layers));
        traverse_(destroyLayer)(layerArray)();
        return $foreign.destroyRootImpl(root.element)();
    };
};

// | Default layer configuration
var defaultLayerConfig = /* #__PURE__ */ (function () {
    return {
        level: Modal.value,
        className: Data_Maybe.Nothing.value,
        ariaLabel: Data_Maybe.Nothing.value,
        trapFocus: false
    };
})();
var createRootIn = function (parent) {
    return function __do() {
        var element = $foreign.createRootInImpl(parent)();
        var layers = Effect_Ref["new"](Data_Map_Internal.empty)();
        var counter = Effect_Ref["new"](0)();
        return {
            element: element,
            layers: layers,
            counter: counter
        };
    };
};
var createRoot = function __do() {
    var element = $foreign.createRootImpl();
    var layers = Effect_Ref["new"](Data_Map_Internal.empty)();
    var counter = Effect_Ref["new"](0)();
    return {
        element: element,
        layers: layers,
        counter: counter
    };
};
var createLayerWithConfig = function (root) {
    return function (config) {
        return function __do() {
            var n = Effect_Ref.read(root.counter)();
            Effect_Ref.write(n + 1 | 0)(root.counter)();
            var id = "portal-layer-" + show(n);
            var element = $foreign.createLayerImpl(root.element)(id)(layerLevelToZIndex(config.level))(config.className)(config.ariaLabel)(config.trapFocus)();
            var mounted = Effect_Ref["new"](Data_Map_Internal.empty)();
            var layer = {
                id: id,
                element: element,
                level: config.level,
                mounted: mounted
            };
            Effect_Ref.modify_(insert(id)(layer))(root.layers)();
            return layer;
        };
    };
};

// | Create a layer with default config
var createLayer = function (root) {
    return function (level) {
        return createLayerWithConfig(root)({
            level: level,
            className: Data_Maybe.Nothing.value,
            ariaLabel: Data_Maybe.Nothing.value,
            trapFocus: false
        });
    };
};
var bringToFront = function (layer) {
    return $foreign.bringToFrontImpl(layer.element);
};
export {
    createRoot,
    createRootIn,
    destroyRoot,
    Dropdown,
    Sticky,
    Popover,
    Modal,
    Toast,
    Tooltip,
    Custom,
    createLayer,
    createLayerWithConfig,
    destroyLayer,
    mount,
    mountWithKey,
    unmount,
    unmountAll,
    getStackingContext,
    bringToFront,
    sendToBack,
    getZIndex,
    portal,
    portalWithLayer,
    trapFocus,
    releaseFocus,
    restoreFocus,
    eqLayerLevel,
    ordLayerLevel,
    showLayerLevel
};
