// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                     // hydrogen // loadingbar
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | LoadingBar component
// |
// | A progress/loading bar for page transitions and async operations.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Component.LoadingBar as LoadingBar
// |
// | -- Indeterminate loading (continuous animation)
// | LoadingBar.loadingBar
// |   [ LoadingBar.indeterminate true
// |   , LoadingBar.visible state.isLoading
// |   ]
// |
// | -- Determinate progress
// | LoadingBar.loadingBar
// |   [ LoadingBar.progress state.uploadProgress
// |   , LoadingBar.visible true
// |   ]
// |
// | -- Top of page (fixed position)
// | LoadingBar.loadingBar
// |   [ LoadingBar.position LoadingBar.Top
// |   , LoadingBar.indeterminate true
// |   , LoadingBar.visible state.isLoading
// |   ]
// |
// | -- Custom color
// | LoadingBar.loadingBar
// |   [ LoadingBar.color "bg-green-500"
// |   , LoadingBar.progress 75.0
// |   ]
// | ```
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Boolean from "../Data.Boolean/index.js";
import * as Data_Int from "../Data.Int/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Halogen_HTML_Core from "../Halogen.HTML.Core/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Properties from "../Halogen.HTML.Properties/index.js";
import * as Halogen_HTML_Properties_ARIA from "../Halogen.HTML.Properties.ARIA/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showNumber);
var show1 = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Position variants
var Top = /* #__PURE__ */ (function () {
    function Top() {

    };
    Top.value = new Top();
    return Top;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Position variants
var Bottom = /* #__PURE__ */ (function () {
    function Bottom() {

    };
    Bottom.value = new Bottom();
    return Bottom;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Position variants
var Inline = /* #__PURE__ */ (function () {
    function Inline() {

    };
    Inline.value = new Inline();
    return Inline;
})();

// | Set visibility
var visible = function (v) {
    return function (props) {
        return {
            progress: props.progress,
            indeterminate: props.indeterminate,
            position: props.position,
            height: props.height,
            color: props.color,
            showPercentage: props.showPercentage,
            animated: props.animated,
            striped: props.striped,
            className: props.className,
            visible: v
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // styling
// ═══════════════════════════════════════════════════════════════════════════════
// | Background track classes
var trackClasses = "w-full bg-secondary overflow-hidden";

// | Striped pattern classes
var stripedClasses = "bg-[linear-gradient(45deg,rgba(255,255,255,.15)_25%,transparent_25%,transparent_50%,rgba(255,255,255,.15)_50%,rgba(255,255,255,.15)_75%,transparent_75%,transparent)] bg-[length:1rem_1rem]";

// | Enable striped pattern
var striped = function (s) {
    return function (props) {
        return {
            progress: props.progress,
            indeterminate: props.indeterminate,
            visible: props.visible,
            position: props.position,
            height: props.height,
            color: props.color,
            showPercentage: props.showPercentage,
            animated: props.animated,
            className: props.className,
            striped: s
        };
    };
};

// | Show percentage text
var showPercentage = function (s) {
    return function (props) {
        return {
            progress: props.progress,
            indeterminate: props.indeterminate,
            visible: props.visible,
            position: props.position,
            height: props.height,
            color: props.color,
            animated: props.animated,
            striped: props.striped,
            className: props.className,
            showPercentage: s
        };
    };
};

// | Get position classes
var positionClasses = function (v) {
    if (v instanceof Top) {
        return "fixed top-0 left-0 right-0 z-50";
    };
    if (v instanceof Bottom) {
        return "fixed bottom-0 left-0 right-0 z-50";
    };
    if (v instanceof Inline) {
        return "relative w-full";
    };
    throw new Error("Failed pattern match at Hydrogen.Component.LoadingBar (line 85, column 19 - line 88, column 30): " + [ v.constructor.name ]);
};

// | Set position
var position = function (p) {
    return function (props) {
        return {
            progress: props.progress,
            indeterminate: props.indeterminate,
            visible: props.visible,
            height: props.height,
            color: props.color,
            showPercentage: props.showPercentage,
            animated: props.animated,
            striped: props.striped,
            className: props.className,
            position: p
        };
    };
};

// | Percentage container classes
var percentageClasses = "absolute right-2 top-1/2 -translate-y-1/2 text-xs font-medium text-foreground";

// | Indeterminate animation classes
var indeterminateClasses = "animate-loading-bar";

// | Set indeterminate mode
var indeterminate = function (i) {
    return function (props) {
        return {
            progress: props.progress,
            visible: props.visible,
            position: props.position,
            height: props.height,
            color: props.color,
            showPercentage: props.showPercentage,
            animated: props.animated,
            striped: props.striped,
            className: props.className,
            indeterminate: i
        };
    };
};

// | Set height (Tailwind class like "h-1", "h-2", etc)
var height = function (h) {
    return function (props) {
        return {
            progress: props.progress,
            indeterminate: props.indeterminate,
            visible: props.visible,
            position: props.position,
            color: props.color,
            showPercentage: props.showPercentage,
            animated: props.animated,
            striped: props.striped,
            className: props.className,
            height: h
        };
    };
};
var eqPosition = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Top && y instanceof Top) {
                return true;
            };
            if (x instanceof Bottom && y instanceof Bottom) {
                return true;
            };
            if (x instanceof Inline && y instanceof Inline) {
                return true;
            };
            return false;
        };
    }
};

// | Default properties
var defaultProps = /* #__PURE__ */ (function () {
    return {
        progress: 0.0,
        indeterminate: false,
        visible: true,
        position: Inline.value,
        height: "h-1",
        color: "bg-primary",
        showPercentage: false,
        animated: true,
        striped: false,
        className: ""
    };
})();

// | Set color (Tailwind class like "bg-primary", "bg-green-500")
var color = function (c) {
    return function (props) {
        return {
            progress: props.progress,
            indeterminate: props.indeterminate,
            visible: props.visible,
            position: props.position,
            height: props.height,
            showPercentage: props.showPercentage,
            animated: props.animated,
            striped: props.striped,
            className: props.className,
            color: c
        };
    };
};

// | Add custom class
var className = function (c) {
    return function (props) {
        return {
            progress: props.progress,
            indeterminate: props.indeterminate,
            visible: props.visible,
            position: props.position,
            height: props.height,
            color: props.color,
            showPercentage: props.showPercentage,
            animated: props.animated,
            striped: props.striped,
            className: props.className + (" " + c)
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // components
// ═══════════════════════════════════════════════════════════════════════════════
// | Clamp a value between min and max
var clamp = function (minVal) {
    return function (maxVal) {
        return function (val) {
            if (val < minVal) {
                return minVal;
            };
            if (val > maxVal) {
                return maxVal;
            };
            if (Data_Boolean.otherwise) {
                return val;
            };
            throw new Error("Failed pattern match at Hydrogen.Component.LoadingBar (line 209, column 1 - line 209, column 46): " + [ minVal.constructor.name, maxVal.constructor.name, val.constructor.name ]);
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // prop builders
// ═══════════════════════════════════════════════════════════════════════════════
// | Set progress (0-100)
var progress = function (p) {
    return function (props) {
        return {
            indeterminate: props.indeterminate,
            visible: props.visible,
            position: props.position,
            height: props.height,
            color: props.color,
            showPercentage: props.showPercentage,
            animated: props.animated,
            striped: props.striped,
            className: props.className,
            progress: clamp(0.0)(100.0)(p)
        };
    };
};

// | Progress bar classes
var barClasses = "h-full transition-all duration-300 ease-out";

// | Animated stripes classes
var animatedStripesClasses = "animate-[progress-stripes_1s_linear_infinite]";

// | Full loading bar component
var loadingBar = function (propMods) {
    var props = Data_Array.foldl(function (p) {
        return function (f) {
            return f(p);
        };
    })(defaultProps)(propMods);
    
    // Width style
var widthStyle = (function () {
        if (props.indeterminate) {
            return "width: 50%";
        };
        return "width: " + (show(props.progress) + "%");
    })();
    
    // Round percentage for display
var percentageText = show1(Data_Int.round(props.progress)) + "%";
    
    // Bar classes
var barCls = barClasses + (" " + (props.color + ((function () {
        if (props.striped) {
            return " " + stripedClasses;
        };
        return "";
    })() + ((function () {
        var $28 = props.striped && props.animated;
        if ($28) {
            return " " + animatedStripesClasses;
        };
        return "";
    })() + (function () {
        if (props.indeterminate) {
            return " " + indeterminateClasses;
        };
        return "";
    })()))));
    var $30 = !props.visible;
    if ($30) {
        return Halogen_HTML_Core.text("");
    };
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ positionClasses(props.position), props.className ]) ])([ Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ trackClasses, props.height ]), Halogen_HTML_Properties_ARIA.role("progressbar"), Halogen_HTML_Properties_ARIA.valueMin("0"), Halogen_HTML_Properties_ARIA.valueMax("100"), Halogen_HTML_Properties_ARIA.valueNow(show1(Data_Int.round(props.progress))) ])([ Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ barCls ]), Halogen_HTML_Properties.attr("style")(widthStyle) ])([  ]) ]), (function () {
        var $31 = props.showPercentage && !props.indeterminate;
        if ($31) {
            return Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ percentageClasses ]) ])([ Halogen_HTML_Core.text(percentageText) ]);
        };
        return Halogen_HTML_Core.text("");
    })() ]);
};

// | Inline loading bar (convenience wrapper)
var loadingBarInline = function (progressValue) {
    return loadingBar([ progress(progressValue), position(Inline.value) ]);
};

// | Enable animation
var animated = function (a) {
    return function (props) {
        return {
            progress: props.progress,
            indeterminate: props.indeterminate,
            visible: props.visible,
            position: props.position,
            height: props.height,
            color: props.color,
            showPercentage: props.showPercentage,
            striped: props.striped,
            className: props.className,
            animated: a
        };
    };
};
export {
    loadingBar,
    loadingBarInline,
    defaultProps,
    progress,
    indeterminate,
    visible,
    position,
    height,
    color,
    showPercentage,
    animated,
    striped,
    className,
    Top,
    Bottom,
    Inline,
    eqPosition
};
