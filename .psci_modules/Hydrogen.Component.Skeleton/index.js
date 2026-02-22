// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                       // hydrogen // skeleton
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Skeleton loading component
// |
// | Placeholder loading skeletons for content that is being fetched.
// |
// | ## Features
// |
// | - Text skeleton (lines of varying width)
// | - Circle skeleton (avatar placeholder)
// | - Rectangle skeleton (card/image placeholder)
// | - Custom shapes
// | - Animation variants: pulse, shimmer, wave
// | - Composition helpers for complex layouts
// | - Pre-built presets: card, table, list
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Component.Skeleton as Skeleton
// |
// | -- Basic text skeleton
// | Skeleton.text [ Skeleton.lines 3 ]
// |
// | -- Avatar skeleton
// | Skeleton.circle [ Skeleton.size 48 ]
// |
// | -- Rectangle skeleton
// | Skeleton.rectangle [ Skeleton.width 200, Skeleton.height 100 ]
// |
// | -- With shimmer animation
// | Skeleton.text [ Skeleton.animation Skeleton.Shimmer ]
// |
// | -- Card preset
// | Skeleton.cardSkeleton []
// |
// | -- Table preset
// | Skeleton.tableSkeleton [ Skeleton.rows 5, Skeleton.columns 4 ]
// |
// | -- Compose custom skeleton
// | Skeleton.group [ Skeleton.direction Skeleton.Horizontal ]
// |   [ Skeleton.circle [ Skeleton.size 40 ]
// |   , Skeleton.group [ Skeleton.direction Skeleton.Vertical ]
// |       [ Skeleton.text [ Skeleton.width 120 ]
// |       , Skeleton.text [ Skeleton.width 80 ]
// |       ]
// |   ]
// | ```
import * as Data_Array from "../Data.Array/index.js";
import * as Data_EuclideanRing from "../Data.EuclideanRing/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Properties from "../Halogen.HTML.Properties/index.js";
import * as Halogen_HTML_Properties_ARIA from "../Halogen.HTML.Properties.ARIA/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);
var map = /* #__PURE__ */ Data_Functor.map(Data_Functor.functorArray);
var mod = /* #__PURE__ */ Data_EuclideanRing.mod(Data_EuclideanRing.euclideanRingInt);

// | Group direction
var Horizontal = /* #__PURE__ */ (function () {
    function Horizontal() {

    };
    Horizontal.value = new Horizontal();
    return Horizontal;
})();

// | Group direction
var Vertical = /* #__PURE__ */ (function () {
    function Vertical() {

    };
    Vertical.value = new Vertical();
    return Vertical;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Skeleton animation type
var Pulse = /* #__PURE__ */ (function () {
    function Pulse() {

    };
    Pulse.value = new Pulse();
    return Pulse;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Skeleton animation type
var Shimmer = /* #__PURE__ */ (function () {
    function Shimmer() {

    };
    Shimmer.value = new Shimmer();
    return Shimmer;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Skeleton animation type
var Wave = /* #__PURE__ */ (function () {
    function Wave() {

    };
    Wave.value = new Wave();
    return Wave;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Skeleton animation type
var None = /* #__PURE__ */ (function () {
    function None() {

    };
    None.value = new None();
    return None;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // prop builders
// ═══════════════════════════════════════════════════════════════════════════════
// | Set width (CSS value)
var width = function (w) {
    return function (props) {
        return {
            height: props.height,
            animation: props.animation,
            rounded: props.rounded,
            className: props.className,
            width: w
        };
    };
};

// | Set size (for circle - sets both width and height)
var size = function (s) {
    return function (props) {
        return {
            animation: props.animation,
            rounded: props.rounded,
            className: props.className,
            width: show(s) + "px",
            height: show(s) + "px"
        };
    };
};

// | Set number of rows (for table)
var rows = function (r) {
    return function (props) {
        return {
            columns: props.columns,
            headerHeight: props.headerHeight,
            rowHeight: props.rowHeight,
            animation: props.animation,
            className: props.className,
            rows: r
        };
    };
};

// | Set border radius class
var rounded = function (r) {
    return function (props) {
        return {
            width: props.width,
            height: props.height,
            animation: props.animation,
            className: props.className,
            rounded: r
        };
    };
};

// | Set number of lines (for text skeleton)
var lines = function (v) {
    return function (props) {
        return props;
    };
};

// | Set height (CSS value)
var height = function (h) {
    return function (props) {
        return {
            width: props.width,
            animation: props.animation,
            rounded: props.rounded,
            className: props.className,
            height: h
        };
    };
};

// | Set group gap
var gap = function (g) {
    return function (props) {
        return {
            direction: props.direction,
            className: props.className,
            gap: g
        };
    };
};
var eqDirection = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Horizontal && y instanceof Horizontal) {
                return true;
            };
            if (x instanceof Vertical && y instanceof Vertical) {
                return true;
            };
            return false;
        };
    }
};
var eqAnimation = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Pulse && y instanceof Pulse) {
                return true;
            };
            if (x instanceof Shimmer && y instanceof Shimmer) {
                return true;
            };
            if (x instanceof Wave && y instanceof Wave) {
                return true;
            };
            if (x instanceof None && y instanceof None) {
                return true;
            };
            return false;
        };
    }
};

// | Set group direction
var direction = function (d) {
    return function (props) {
        return {
            gap: props.gap,
            className: props.className,
            direction: d
        };
    };
};

// | Default table properties
var defaultTableProps = /* #__PURE__ */ (function () {
    return {
        rows: 5,
        columns: 4,
        headerHeight: "2.5rem",
        rowHeight: "2rem",
        animation: Pulse.value,
        className: ""
    };
})();

// | Default skeleton properties
var defaultProps = /* #__PURE__ */ (function () {
    return {
        width: "100%",
        height: "1rem",
        animation: Pulse.value,
        rounded: "rounded",
        className: ""
    };
})();

// | Default group properties
var defaultGroupProps = /* #__PURE__ */ (function () {
    return {
        direction: Vertical.value,
        gap: "gap-2",
        className: ""
    };
})();

// | Group skeletons together
// |
// | Layout container for composing skeletons
var group = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultGroupProps)(propMods);
        var directionClass = (function () {
            if (props.direction instanceof Horizontal) {
                return "flex-row items-center";
            };
            if (props.direction instanceof Vertical) {
                return "flex-col";
            };
            throw new Error("Failed pattern match at Hydrogen.Component.Skeleton (line 323, column 22 - line 325, column 29): " + [ props.direction.constructor.name ]);
        })();
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "skeleton-group flex", directionClass, props.gap, props.className ]), Halogen_HTML_Properties_ARIA.hidden("true") ])(children);
    };
};

// | Set number of columns (for table)
var columns = function (c) {
    return function (props) {
        return {
            rows: props.rows,
            headerHeight: props.headerHeight,
            rowHeight: props.rowHeight,
            animation: props.animation,
            className: props.className,
            columns: c
        };
    };
};

// | Add custom class
var className = function (c) {
    return function (props) {
        return {
            width: props.width,
            height: props.height,
            animation: props.animation,
            rounded: props.rounded,
            className: props.className + (" " + c)
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // components
// ═══════════════════════════════════════════════════════════════════════════════
// | Get animation classes
var animationClasses = function (v) {
    if (v instanceof Pulse) {
        return "animate-pulse";
    };
    if (v instanceof Shimmer) {
        return "animate-shimmer bg-gradient-to-r from-muted via-muted-foreground/10 to-muted bg-[length:200%_100%]";
    };
    if (v instanceof Wave) {
        return "animate-wave";
    };
    if (v instanceof None) {
        return "";
    };
    throw new Error("Failed pattern match at Hydrogen.Component.Skeleton (line 241, column 20 - line 245, column 13): " + [ v.constructor.name ]);
};

// | Circle skeleton
// |
// | Circular placeholder (for avatars)
var circle = function (propMods) {
    var props = Data_Array.foldl(function (p) {
        return function (f) {
            return f(p);
        };
    })({
        animation: defaultProps.animation,
        className: defaultProps.className,
        height: defaultProps.height,
        width: defaultProps.width,
        rounded: "rounded-full"
    })(propMods);
    var sizeStyle = "width: " + (props.width + ("; height: " + props.height));
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "skeleton-circle bg-muted rounded-full flex-shrink-0", animationClasses(props.animation), props.className ]), Halogen_HTML_Properties.attr("style")(sizeStyle), Halogen_HTML_Properties_ARIA.hidden("true") ])([  ]);
};

// | Rectangle skeleton
// |
// | Rectangular placeholder (for cards, images)
var rectangle = function (propMods) {
    var props = Data_Array.foldl(function (p) {
        return function (f) {
            return f(p);
        };
    })({
        animation: defaultProps.animation,
        className: defaultProps.className,
        height: defaultProps.height,
        width: defaultProps.width,
        rounded: "rounded-lg"
    })(propMods);
    var sizeStyle = "width: " + (props.width + ("; height: " + props.height));
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "skeleton-rectangle bg-muted", props.rounded, animationClasses(props.animation), props.className ]), Halogen_HTML_Properties.attr("style")(sizeStyle), Halogen_HTML_Properties_ARIA.hidden("true") ])([  ]);
};

// | Base skeleton element
// |
// | Generic skeleton with configurable dimensions
var skeleton = function (propMods) {
    var props = Data_Array.foldl(function (p) {
        return function (f) {
            return f(p);
        };
    })(defaultProps)(propMods);
    var sizeStyle = "width: " + (props.width + ("; height: " + props.height));
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "skeleton bg-muted", props.rounded, animationClasses(props.animation), props.className ]), Halogen_HTML_Properties.attr("style")(sizeStyle), Halogen_HTML_Properties_ARIA.hidden("true") ])([  ]);
};

// | Table skeleton preset
// |
// | Table with header and rows
var tableSkeleton = function (propMods) {
    var props = Data_Array.foldl(function (p) {
        return function (f) {
            return f(p);
        };
    })(defaultTableProps)(propMods);
    var renderRow = function (v) {
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "skeleton-row grid gap-4" ]), Halogen_HTML_Properties.attr("style")("grid-template-columns: repeat(" + (show(props.columns) + ", 1fr)")) ])(Data_Array.replicate(props.columns)(Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "skeleton-cell bg-muted rounded", animationClasses(props.animation) ]), Halogen_HTML_Properties.attr("style")("height: " + props.rowHeight) ])([  ])));
    };
    var headerCells = Data_Array.replicate(props.columns)(Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "skeleton-cell bg-muted rounded", animationClasses(props.animation) ]), Halogen_HTML_Properties.attr("style")("height: " + props.headerHeight) ])([  ]));
    var dataRows = map(renderRow)(Data_Array.range(1)(props.rows));
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "skeleton-table space-y-2", props.className ]), Halogen_HTML_Properties_ARIA.hidden("true"), Halogen_HTML_Properties_ARIA.label("Loading table") ])([ Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "skeleton-header grid gap-4" ]), Halogen_HTML_Properties.attr("style")("grid-template-columns: repeat(" + (show(props.columns) + ", 1fr)")) ])(headerCells), Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "border-b my-2" ]) ])([  ]), Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "skeleton-body space-y-2" ]) ])(dataRows) ]);
};

// | Text skeleton
// |
// | Multiple lines of text placeholder
var text = function (propMods) {
    var props = Data_Array.foldl(function (p) {
        return function (f) {
            return f(p);
        };
    })(defaultProps)(propMods);
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "skeleton-text bg-muted", props.rounded, animationClasses(props.animation), props.className ]), Halogen_HTML_Properties.attr("style")("width: " + (props.width + ("; height: " + props.height))), Halogen_HTML_Properties_ARIA.hidden("true") ])([  ]);
};

// | Avatar with text preset
// |
// | Common pattern: avatar circle with name and subtitle
var avatarWithText = function (propMods) {
    var props = Data_Array.foldl(function (p) {
        return function (f) {
            return f(p);
        };
    })(defaultProps)(propMods);
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "skeleton-avatar-text flex items-center gap-3", animationClasses(props.animation), props.className ]), Halogen_HTML_Properties_ARIA.hidden("true") ])([ circle([ size(40) ]), group([ gap("gap-1") ])([ text([ width("8rem"), height("1rem") ]), text([ width("6rem"), height("0.75rem") ]) ]) ]);
};

// | List skeleton preset
// |
// | List items with avatar and text
var listSkeleton = function (count) {
    return function (propMods) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        var items = map(function (v) {
            return avatarWithText([  ]);
        })(Data_Array.range(1)(count));
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "skeleton-list space-y-4", props.className ]), Halogen_HTML_Properties_ARIA.hidden("true"), Halogen_HTML_Properties_ARIA.label("Loading list") ])(items);
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // presets
// ═══════════════════════════════════════════════════════════════════════════════
// | Card skeleton preset
// |
// | Typical card layout with image, title, and description
var cardSkeleton = function (propMods) {
    var props = Data_Array.foldl(function (p) {
        return function (f) {
            return f(p);
        };
    })(defaultProps)(propMods);
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "skeleton-card space-y-4 p-4 border rounded-lg", animationClasses(props.animation), props.className ]), Halogen_HTML_Properties_ARIA.hidden("true"), Halogen_HTML_Properties_ARIA.label("Loading card") ])([ rectangle([ height("10rem") ]), text([ width("70%"), height("1.25rem") ]), group([  ])([ text([ width("100%"), height("0.875rem") ]), text([ width("90%"), height("0.875rem") ]), text([ width("60%"), height("0.875rem") ]) ]) ]);
};

// | Set animation type
var animation = function (a) {
    return function (props) {
        return {
            width: props.width,
            height: props.height,
            rounded: props.rounded,
            className: props.className,
            animation: a
        };
    };
};

// | Paragraph skeleton
// |
// | Multiple lines with varying widths
var paragraphSkeleton = function (lineCount) {
    return function (propMods) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        
        // Vary widths based on line index
var getWidth = function (idx) {
            var v = mod(idx)(5);
            if (v === 0) {
                return "100%";
            };
            if (v === 1) {
                return "95%";
            };
            if (v === 2) {
                return "85%";
            };
            if (v === 3) {
                return "90%";
            };
            return "70%";
        };
        var renderLine = function (idx) {
            return text([ width(getWidth(idx)), height("0.875rem"), animation(props.animation) ]);
        };
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "skeleton-paragraph space-y-2", props.className ]), Halogen_HTML_Properties_ARIA.hidden("true") ])(map(renderLine)(Data_Array.range(0)(lineCount - 1 | 0)));
    };
};
export {
    skeleton,
    text,
    circle,
    rectangle,
    group,
    cardSkeleton,
    tableSkeleton,
    listSkeleton,
    avatarWithText,
    paragraphSkeleton,
    defaultProps,
    defaultGroupProps,
    defaultTableProps,
    width,
    height,
    size,
    animation,
    rounded,
    lines,
    rows,
    columns,
    direction,
    gap,
    className,
    Pulse,
    Shimmer,
    Wave,
    None,
    Horizontal,
    Vertical,
    eqAnimation,
    eqDirection
};
