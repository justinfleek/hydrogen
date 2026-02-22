// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                      // hydrogen // scroll-area
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Custom scrollbars with shadow indicators
// |
// | Styled scrollbars with auto-hide, drag support, and scroll shadows
// | to indicate more content. Full touch support.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Interaction.ScrollArea as ScrollArea
// |
// | -- Basic scroll area
// | ScrollArea.scrollArea
// |   [ ScrollArea.height 400
// |   , ScrollArea.autoHide true
// |   ]
// |   [ HH.div_ longContent ]
// |
// | -- With horizontal scrollbar
// | ScrollArea.scrollArea
// |   [ ScrollArea.height 200
// |   , ScrollArea.horizontal true
// |   ]
// |   [ HH.div [ HP.style "width: 2000px" ] wideContent ]
// |
// | -- With scroll shadows
// | ScrollArea.scrollArea
// |   [ ScrollArea.height 300
// |   , ScrollArea.shadows true
// |   ]
// |   [ HH.div_ content ]
// | ```
import * as $foreign from "./foreign.js";
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Semigroup from "../Data.Semigroup/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Data_Unit from "../Data.Unit/index.js";
import * as Effect_Ref from "../Effect.Ref/index.js";
import * as Halogen_HTML_Core from "../Halogen.HTML.Core/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Properties from "../Halogen.HTML.Properties/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showNumber);
var append1 = /* #__PURE__ */ Data_Semigroup.append(Data_Semigroup.semigroupArray);
var max = /* #__PURE__ */ Data_Ord.max(Data_Ord.ordNumber);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Scrollbar orientation
var Vertical = /* #__PURE__ */ (function () {
    function Vertical() {

    };
    Vertical.value = new Vertical();
    return Vertical;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Scrollbar orientation
var Horizontal = /* #__PURE__ */ (function () {
    function Horizontal() {

    };
    Horizontal.value = new Horizontal();
    return Horizontal;
})();

// | Reference for imperative operations
var ScrollAreaRef = function (x) {
    return x;
};

// | Set fixed width
var width = function (w) {
    return function (props) {
        return {
            height: props.height,
            maxHeight: props.maxHeight,
            maxWidth: props.maxWidth,
            horizontal: props.horizontal,
            vertical: props.vertical,
            autoHide: props.autoHide,
            hideDelay: props.hideDelay,
            shadows: props.shadows,
            shadowSize: props.shadowSize,
            scrollbarWidth: props.scrollbarWidth,
            onScroll: props.onScroll,
            className: props.className,
            width: new Data_Maybe.Just(w)
        };
    };
};

// | Enable vertical scrolling (default: true)
var vertical = function (v) {
    return function (props) {
        return {
            height: props.height,
            maxHeight: props.maxHeight,
            width: props.width,
            maxWidth: props.maxWidth,
            horizontal: props.horizontal,
            autoHide: props.autoHide,
            hideDelay: props.hideDelay,
            shadows: props.shadows,
            shadowSize: props.shadowSize,
            scrollbarWidth: props.scrollbarWidth,
            onScroll: props.onScroll,
            className: props.className,
            vertical: v
        };
    };
};

// | Minimum thumb size in pixels
var thumbMinSize = function (s) {
    return function (props) {
        return {
            orientation: props.orientation,
            visible: props.visible,
            thumbPosition: props.thumbPosition,
            thumbSize: props.thumbSize,
            className: props.className,
            thumbClassName: props.thumbClassName,
            thumbMinSize: s
        };
    };
};

// | Custom thumb class
var thumbClassName = function (c) {
    return function (props) {
        return {
            orientation: props.orientation,
            thumbMinSize: props.thumbMinSize,
            visible: props.visible,
            thumbPosition: props.thumbPosition,
            thumbSize: props.thumbSize,
            className: props.className,
            thumbClassName: c
        };
    };
};
var showScrollbarOrientation = {
    show: function (v) {
        if (v instanceof Vertical) {
            return "vertical";
        };
        if (v instanceof Horizontal) {
            return "horizontal";
        };
        throw new Error("Failed pattern match at Hydrogen.Interaction.ScrollArea (line 101, column 1 - line 103, column 33): " + [ v.constructor.name ]);
    }
};
var show1 = /* #__PURE__ */ Data_Show.show(showScrollbarOrientation);

// | Show scroll shadows at edges
var shadows = function (s) {
    return function (props) {
        return {
            height: props.height,
            maxHeight: props.maxHeight,
            width: props.width,
            maxWidth: props.maxWidth,
            horizontal: props.horizontal,
            vertical: props.vertical,
            autoHide: props.autoHide,
            hideDelay: props.hideDelay,
            shadowSize: props.shadowSize,
            scrollbarWidth: props.scrollbarWidth,
            onScroll: props.onScroll,
            className: props.className,
            shadows: s
        };
    };
};

// | Shadow size in pixels
var shadowSize = function (s) {
    return function (props) {
        return {
            height: props.height,
            maxHeight: props.maxHeight,
            width: props.width,
            maxWidth: props.maxWidth,
            horizontal: props.horizontal,
            vertical: props.vertical,
            autoHide: props.autoHide,
            hideDelay: props.hideDelay,
            shadows: props.shadows,
            scrollbarWidth: props.scrollbarWidth,
            onScroll: props.onScroll,
            className: props.className,
            shadowSize: s
        };
    };
};

// | Scrollbar width in pixels
var scrollbarWidth = function (w) {
    return function (props) {
        return {
            height: props.height,
            maxHeight: props.maxHeight,
            width: props.width,
            maxWidth: props.maxWidth,
            horizontal: props.horizontal,
            vertical: props.vertical,
            autoHide: props.autoHide,
            hideDelay: props.hideDelay,
            shadows: props.shadows,
            shadowSize: props.shadowSize,
            onScroll: props.onScroll,
            className: props.className,
            scrollbarWidth: w
        };
    };
};

// | Scroll to right
var scrollToRight = function (v) {
    return function __do() {
        var maybeContainer = Effect_Ref.read(v.containerRef)();
        var state = Effect_Ref.read(v.state)();
        if (maybeContainer instanceof Data_Maybe.Just) {
            return $foreign.scrollToImpl(maybeContainer.value0)(state.scrollWidth - state.clientWidth)(0.0)();
        };
        if (maybeContainer instanceof Data_Maybe.Nothing) {
            return Data_Unit.unit;
        };
        throw new Error("Failed pattern match at Hydrogen.Interaction.ScrollArea (line 560, column 3 - line 562, column 25): " + [ maybeContainer.constructor.name ]);
    };
};

// | Scroll to bring element into view
var scrollToElement = function (v) {
    return function (selector) {
        return function __do() {
            var maybeContainer = Effect_Ref.read(v.containerRef)();
            if (maybeContainer instanceof Data_Maybe.Just) {
                return $foreign.scrollToElementImpl(maybeContainer.value0)(selector)();
            };
            if (maybeContainer instanceof Data_Maybe.Nothing) {
                return Data_Unit.unit;
            };
            throw new Error("Failed pattern match at Hydrogen.Interaction.ScrollArea (line 534, column 3 - line 536, column 25): " + [ maybeContainer.constructor.name ]);
        };
    };
};

// | Scroll to bottom
var scrollToBottom = function (v) {
    return function __do() {
        var maybeContainer = Effect_Ref.read(v.containerRef)();
        var state = Effect_Ref.read(v.state)();
        if (maybeContainer instanceof Data_Maybe.Just) {
            return $foreign.scrollToImpl(maybeContainer.value0)(0.0)(state.scrollHeight - state.clientHeight)();
        };
        if (maybeContainer instanceof Data_Maybe.Nothing) {
            return Data_Unit.unit;
        };
        throw new Error("Failed pattern match at Hydrogen.Interaction.ScrollArea (line 547, column 3 - line 549, column 25): " + [ maybeContainer.constructor.name ]);
    };
};

// | Scroll to specific position
var scrollTo = function (v) {
    return function (pos) {
        return function __do() {
            var maybeContainer = Effect_Ref.read(v.containerRef)();
            if (maybeContainer instanceof Data_Maybe.Just) {
                return $foreign.scrollToImpl(maybeContainer.value0)(pos.x)(pos.y)();
            };
            if (maybeContainer instanceof Data_Maybe.Nothing) {
                return Data_Unit.unit;
            };
            throw new Error("Failed pattern match at Hydrogen.Interaction.ScrollArea (line 526, column 3 - line 528, column 25): " + [ maybeContainer.constructor.name ]);
        };
    };
};

// | Scroll to left
var scrollToLeft = function (ref) {
    return scrollTo(ref)({
        x: 0.0,
        y: 0.0
    });
};

// | Scroll to top
var scrollToTop = function (ref) {
    return scrollTo(ref)({
        x: 0.0,
        y: 0.0
    });
};

// | Scroll shadow indicators
// |
// | Shows shadows at edges when content is scrollable in that direction.
var scrollShadows = function (opts) {
    var canScrollUp = opts.scrollTop > 0.0;
    var topShadow = (function () {
        var $62 = opts.showVertical && canScrollUp;
        if ($62) {
            return [ Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "pointer-events-none absolute z-10 transition-opacity duration-150", "inset-x-0 top-0" ]), Halogen_HTML_Properties.style("height: " + (show(opts.shadowSize) + "px; background: linear-gradient(to bottom, rgba(0,0,0,0.1), transparent);")) ])([  ]) ];
        };
        return [  ];
    })();
    var canScrollRight = opts.scrollLeft < opts.scrollWidth - opts.clientWidth - 1.0;
    var rightShadow = (function () {
        var $63 = opts.showHorizontal && canScrollRight;
        if ($63) {
            return [ Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "pointer-events-none absolute z-10 transition-opacity duration-150", "inset-y-0 right-0" ]), Halogen_HTML_Properties.style("width: " + (show(opts.shadowSize) + "px; background: linear-gradient(to left, rgba(0,0,0,0.1), transparent);")) ])([  ]) ];
        };
        return [  ];
    })();
    var canScrollLeft = opts.scrollLeft > 0.0;
    var leftShadow = (function () {
        var $64 = opts.showHorizontal && canScrollLeft;
        if ($64) {
            return [ Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "pointer-events-none absolute z-10 transition-opacity duration-150", "inset-y-0 left-0" ]), Halogen_HTML_Properties.style("width: " + (show(opts.shadowSize) + "px; background: linear-gradient(to right, rgba(0,0,0,0.1), transparent);")) ])([  ]) ];
        };
        return [  ];
    })();
    var canScrollDown = opts.scrollTop < opts.scrollHeight - opts.clientHeight - 1.0;
    var bottomShadow = (function () {
        var $65 = opts.showVertical && canScrollDown;
        if ($65) {
            return [ Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "pointer-events-none absolute z-10 transition-opacity duration-150", "inset-x-0 bottom-0" ]), Halogen_HTML_Properties.style("height: " + (show(opts.shadowSize) + "px; background: linear-gradient(to top, rgba(0,0,0,0.1), transparent);")) ])([  ]) ];
        };
        return [  ];
    })();
    return append1(topShadow)(append1(bottomShadow)(append1(leftShadow)(rightShadow)));
};

// | Set scrollbar orientation
var orientation = function (o) {
    return function (props) {
        return {
            thumbMinSize: props.thumbMinSize,
            visible: props.visible,
            thumbPosition: props.thumbPosition,
            thumbSize: props.thumbSize,
            className: props.className,
            thumbClassName: props.thumbClassName,
            orientation: o
        };
    };
};

// | Callback when scrolled
var onScroll = function (handler) {
    return function (props) {
        return {
            height: props.height,
            maxHeight: props.maxHeight,
            width: props.width,
            maxWidth: props.maxWidth,
            horizontal: props.horizontal,
            vertical: props.vertical,
            autoHide: props.autoHide,
            hideDelay: props.hideDelay,
            shadows: props.shadows,
            shadowSize: props.shadowSize,
            scrollbarWidth: props.scrollbarWidth,
            className: props.className,
            onScroll: new Data_Maybe.Just(handler)
        };
    };
};

// | Set max width
var maxWidth = function (w) {
    return function (props) {
        return {
            height: props.height,
            maxHeight: props.maxHeight,
            width: props.width,
            horizontal: props.horizontal,
            vertical: props.vertical,
            autoHide: props.autoHide,
            hideDelay: props.hideDelay,
            shadows: props.shadows,
            shadowSize: props.shadowSize,
            scrollbarWidth: props.scrollbarWidth,
            onScroll: props.onScroll,
            className: props.className,
            maxWidth: new Data_Maybe.Just(w)
        };
    };
};

// | Set max height (scroll when exceeded)
var maxHeight = function (h) {
    return function (props) {
        return {
            height: props.height,
            width: props.width,
            maxWidth: props.maxWidth,
            horizontal: props.horizontal,
            vertical: props.vertical,
            autoHide: props.autoHide,
            hideDelay: props.hideDelay,
            shadows: props.shadows,
            shadowSize: props.shadowSize,
            scrollbarWidth: props.scrollbarWidth,
            onScroll: props.onScroll,
            className: props.className,
            maxHeight: new Data_Maybe.Just(h)
        };
    };
};

// | Enable horizontal scrolling
var horizontal = function (h) {
    return function (props) {
        return {
            height: props.height,
            maxHeight: props.maxHeight,
            width: props.width,
            maxWidth: props.maxWidth,
            vertical: props.vertical,
            autoHide: props.autoHide,
            hideDelay: props.hideDelay,
            shadows: props.shadows,
            shadowSize: props.shadowSize,
            scrollbarWidth: props.scrollbarWidth,
            onScroll: props.onScroll,
            className: props.className,
            horizontal: h
        };
    };
};

// | Delay before hiding scrollbars (ms)
var hideDelay = function (d) {
    return function (props) {
        return {
            height: props.height,
            maxHeight: props.maxHeight,
            width: props.width,
            maxWidth: props.maxWidth,
            horizontal: props.horizontal,
            vertical: props.vertical,
            autoHide: props.autoHide,
            shadows: props.shadows,
            shadowSize: props.shadowSize,
            scrollbarWidth: props.scrollbarWidth,
            onScroll: props.onScroll,
            className: props.className,
            hideDelay: d
        };
    };
};

// | Set fixed height
var height = function (h) {
    return function (props) {
        return {
            maxHeight: props.maxHeight,
            width: props.width,
            maxWidth: props.maxWidth,
            horizontal: props.horizontal,
            vertical: props.vertical,
            autoHide: props.autoHide,
            hideDelay: props.hideDelay,
            shadows: props.shadows,
            shadowSize: props.shadowSize,
            scrollbarWidth: props.scrollbarWidth,
            onScroll: props.onScroll,
            className: props.className,
            height: new Data_Maybe.Just(h)
        };
    };
};

// | Get current scroll position
var getScrollPosition = function (v) {
    return function __do() {
        var maybeContainer = Effect_Ref.read(v.containerRef)();
        if (maybeContainer instanceof Data_Maybe.Just) {
            return $foreign.getScrollPositionImpl(maybeContainer.value0)();
        };
        if (maybeContainer instanceof Data_Maybe.Nothing) {
            return {
                x: 0.0,
                y: 0.0
            };
        };
        throw new Error("Failed pattern match at Hydrogen.Interaction.ScrollArea (line 568, column 3 - line 570, column 39): " + [ maybeContainer.constructor.name ]);
    };
};
var eqScrollbarOrientation = {
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
var eq = /* #__PURE__ */ Data_Eq.eq(eqScrollbarOrientation);
var defaultScrollbarProps = /* #__PURE__ */ (function () {
    return {
        orientation: Vertical.value,
        thumbMinSize: 20.0,
        visible: true,
        thumbPosition: 0.0,
        thumbSize: 0.2,
        className: "",
        thumbClassName: ""
    };
})();

// | Scrollbar thumb (draggable)
var scrollbarThumb = function (propMods) {
    return function (style) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultScrollbarProps)(propMods);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "scroll-area-thumb rounded-full bg-border hover:bg-border/80 transition-colors cursor-pointer", props.thumbClassName ]), Halogen_HTML_Properties.style(style) ])([  ]);
    };
};

// | Custom scrollbar component
var scrollbar = function (propMods) {
    var props = Data_Array.foldl(function (p) {
        return function (f) {
            return f(p);
        };
    })(defaultScrollbarProps)(propMods);
    
    // Calculate thumb position and size
var thumbPosPercent = props.thumbPosition * 100.0;
    var thumbSizePercent = max(props.thumbMinSize / 100.0)(props.thumbSize) * 100.0;
    var visibilityClass = (function () {
        if (props.visible) {
            return "opacity-100";
        };
        return "opacity-0";
    })();
    var isVertical = eq(props.orientation)(Vertical.value);
    var thumbStyle = (function () {
        if (isVertical) {
            return "position: absolute; left: 0; right: 0; top: " + (show(thumbPosPercent) + ("%; height: " + (show(thumbSizePercent) + "%;")));
        };
        return "position: absolute; top: 0; bottom: 0; left: " + (show(thumbPosPercent) + ("%; width: " + (show(thumbSizePercent) + "%;")));
    })();
    var trackStyle = (function () {
        if (isVertical) {
            return "position: absolute; right: 0; top: 0; bottom: 0; width: 8px;";
        };
        return "position: absolute; bottom: 0; left: 0; right: 0; height: 8px;";
    })();
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "scroll-area-scrollbar transition-opacity duration-150", visibilityClass, props.className ]), Halogen_HTML_Properties.style(trackStyle), Halogen_HTML_Properties.attr("data-orientation")(show1(props.orientation)) ])([ scrollbarThumb([ function (p) {
        return {
            orientation: p.orientation,
            thumbMinSize: p.thumbMinSize,
            visible: p.visible,
            thumbPosition: p.thumbPosition,
            thumbSize: p.thumbSize,
            thumbClassName: p.thumbClassName,
            className: props.thumbClassName
        };
    } ])(thumbStyle) ]);
};
var defaultProps = /* #__PURE__ */ (function () {
    return {
        height: Data_Maybe.Nothing.value,
        maxHeight: Data_Maybe.Nothing.value,
        width: Data_Maybe.Nothing.value,
        maxWidth: Data_Maybe.Nothing.value,
        horizontal: false,
        vertical: true,
        autoHide: true,
        hideDelay: 1000.0,
        shadows: false,
        shadowSize: 8.0,
        scrollbarWidth: 8.0,
        onScroll: Data_Maybe.Nothing.value,
        className: ""
    };
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // components
// ═══════════════════════════════════════════════════════════════════════════════
// | Scroll area container with custom scrollbars
// |
// | Hides native scrollbars and renders custom styled ones.
// | Supports both vertical and horizontal scrolling.
var scrollArea = function (propMods) {
    return function (children) {
        return function (state) {
            var dimensionStyle = function (prop) {
                return function (mVal) {
                    if (mVal instanceof Data_Maybe.Just) {
                        return " " + (prop + (": " + (show(mVal.value0) + "px;")));
                    };
                    if (mVal instanceof Data_Maybe.Nothing) {
                        return "";
                    };
                    throw new Error("Failed pattern match at Hydrogen.Interaction.ScrollArea (line 372, column 30 - line 374, column 18): " + [ mVal.constructor.name ]);
                };
            };
            
            // Viewport styles
var viewportStyle = "position: relative; overflow: auto; height: 100%; width: 100%;" + (" scrollbar-width: none; -ms-overflow-style: none;" + " -webkit-overflow-scrolling: touch;");
            var verticalThumbSize = (function () {
                var $76 = state.scrollHeight > 0.0;
                if ($76) {
                    return state.clientHeight / state.scrollHeight;
                };
                return 1.0;
            })();
            
            // Calculate thumb positions
var verticalThumbPos = (function () {
                var $77 = state.scrollHeight > state.clientHeight;
                if ($77) {
                    return state.scrollTop / (state.scrollHeight - state.clientHeight);
                };
                return 0.0;
            })();
            var props = Data_Array.foldl(function (p) {
                return function (f) {
                    return f(p);
                };
            })(defaultProps)(propMods);
            var scrollbarVisible = !props.autoHide || (state.isDragging || state.isHovering);
            
            // Scroll shadows
var shadowEls = (function () {
                if (props.shadows) {
                    return scrollShadows({
                        scrollTop: state.scrollTop,
                        scrollLeft: state.scrollLeft,
                        scrollHeight: state.scrollHeight,
                        scrollWidth: state.scrollWidth,
                        clientHeight: state.clientHeight,
                        clientWidth: state.clientWidth,
                        shadowSize: props.shadowSize,
                        showVertical: props.vertical,
                        showHorizontal: props.horizontal
                    });
                };
                return [  ];
            })();
            var showHoriz = props.horizontal && state.scrollWidth > state.clientWidth;
            
            // Show scrollbars
var showVert = props.vertical && state.scrollHeight > state.clientHeight;
            var horizontalThumbSize = (function () {
                var $79 = state.scrollWidth > 0.0;
                if ($79) {
                    return state.clientWidth / state.scrollWidth;
                };
                return 1.0;
            })();
            var horizontalThumbPos = (function () {
                var $80 = state.scrollWidth > state.clientWidth;
                if ($80) {
                    return state.scrollLeft / (state.scrollWidth - state.clientWidth);
                };
                return 0.0;
            })();
            
            // Calculate container styles
var containerStyle = "position: relative; overflow: hidden;" + (dimensionStyle("height")(props.height) + (dimensionStyle("max-height")(props.maxHeight) + (dimensionStyle("width")(props.width) + dimensionStyle("max-width")(props.maxWidth))));
            return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "scroll-area-root group/scroll-area", props.className ]), Halogen_HTML_Properties.style(containerStyle) ])(append1([ Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "scroll-area-viewport [&::-webkit-scrollbar]:hidden" ]), Halogen_HTML_Properties.style(viewportStyle) ])(children), (function () {
                if (showVert) {
                    return scrollbar([ orientation(Vertical.value), function (p) {
                        return {
                            orientation: p.orientation,
                            thumbMinSize: p.thumbMinSize,
                            thumbPosition: p.thumbPosition,
                            thumbSize: p.thumbSize,
                            className: p.className,
                            thumbClassName: p.thumbClassName,
                            visible: scrollbarVisible
                        };
                    }, function (p) {
                        return {
                            orientation: p.orientation,
                            thumbMinSize: p.thumbMinSize,
                            visible: p.visible,
                            thumbSize: p.thumbSize,
                            className: p.className,
                            thumbClassName: p.thumbClassName,
                            thumbPosition: verticalThumbPos
                        };
                    }, function (p) {
                        return {
                            orientation: p.orientation,
                            thumbMinSize: p.thumbMinSize,
                            visible: p.visible,
                            thumbPosition: p.thumbPosition,
                            className: p.className,
                            thumbClassName: p.thumbClassName,
                            thumbSize: verticalThumbSize
                        };
                    } ]);
                };
                return Halogen_HTML_Core.text("");
            })(), (function () {
                if (showHoriz) {
                    return scrollbar([ orientation(Horizontal.value), function (p) {
                        return {
                            orientation: p.orientation,
                            thumbMinSize: p.thumbMinSize,
                            thumbPosition: p.thumbPosition,
                            thumbSize: p.thumbSize,
                            className: p.className,
                            thumbClassName: p.thumbClassName,
                            visible: scrollbarVisible
                        };
                    }, function (p) {
                        return {
                            orientation: p.orientation,
                            thumbMinSize: p.thumbMinSize,
                            visible: p.visible,
                            thumbSize: p.thumbSize,
                            className: p.className,
                            thumbClassName: p.thumbClassName,
                            thumbPosition: horizontalThumbPos
                        };
                    }, function (p) {
                        return {
                            orientation: p.orientation,
                            thumbMinSize: p.thumbMinSize,
                            visible: p.visible,
                            thumbPosition: p.thumbPosition,
                            className: p.className,
                            thumbClassName: p.thumbClassName,
                            thumbSize: horizontalThumbSize
                        };
                    } ]);
                };
                return Halogen_HTML_Core.text("");
            })(), (function () {
                var $83 = showVert && showHoriz;
                if ($83) {
                    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "scroll-area-corner absolute bottom-0 right-0 bg-border" ]), Halogen_HTML_Properties.style("width: " + (show(props.scrollbarWidth) + ("px; height: " + (show(props.scrollbarWidth) + "px;")))) ])([  ]);
                };
                return Halogen_HTML_Core.text("");
            })() ])(shadowEls));
        };
    };
};

// | Create scroll area ref
var createScrollAreaRef = /* #__PURE__ */ (function () {
    var defaultState = {
        scrollTop: 0.0,
        scrollLeft: 0.0,
        scrollHeight: 0.0,
        scrollWidth: 0.0,
        clientHeight: 0.0,
        clientWidth: 0.0,
        showVertical: false,
        showHorizontal: false,
        isDragging: false,
        isHovering: false
    };
    return function __do() {
        var containerRef = Effect_Ref["new"](Data_Maybe.Nothing.value)();
        var state = Effect_Ref["new"](defaultState)();
        var hideTimeout = Effect_Ref["new"](Data_Maybe.Nothing.value)();
        return {
            containerRef: containerRef,
            state: state,
            hideTimeout: hideTimeout
        };
    };
})();

// | Add custom class
var className = function (c) {
    return function (props) {
        return {
            height: props.height,
            maxHeight: props.maxHeight,
            width: props.width,
            maxWidth: props.maxWidth,
            horizontal: props.horizontal,
            vertical: props.vertical,
            autoHide: props.autoHide,
            hideDelay: props.hideDelay,
            shadows: props.shadows,
            shadowSize: props.shadowSize,
            scrollbarWidth: props.scrollbarWidth,
            onScroll: props.onScroll,
            className: props.className + (" " + c)
        };
    };
};

// | Auto-hide scrollbars when not scrolling
var autoHide = function (a) {
    return function (props) {
        return {
            height: props.height,
            maxHeight: props.maxHeight,
            width: props.width,
            maxWidth: props.maxWidth,
            horizontal: props.horizontal,
            vertical: props.vertical,
            hideDelay: props.hideDelay,
            shadows: props.shadows,
            shadowSize: props.shadowSize,
            scrollbarWidth: props.scrollbarWidth,
            onScroll: props.onScroll,
            className: props.className,
            autoHide: a
        };
    };
};
export {
    scrollArea,
    scrollbar,
    scrollbarThumb,
    scrollShadows,
    Vertical,
    Horizontal,
    height,
    maxHeight,
    width,
    maxWidth,
    horizontal,
    vertical,
    autoHide,
    hideDelay,
    shadows,
    shadowSize,
    scrollbarWidth,
    onScroll,
    className,
    orientation,
    thumbMinSize,
    thumbClassName,
    createScrollAreaRef,
    scrollTo,
    scrollToElement,
    scrollToTop,
    scrollToBottom,
    scrollToLeft,
    scrollToRight,
    getScrollPosition,
    eqScrollbarOrientation,
    showScrollbarOrientation
};
