// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                        // hydrogen // sidebar
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Sidebar layout component
// |
// | Fixed sidebar with scrollable content area. Supports collapsible,
// | mobile drawer mode, and mini (icons-only) mode.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Layout.Sidebar as Sidebar
// |
// | -- Basic sidebar layout
// | Sidebar.sidebar []
// |   { sidebar: navigationMenu
// |   , content: mainContent
// |   }
// |
// | -- Collapsible sidebar
// | Sidebar.sidebar
// |   [ Sidebar.collapsible true
// |   , Sidebar.collapsed state.sidebarCollapsed
// |   , Sidebar.onCollapse \c -> setState { sidebarCollapsed: c }
// |   ]
// |   { sidebar: nav, content: main }
// |
// | -- Right-positioned sidebar
// | Sidebar.sidebar [ Sidebar.position Sidebar.Right ]
// |   { sidebar: detailsPanel, content: list }
// |
// | -- Mini mode (icons only when collapsed)
// | Sidebar.sidebar
// |   [ Sidebar.miniMode true
// |   , Sidebar.collapsed true
// |   ]
// |   { sidebar: iconNav, content: main }
// | ```
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Halogen_HTML_Core from "../Halogen.HTML.Core/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Properties from "../Halogen.HTML.Properties/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // position
// ═══════════════════════════════════════════════════════════════════════════════
// | Sidebar position
var Left = /* #__PURE__ */ (function () {
    function Left() {

    };
    Left.value = new Left();
    return Left;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // position
// ═══════════════════════════════════════════════════════════════════════════════
// | Sidebar position
var Right = /* #__PURE__ */ (function () {
    function Right() {

    };
    Right.value = new Right();
    return Right;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // breakpoint
// ═══════════════════════════════════════════════════════════════════════════════
// | Mobile breakpoint
var Sm = /* #__PURE__ */ (function () {
    function Sm() {

    };
    Sm.value = new Sm();
    return Sm;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // breakpoint
// ═══════════════════════════════════════════════════════════════════════════════
// | Mobile breakpoint
var Md = /* #__PURE__ */ (function () {
    function Md() {

    };
    Md.value = new Md();
    return Md;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // breakpoint
// ═══════════════════════════════════════════════════════════════════════════════
// | Mobile breakpoint
var Lg = /* #__PURE__ */ (function () {
    function Lg() {

    };
    Lg.value = new Lg();
    return Lg;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // breakpoint
// ═══════════════════════════════════════════════════════════════════════════════
// | Mobile breakpoint
var Xl = /* #__PURE__ */ (function () {
    function Xl() {

    };
    Xl.value = new Xl();
    return Xl;
})();

// | Set sidebar width
var width = function (w) {
    return function (props) {
        return {
            position: props.position,
            miniWidth: props.miniWidth,
            collapsible: props.collapsible,
            collapsed: props.collapsed,
            miniMode: props.miniMode,
            mobileBreakpoint: props.mobileBreakpoint,
            mobileDrawer: props.mobileDrawer,
            overlay: props.overlay,
            onCollapse: props.onCollapse,
            className: props.className,
            sidebarClassName: props.sidebarClassName,
            contentClassName: props.contentClassName,
            width: w
        };
    };
};

// | Add custom class to sidebar
var sidebarClassName = function (c) {
    return function (props) {
        return {
            position: props.position,
            width: props.width,
            miniWidth: props.miniWidth,
            collapsible: props.collapsible,
            collapsed: props.collapsed,
            miniMode: props.miniMode,
            mobileBreakpoint: props.mobileBreakpoint,
            mobileDrawer: props.mobileDrawer,
            overlay: props.overlay,
            onCollapse: props.onCollapse,
            className: props.className,
            contentClassName: props.contentClassName,
            sidebarClassName: props.sidebarClassName + (" " + c)
        };
    };
};

// | Set sidebar position
var position = function (p) {
    return function (props) {
        return {
            width: props.width,
            miniWidth: props.miniWidth,
            collapsible: props.collapsible,
            collapsed: props.collapsed,
            miniMode: props.miniMode,
            mobileBreakpoint: props.mobileBreakpoint,
            mobileDrawer: props.mobileDrawer,
            overlay: props.overlay,
            onCollapse: props.onCollapse,
            className: props.className,
            sidebarClassName: props.sidebarClassName,
            contentClassName: props.contentClassName,
            position: p
        };
    };
};

// | Enable overlay when drawer is open
var overlay = function (o) {
    return function (props) {
        return {
            position: props.position,
            width: props.width,
            miniWidth: props.miniWidth,
            collapsible: props.collapsible,
            collapsed: props.collapsed,
            miniMode: props.miniMode,
            mobileBreakpoint: props.mobileBreakpoint,
            mobileDrawer: props.mobileDrawer,
            onCollapse: props.onCollapse,
            className: props.className,
            sidebarClassName: props.sidebarClassName,
            contentClassName: props.contentClassName,
            overlay: o
        };
    };
};

// | Handle collapse events
var onCollapse = function (f) {
    return function (props) {
        return {
            position: props.position,
            width: props.width,
            miniWidth: props.miniWidth,
            collapsible: props.collapsible,
            collapsed: props.collapsed,
            miniMode: props.miniMode,
            mobileBreakpoint: props.mobileBreakpoint,
            mobileDrawer: props.mobileDrawer,
            overlay: props.overlay,
            className: props.className,
            sidebarClassName: props.sidebarClassName,
            contentClassName: props.contentClassName,
            onCollapse: new Data_Maybe.Just(f)
        };
    };
};

// | Enable mobile drawer mode
var mobileDrawer = function (d) {
    return function (props) {
        return {
            position: props.position,
            width: props.width,
            miniWidth: props.miniWidth,
            collapsible: props.collapsible,
            collapsed: props.collapsed,
            miniMode: props.miniMode,
            mobileBreakpoint: props.mobileBreakpoint,
            overlay: props.overlay,
            onCollapse: props.onCollapse,
            className: props.className,
            sidebarClassName: props.sidebarClassName,
            contentClassName: props.contentClassName,
            mobileDrawer: d
        };
    };
};

// | Set mobile breakpoint
var mobileBreakpoint = function (b) {
    return function (props) {
        return {
            position: props.position,
            width: props.width,
            miniWidth: props.miniWidth,
            collapsible: props.collapsible,
            collapsed: props.collapsed,
            miniMode: props.miniMode,
            mobileDrawer: props.mobileDrawer,
            overlay: props.overlay,
            onCollapse: props.onCollapse,
            className: props.className,
            sidebarClassName: props.sidebarClassName,
            contentClassName: props.contentClassName,
            mobileBreakpoint: b
        };
    };
};

// | Set mini mode width
var miniWidth = function (w) {
    return function (props) {
        return {
            position: props.position,
            width: props.width,
            collapsible: props.collapsible,
            collapsed: props.collapsed,
            miniMode: props.miniMode,
            mobileBreakpoint: props.mobileBreakpoint,
            mobileDrawer: props.mobileDrawer,
            overlay: props.overlay,
            onCollapse: props.onCollapse,
            className: props.className,
            sidebarClassName: props.sidebarClassName,
            contentClassName: props.contentClassName,
            miniWidth: w
        };
    };
};

// | Enable mini mode (icons only when collapsed)
var miniMode = function (m) {
    return function (props) {
        return {
            position: props.position,
            width: props.width,
            miniWidth: props.miniWidth,
            collapsible: props.collapsible,
            collapsed: props.collapsed,
            mobileBreakpoint: props.mobileBreakpoint,
            mobileDrawer: props.mobileDrawer,
            overlay: props.overlay,
            onCollapse: props.onCollapse,
            className: props.className,
            sidebarClassName: props.sidebarClassName,
            contentClassName: props.contentClassName,
            miniMode: m
        };
    };
};
var eqPosition = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Left && y instanceof Left) {
                return true;
            };
            if (x instanceof Right && y instanceof Right) {
                return true;
            };
            return false;
        };
    }
};
var eqBreakpoint = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Sm && y instanceof Sm) {
                return true;
            };
            if (x instanceof Md && y instanceof Md) {
                return true;
            };
            if (x instanceof Lg && y instanceof Lg) {
                return true;
            };
            if (x instanceof Xl && y instanceof Xl) {
                return true;
            };
            return false;
        };
    }
};
var defaultProps = /* #__PURE__ */ (function () {
    return {
        position: Left.value,
        width: "256px",
        miniWidth: "64px",
        collapsible: false,
        collapsed: false,
        miniMode: false,
        mobileBreakpoint: Lg.value,
        mobileDrawer: true,
        overlay: true,
        onCollapse: Data_Maybe.Nothing.value,
        className: "",
        sidebarClassName: "",
        contentClassName: ""
    };
})();

// | Add custom class to content
var contentClassName = function (c) {
    return function (props) {
        return {
            position: props.position,
            width: props.width,
            miniWidth: props.miniWidth,
            collapsible: props.collapsible,
            collapsed: props.collapsed,
            miniMode: props.miniMode,
            mobileBreakpoint: props.mobileBreakpoint,
            mobileDrawer: props.mobileDrawer,
            overlay: props.overlay,
            onCollapse: props.onCollapse,
            className: props.className,
            sidebarClassName: props.sidebarClassName,
            contentClassName: props.contentClassName + (" " + c)
        };
    };
};

// | Enable collapsible sidebar
var collapsible = function (c) {
    return function (props) {
        return {
            position: props.position,
            width: props.width,
            miniWidth: props.miniWidth,
            collapsed: props.collapsed,
            miniMode: props.miniMode,
            mobileBreakpoint: props.mobileBreakpoint,
            mobileDrawer: props.mobileDrawer,
            overlay: props.overlay,
            onCollapse: props.onCollapse,
            className: props.className,
            sidebarClassName: props.sidebarClassName,
            contentClassName: props.contentClassName,
            collapsible: c
        };
    };
};

// | Set collapsed state
var collapsed = function (c) {
    return function (props) {
        return {
            position: props.position,
            width: props.width,
            miniWidth: props.miniWidth,
            collapsible: props.collapsible,
            miniMode: props.miniMode,
            mobileBreakpoint: props.mobileBreakpoint,
            mobileDrawer: props.mobileDrawer,
            overlay: props.overlay,
            onCollapse: props.onCollapse,
            className: props.className,
            sidebarClassName: props.sidebarClassName,
            contentClassName: props.contentClassName,
            collapsed: c
        };
    };
};

// | Add custom class to container
var className = function (c) {
    return function (props) {
        return {
            position: props.position,
            width: props.width,
            miniWidth: props.miniWidth,
            collapsible: props.collapsible,
            collapsed: props.collapsed,
            miniMode: props.miniMode,
            mobileBreakpoint: props.mobileBreakpoint,
            mobileDrawer: props.mobileDrawer,
            overlay: props.overlay,
            onCollapse: props.onCollapse,
            sidebarClassName: props.sidebarClassName,
            contentClassName: props.contentClassName,
            className: props.className + (" " + c)
        };
    };
};
var breakpointClass = function (v) {
    if (v instanceof Sm) {
        return "sm";
    };
    if (v instanceof Md) {
        return "md";
    };
    if (v instanceof Lg) {
        return "lg";
    };
    if (v instanceof Xl) {
        return "xl";
    };
    throw new Error("Failed pattern match at Hydrogen.Layout.Sidebar (line 100, column 19 - line 104, column 13): " + [ v.constructor.name ]);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // component
// ═══════════════════════════════════════════════════════════════════════════════
// | Sidebar layout container
// |
// | Creates a fixed sidebar with scrollable main content.
// | Supports responsive behavior, collapsible states, and mobile drawer mode.
var sidebar = function (propMods) {
    return function (content) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        
        // Sidebar position classes
var sidebarPosition = (function () {
            if (props.position instanceof Left) {
                return "left-0";
            };
            if (props.position instanceof Right) {
                return "right-0";
            };
            throw new Error("Failed pattern match at Hydrogen.Layout.Sidebar (line 239, column 23 - line 241, column 25): " + [ props.position.constructor.name ]);
        })();
        
        // Calculate effective width
var effectiveWidth = (function () {
            if (props.collapsed) {
                if (props.miniMode) {
                    return props.miniWidth;
                };
                return "0px";
            };
            return props.width;
        })();
        
        // Container layout direction
var containerDirection = (function () {
            if (props.position instanceof Left) {
                return "flex-row";
            };
            if (props.position instanceof Right) {
                return "flex-row-reverse";
            };
            throw new Error("Failed pattern match at Hydrogen.Layout.Sidebar (line 225, column 26 - line 227, column 34): " + [ props.position.constructor.name ]);
        })();
        var bp = breakpointClass(props.mobileBreakpoint);
        
        // Mobile drawer styles
var mobileStyles = (function () {
            if (props.mobileDrawer) {
                return "fixed " + (bp + (":relative z-40 " + (bp + ":z-auto top-0 bottom-0 transition-transform duration-300")));
            };
            return "relative";
        })();
        
        // Sidebar visibility classes for responsive
var sidebarVisibility = (function () {
            if (props.mobileDrawer) {
                return bp + (":translate-x-0 " + (function () {
                    if (props.collapsed) {
                        return "translate-x-full";
                    };
                    return "translate-x-0";
                })());
            };
            return "";
        })();
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex h-full w-full overflow-hidden", containerDirection, props.className ]), Halogen_HTML_Properties.attr("data-sidebar")("true") ])([ (function () {
            var $33 = props.mobileDrawer && (props.overlay && !props.collapsed);
            if ($33) {
                return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ bp + ":hidden fixed inset-0 bg-black/50 z-30 transition-opacity" ]) ])([  ]);
            };
            return Halogen_HTML_Core.text("");
        })(), Halogen_HTML_Elements.aside([ Hydrogen_UI_Core.cls([ "flex flex-col bg-background border-border shrink-0 overflow-y-auto overflow-x-hidden", sidebarPosition, mobileStyles, sidebarVisibility, (function () {
            if (props.position instanceof Left) {
                return "border-r";
            };
            if (props.position instanceof Right) {
                return "border-l";
            };
            throw new Error("Failed pattern match at Hydrogen.Layout.Sidebar (line 264, column 19 - line 266, column 40): " + [ props.position.constructor.name ]);
        })(), props.sidebarClassName ]), Halogen_HTML_Properties.style("width: " + (effectiveWidth + ("; min-width: " + effectiveWidth))), Halogen_HTML_Properties.attr("data-sidebar-panel")("true"), Halogen_HTML_Properties.attr("data-collapsed")((function () {
            if (props.collapsed) {
                return "true";
            };
            return "false";
        })()) ])([ content.sidebar ]), Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex-1 overflow-auto min-w-0", props.contentClassName ]), Halogen_HTML_Properties.attr("data-sidebar-content")("true"), Halogen_HTML_Properties.attr("role")("main") ])([ content.content ]) ]);
    };
};
export {
    sidebar,
    position,
    width,
    miniWidth,
    collapsible,
    collapsed,
    miniMode,
    mobileBreakpoint,
    mobileDrawer,
    overlay,
    onCollapse,
    className,
    sidebarClassName,
    contentClassName,
    Left,
    Right,
    Sm,
    Md,
    Lg,
    Xl,
    eqPosition,
    eqBreakpoint
};
