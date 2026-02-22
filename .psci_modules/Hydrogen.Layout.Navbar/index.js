// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                         // hydrogen // navbar
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Navbar component
// |
// | A responsive navigation bar with logo, nav items, and actions.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Layout.Navbar as Navbar
// |
// | -- Basic navbar
// | Navbar.navbar []
// |   { brand: Just (HH.text "MyApp")
// |   , items: 
// |       [ Navbar.navItem { label: "Home", href: "/", active: true }
// |       , Navbar.navItem { label: "About", href: "/about", active: false }
// |       ]
// |   , actions: Just userMenu
// |   }
// |
// | -- Transparent navbar (for hero sections)
// | Navbar.navbar
// |   [ Navbar.variant Navbar.Transparent
// |   , Navbar.sticky true
// |   ]
// |   slots
// |
// | -- With mobile menu
// | Navbar.navbar
// |   [ Navbar.mobileMenuOpen state.menuOpen
// |   , Navbar.onMobileMenuToggle HandleToggle
// |   ]
// |   slots
// | ```
import * as DOM_HTML_Indexed_ButtonType from "../DOM.HTML.Indexed.ButtonType/index.js";
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Semigroup from "../Data.Semigroup/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Halogen_HTML_Core from "../Halogen.HTML.Core/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Events from "../Halogen.HTML.Events/index.js";
import * as Halogen_HTML_Properties from "../Halogen.HTML.Properties/index.js";
import * as Halogen_HTML_Properties_ARIA from "../Halogen.HTML.Properties.ARIA/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";
var append = /* #__PURE__ */ Data_Semigroup.append(Data_Semigroup.semigroupArray);
var type_ = /* #__PURE__ */ Halogen_HTML_Properties.type_(Halogen_HTML_Core.isPropButtonType);
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showBoolean);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Navbar variants
var Default = /* #__PURE__ */ (function () {
    function Default() {

    };
    Default.value = new Default();
    return Default;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Navbar variants
var Transparent = /* #__PURE__ */ (function () {
    function Transparent() {

    };
    Transparent.value = new Transparent();
    return Transparent;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Navbar variants
var Blurred = /* #__PURE__ */ (function () {
    function Blurred() {

    };
    Blurred.value = new Blurred();
    return Blurred;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Navbar variants
var Bordered = /* #__PURE__ */ (function () {
    function Bordered() {

    };
    Bordered.value = new Bordered();
    return Bordered;
})();

// | Inner wrapper classes
var wrapperClasses = "mx-auto px-4 sm:px-6 lg:px-8";

// | Get variant classes
var variantClasses = function (v) {
    if (v instanceof Default) {
        return "bg-background border-b";
    };
    if (v instanceof Transparent) {
        return "bg-transparent";
    };
    if (v instanceof Blurred) {
        return "bg-background/80 backdrop-blur-md border-b";
    };
    if (v instanceof Bordered) {
        return "bg-background border-b-2 border-primary";
    };
    throw new Error("Failed pattern match at Hydrogen.Layout.Navbar (line 95, column 18 - line 99, column 56): " + [ v.constructor.name ]);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // prop builders
// ═══════════════════════════════════════════════════════════════════════════════
// | Set variant
var variant = function (v) {
    return function (props) {
        return {
            sticky: props.sticky,
            bordered: props.bordered,
            blur: props.blur,
            height: props.height,
            maxWidth: props.maxWidth,
            mobileMenuOpen: props.mobileMenuOpen,
            mobileBreakpoint: props.mobileBreakpoint,
            className: props.className,
            onMobileMenuToggle: props.onMobileMenuToggle,
            variant: v
        };
    };
};

// | Make sticky
var sticky = function (s) {
    return function (props) {
        return {
            variant: props.variant,
            bordered: props.bordered,
            blur: props.blur,
            height: props.height,
            maxWidth: props.maxWidth,
            mobileMenuOpen: props.mobileMenuOpen,
            mobileBreakpoint: props.mobileBreakpoint,
            className: props.className,
            onMobileMenuToggle: props.onMobileMenuToggle,
            sticky: s
        };
    };
};

// | Set mobile menu toggle handler
var onMobileMenuToggle = function (handler) {
    return function (props) {
        return {
            variant: props.variant,
            sticky: props.sticky,
            bordered: props.bordered,
            blur: props.blur,
            height: props.height,
            maxWidth: props.maxWidth,
            mobileMenuOpen: props.mobileMenuOpen,
            mobileBreakpoint: props.mobileBreakpoint,
            className: props.className,
            onMobileMenuToggle: new Data_Maybe.Just(handler)
        };
    };
};

// | Nav items container classes (desktop)
var navItemsClasses = "hidden md:flex md:items-center md:space-x-4";

// | Inactive nav item classes
var navItemInactiveClasses = "text-muted-foreground hover:text-foreground hover:bg-accent";

// | Disabled nav item classes
var navItemDisabledClasses = "text-muted-foreground/50 cursor-not-allowed";

// | Nav item classes
var navItemBaseClasses = "inline-flex items-center px-3 py-2 text-sm font-medium rounded-md transition-colors";

// | Active nav item classes
var navItemActiveClasses = "text-foreground bg-accent";

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // components
// ═══════════════════════════════════════════════════════════════════════════════
// | Create a nav item
var navItem = function (config) {
    var stateClasses = (function () {
        if (config.disabled) {
            return navItemDisabledClasses;
        };
        if (config.active) {
            return navItemActiveClasses;
        };
        return navItemInactiveClasses;
    })();
    var ariaCurrent = (function () {
        if (config.active) {
            return [ Halogen_HTML_Properties.attr("aria-current")("page") ];
        };
        return [  ];
    })();
    return Halogen_HTML_Elements.a(append([ Hydrogen_UI_Core.cls([ navItemBaseClasses, stateClasses ]), Halogen_HTML_Properties.href(config.href) ])(ariaCurrent))([ Halogen_HTML_Core.text(config.label) ]);
};

// | Set mobile menu open state
var mobileMenuOpen = function (o) {
    return function (props) {
        return {
            variant: props.variant,
            sticky: props.sticky,
            bordered: props.bordered,
            blur: props.blur,
            height: props.height,
            maxWidth: props.maxWidth,
            mobileBreakpoint: props.mobileBreakpoint,
            className: props.className,
            onMobileMenuToggle: props.onMobileMenuToggle,
            mobileMenuOpen: o
        };
    };
};

// | Mobile menu panel classes
var mobileMenuClasses = "md:hidden border-t bg-background";

// | Set mobile breakpoint
var mobileBreakpoint = function (b) {
    return function (props) {
        return {
            variant: props.variant,
            sticky: props.sticky,
            bordered: props.bordered,
            blur: props.blur,
            height: props.height,
            maxWidth: props.maxWidth,
            mobileMenuOpen: props.mobileMenuOpen,
            className: props.className,
            onMobileMenuToggle: props.onMobileMenuToggle,
            mobileBreakpoint: b
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // icons
// ═══════════════════════════════════════════════════════════════════════════════
// | Menu (hamburger) icon
var menuIcon = /* #__PURE__ */ Halogen_HTML_Elements.element("svg")([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "h-6 w-6" ]), /* #__PURE__ */ Halogen_HTML_Properties.attr("xmlns")("http://www.w3.org/2000/svg"), /* #__PURE__ */ Halogen_HTML_Properties.attr("fill")("none"), /* #__PURE__ */ Halogen_HTML_Properties.attr("viewBox")("0 0 24 24"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke")("currentColor"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke-width")("2") ])([ /* #__PURE__ */ Halogen_HTML_Elements.element("path")([ /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke-linecap")("round"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke-linejoin")("round"), /* #__PURE__ */ Halogen_HTML_Properties.attr("d")("M4 6h16M4 12h16M4 18h16") ])([  ]) ]);

// | Mobile menu button classes
var menuButtonClasses = "inline-flex items-center justify-center p-2 rounded-md text-muted-foreground hover:text-foreground hover:bg-accent focus:outline-none focus:ring-2 focus:ring-ring md:hidden";

// | Set max width (Tailwind class)
var maxWidth = function (m) {
    return function (props) {
        return {
            variant: props.variant,
            sticky: props.sticky,
            bordered: props.bordered,
            blur: props.blur,
            height: props.height,
            mobileMenuOpen: props.mobileMenuOpen,
            mobileBreakpoint: props.mobileBreakpoint,
            className: props.className,
            onMobileMenuToggle: props.onMobileMenuToggle,
            maxWidth: m
        };
    };
};

// | Set height (Tailwind class)
var height = function (h) {
    return function (props) {
        return {
            variant: props.variant,
            sticky: props.sticky,
            bordered: props.bordered,
            blur: props.blur,
            maxWidth: props.maxWidth,
            mobileMenuOpen: props.mobileMenuOpen,
            mobileBreakpoint: props.mobileBreakpoint,
            className: props.className,
            onMobileMenuToggle: props.onMobileMenuToggle,
            height: h
        };
    };
};

// | Flex container classes
var flexClasses = "flex items-center justify-between";
var eqNavbarVariant = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Default && y instanceof Default) {
                return true;
            };
            if (x instanceof Transparent && y instanceof Transparent) {
                return true;
            };
            if (x instanceof Blurred && y instanceof Blurred) {
                return true;
            };
            if (x instanceof Bordered && y instanceof Bordered) {
                return true;
            };
            return false;
        };
    }
};

// | Default properties
var defaultProps = /* #__PURE__ */ (function () {
    return {
        variant: Default.value,
        sticky: false,
        bordered: true,
        blur: false,
        height: "h-16",
        maxWidth: "max-w-7xl",
        mobileMenuOpen: false,
        mobileBreakpoint: "md",
        className: "",
        onMobileMenuToggle: Data_Maybe.Nothing.value
    };
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // styling
// ═══════════════════════════════════════════════════════════════════════════════
// | Container classes
var containerClasses = "w-full z-40";

// | Close (X) icon
var closeIcon = /* #__PURE__ */ Halogen_HTML_Elements.element("svg")([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "h-6 w-6" ]), /* #__PURE__ */ Halogen_HTML_Properties.attr("xmlns")("http://www.w3.org/2000/svg"), /* #__PURE__ */ Halogen_HTML_Properties.attr("fill")("none"), /* #__PURE__ */ Halogen_HTML_Properties.attr("viewBox")("0 0 24 24"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke")("currentColor"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke-width")("2") ])([ /* #__PURE__ */ Halogen_HTML_Elements.element("path")([ /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke-linecap")("round"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke-linejoin")("round"), /* #__PURE__ */ Halogen_HTML_Properties.attr("d")("M6 18L18 6M6 6l12 12") ])([  ]) ]);

// | Mobile menu toggle button
var mobileMenuButton = function (config) {
    var clickHandler = (function () {
        if (config.onClick instanceof Data_Maybe.Just) {
            return [ Halogen_HTML_Events.onClick(function (v) {
                return config.onClick.value0;
            }) ];
        };
        if (config.onClick instanceof Data_Maybe.Nothing) {
            return [  ];
        };
        throw new Error("Failed pattern match at Hydrogen.Layout.Navbar (line 321, column 20 - line 323, column 20): " + [ config.onClick.constructor.name ]);
    })();
    return Halogen_HTML_Elements.button(append([ Hydrogen_UI_Core.cls([ menuButtonClasses ]), type_(DOM_HTML_Indexed_ButtonType.ButtonButton.value), Halogen_HTML_Properties_ARIA.expanded(show(config.open)), Halogen_HTML_Properties_ARIA.controls("mobile-menu"), Halogen_HTML_Properties_ARIA.label((function () {
        if (config.open) {
            return "Close menu";
        };
        return "Open menu";
    })()) ])(clickHandler))([ (function () {
        if (config.open) {
            return closeIcon;
        };
        return menuIcon;
    })() ]);
};

// | Add custom class
var className = function (c) {
    return function (props) {
        return {
            variant: props.variant,
            sticky: props.sticky,
            bordered: props.bordered,
            blur: props.blur,
            height: props.height,
            maxWidth: props.maxWidth,
            mobileMenuOpen: props.mobileMenuOpen,
            mobileBreakpoint: props.mobileBreakpoint,
            onMobileMenuToggle: props.onMobileMenuToggle,
            className: props.className + (" " + c)
        };
    };
};

// | Chevron down icon (for dropdowns)
var chevronDownIcon = /* #__PURE__ */ Halogen_HTML_Elements.element("svg")([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "ml-1 h-4 w-4" ]), /* #__PURE__ */ Halogen_HTML_Properties.attr("xmlns")("http://www.w3.org/2000/svg"), /* #__PURE__ */ Halogen_HTML_Properties.attr("fill")("none"), /* #__PURE__ */ Halogen_HTML_Properties.attr("viewBox")("0 0 24 24"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke")("currentColor"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke-width")("2") ])([ /* #__PURE__ */ Halogen_HTML_Elements.element("path")([ /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke-linecap")("round"), /* #__PURE__ */ Halogen_HTML_Properties.attr("stroke-linejoin")("round"), /* #__PURE__ */ Halogen_HTML_Properties.attr("d")("M19 9l-7 7-7-7") ])([  ]) ]);

// | Create a nav group (for dropdowns)
var navGroup = function (config) {
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "relative" ]) ])([ Halogen_HTML_Elements.button([ Hydrogen_UI_Core.cls([ navItemBaseClasses, navItemInactiveClasses ]), type_(DOM_HTML_Indexed_ButtonType.ButtonButton.value) ])([ Halogen_HTML_Core.text(config.label), chevronDownIcon ]) ]);
};

// | Brand area classes
var brandClasses = "flex-shrink-0";

// | Brand/logo area wrapper
var navBrand = function (children) {
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ brandClasses ]) ])(children);
};

// | Show border
var bordered = function (b) {
    return function (props) {
        return {
            variant: props.variant,
            sticky: props.sticky,
            blur: props.blur,
            height: props.height,
            maxWidth: props.maxWidth,
            mobileMenuOpen: props.mobileMenuOpen,
            mobileBreakpoint: props.mobileBreakpoint,
            className: props.className,
            onMobileMenuToggle: props.onMobileMenuToggle,
            bordered: b
        };
    };
};

// | Enable backdrop blur
var blur = function (b) {
    return function (props) {
        return {
            variant: props.variant,
            sticky: props.sticky,
            bordered: props.bordered,
            height: props.height,
            maxWidth: props.maxWidth,
            mobileMenuOpen: props.mobileMenuOpen,
            mobileBreakpoint: props.mobileBreakpoint,
            className: props.className,
            onMobileMenuToggle: props.onMobileMenuToggle,
            blur: b
        };
    };
};

// | Actions area classes
var actionsClasses = "hidden md:flex md:items-center md:space-x-4";

// | Actions area wrapper
var navActions = function (children) {
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ actionsClasses ]) ])(children);
};

// | Full navbar component
var navbar = function (propMods) {
    return function (slots) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        
        // Container classes
var containerCls = containerClasses + (" " + (variantClasses(props.variant) + ((function () {
            if (props.sticky) {
                return " sticky top-0";
            };
            return "";
        })() + (" " + props.className))));
        return Halogen_HTML_Elements.nav([ Hydrogen_UI_Core.cls([ containerCls ]), Halogen_HTML_Properties_ARIA.label("Main navigation") ])([ Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ wrapperClasses, props.maxWidth ]) ])([ Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ flexClasses, props.height ]) ])([ (function () {
            if (slots.brand instanceof Data_Maybe.Just) {
                return navBrand([ slots.brand.value0 ]);
            };
            if (slots.brand instanceof Data_Maybe.Nothing) {
                return Halogen_HTML_Core.text("");
            };
            throw new Error("Failed pattern match at Hydrogen.Layout.Navbar (line 358, column 17 - line 360, column 40): " + [ slots.brand.constructor.name ]);
        })(), Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ navItemsClasses ]) ])(slots.items), (function () {
            if (slots.actions instanceof Data_Maybe.Just) {
                return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ actionsClasses ]) ])([ slots.actions.value0 ]);
            };
            if (slots.actions instanceof Data_Maybe.Nothing) {
                return Halogen_HTML_Core.text("");
            };
            throw new Error("Failed pattern match at Hydrogen.Layout.Navbar (line 366, column 17 - line 371, column 40): " + [ slots.actions.constructor.name ]);
        })(), mobileMenuButton({
            open: props.mobileMenuOpen,
            onClick: props.onMobileMenuToggle
        }) ]) ]), (function () {
            if (props.mobileMenuOpen) {
                return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ mobileMenuClasses ]), Halogen_HTML_Properties.id("mobile-menu") ])([ Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "px-2 pt-2 pb-3 space-y-1" ]) ])(slots.items), (function () {
                    if (slots.actions instanceof Data_Maybe.Just) {
                        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "pt-4 pb-3 border-t" ]) ])([ slots.actions.value0 ]);
                    };
                    if (slots.actions instanceof Data_Maybe.Nothing) {
                        return Halogen_HTML_Core.text("");
                    };
                    throw new Error("Failed pattern match at Hydrogen.Layout.Navbar (line 389, column 17 - line 394, column 40): " + [ slots.actions.constructor.name ]);
                })() ]);
            };
            return Halogen_HTML_Core.text("");
        })() ]);
    };
};
export {
    navbar,
    navItem,
    navGroup,
    navBrand,
    navActions,
    mobileMenuButton,
    defaultProps,
    variant,
    sticky,
    bordered,
    blur,
    height,
    maxWidth,
    mobileMenuOpen,
    mobileBreakpoint,
    className,
    onMobileMenuToggle,
    Default,
    Transparent,
    Blurred,
    Bordered,
    eqNavbarVariant
};
