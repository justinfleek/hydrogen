// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                         // hydrogen // footer
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Footer component
// |
// | A responsive footer with configurable columns, links, and bottom bar.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Layout.Footer as Footer
// |
// | -- Simple footer
// | Footer.footer []
// |   [ Footer.footerBottom []
// |       [ HH.text "© 2024 MyCompany. All rights reserved." ]
// |   ]
// |
// | -- Multi-column footer
// | Footer.footer []
// |   [ Footer.footerColumns []
// |       [ Footer.footerColumn
// |           { title: "Product"
// |           , links: 
// |               [ { label: "Features", href: "/features" }
// |               , { label: "Pricing", href: "/pricing" }
// |               ]
// |           }
// |       , Footer.footerColumn
// |           { title: "Company"
// |           , links:
// |               [ { label: "About", href: "/about" }
// |               , { label: "Blog", href: "/blog" }
// |               ]
// |           }
// |       ]
// |   , Footer.footerBottom []
// |       [ HH.text "© 2024 MyCompany" ]
// |   ]
// | ```
import * as DOM_HTML_Indexed_ButtonType from "../DOM.HTML.Indexed.ButtonType/index.js";
import * as DOM_HTML_Indexed_InputType from "../DOM.HTML.Indexed.InputType/index.js";
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Halogen_HTML_Core from "../Halogen.HTML.Core/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Properties from "../Halogen.HTML.Properties/index.js";
import * as Halogen_HTML_Properties_ARIA from "../Halogen.HTML.Properties.ARIA/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";
var type_ = /* #__PURE__ */ Halogen_HTML_Properties.type_(Halogen_HTML_Core.isPropInputType);
var type_1 = /* #__PURE__ */ Halogen_HTML_Properties.type_(Halogen_HTML_Core.isPropButtonType);
var map = /* #__PURE__ */ Data_Functor.map(Data_Functor.functorArray);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Footer variants
var Default = /* #__PURE__ */ (function () {
    function Default() {

    };
    Default.value = new Default();
    return Default;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Footer variants
var Minimal = /* #__PURE__ */ (function () {
    function Minimal() {

    };
    Minimal.value = new Minimal();
    return Minimal;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Footer variants
var Centered = /* #__PURE__ */ (function () {
    function Centered() {

    };
    Centered.value = new Centered();
    return Centered;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════
// | Footer variants
var Dark = /* #__PURE__ */ (function () {
    function Dark() {

    };
    Dark.value = new Dark();
    return Dark;
})();

// | Inner wrapper classes
var wrapperClasses = "mx-auto px-4 sm:px-6 lg:px-8 py-12";

// | Get variant classes
var variantClasses = function (v) {
    if (v instanceof Default) {
        return "bg-background border-t";
    };
    if (v instanceof Minimal) {
        return "bg-background";
    };
    if (v instanceof Centered) {
        return "bg-background border-t text-center";
    };
    if (v instanceof Dark) {
        return "bg-foreground text-background";
    };
    throw new Error("Failed pattern match at Hydrogen.Layout.Footer (line 90, column 18 - line 94, column 42): " + [ v.constructor.name ]);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // prop builders
// ═══════════════════════════════════════════════════════════════════════════════
// | Set variant
var variant = function (v) {
    return function (props) {
        return {
            maxWidth: props.maxWidth,
            bordered: props.bordered,
            className: props.className,
            variant: v
        };
    };
};

// | Social icon classes
var socialIconClasses = "text-muted-foreground hover:text-foreground transition-colors";

// | Social links container classes
var socialClasses = "flex space-x-6";

// | Newsletter input classes
var newsletterInputClasses = "flex h-10 rounded-md border border-input bg-background px-3 py-2 text-sm ring-offset-background placeholder:text-muted-foreground focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2";

// | Newsletter form classes
var newsletterClasses = "flex flex-col sm:flex-row gap-2";

// | Newsletter button classes
var newsletterButtonClasses = "inline-flex items-center justify-center rounded-md text-sm font-medium h-10 px-4 bg-primary text-primary-foreground hover:bg-primary/90";

// | Set max width
var maxWidth = function (m) {
    return function (props) {
        return {
            variant: props.variant,
            bordered: props.bordered,
            className: props.className,
            maxWidth: m
        };
    };
};

// | Link classes
var linkClasses = "block text-sm text-muted-foreground hover:text-foreground transition-colors";

// | Social links section
var footerSocial = function (icons) {
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ socialClasses ]) ])(icons);
};

// | Newsletter signup form
var footerNewsletter = function (config) {
    return Halogen_HTML_Elements.form([ Hydrogen_UI_Core.cls([ newsletterClasses ]) ])([ Halogen_HTML_Elements.input([ Hydrogen_UI_Core.cls([ newsletterInputClasses ]), type_(DOM_HTML_Indexed_InputType.InputEmail.value), Halogen_HTML_Properties.placeholder(config.placeholder), Halogen_HTML_Properties_ARIA.label("Email address") ]), Halogen_HTML_Elements.button([ Hydrogen_UI_Core.cls([ newsletterButtonClasses ]), type_1(DOM_HTML_Indexed_ButtonType.ButtonSubmit.value) ])([ Halogen_HTML_Core.text(config.buttonLabel) ]) ]);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // components
// ═══════════════════════════════════════════════════════════════════════════════
// | Create a footer link
var footerLink = function (config) {
    return Halogen_HTML_Elements.a([ Hydrogen_UI_Core.cls([ linkClasses ]), Halogen_HTML_Properties.href(config.href) ])([ Halogen_HTML_Core.text(config.label) ]);
};
var eqFooterVariant = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Default && y instanceof Default) {
                return true;
            };
            if (x instanceof Minimal && y instanceof Minimal) {
                return true;
            };
            if (x instanceof Centered && y instanceof Centered) {
                return true;
            };
            if (x instanceof Dark && y instanceof Dark) {
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
        maxWidth: "max-w-7xl",
        bordered: true,
        className: ""
    };
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // styling
// ═══════════════════════════════════════════════════════════════════════════════
// | Container classes
var containerClasses = "w-full";

// | Full footer component
var footer = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        var containerCls = containerClasses + (" " + (variantClasses(props.variant) + (" " + props.className)));
        return Halogen_HTML_Elements.footer([ Hydrogen_UI_Core.cls([ containerCls ]), Halogen_HTML_Properties_ARIA.label("Footer") ])([ Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ wrapperClasses, props.maxWidth ]) ])(children) ]);
    };
};

// | Columns grid classes
var columnsClasses = "grid grid-cols-2 gap-8 md:grid-cols-4 lg:grid-cols-5";

// | Footer columns container
var footerColumns = function (customClass) {
    return function (children) {
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ columnsClasses, customClass ]) ])(children);
    };
};

// | Column title classes
var columnTitleClasses = "text-sm font-semibold text-foreground uppercase tracking-wider";

// | Column links container classes
var columnLinksClasses = "space-y-3";

// | Column classes
var columnClasses = "space-y-4";

// | Create a footer column
var footerColumn = function (config) {
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ columnClasses ]) ])([ Halogen_HTML_Elements.h3([ Hydrogen_UI_Core.cls([ columnTitleClasses ]) ])([ Halogen_HTML_Core.text(config.title) ]), Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ columnLinksClasses ]) ])(map(footerLink)(config.links)) ]);
};

// | Add custom class
var className = function (c) {
    return function (props) {
        return {
            variant: props.variant,
            maxWidth: props.maxWidth,
            bordered: props.bordered,
            className: props.className + (" " + c)
        };
    };
};

// | Bottom content classes
var bottomContentClasses = "flex flex-col items-center justify-between gap-4 md:flex-row";

// | Bottom bar classes
var bottomClasses = "border-t py-6";

// | Footer bottom bar
var footerBottom = function (customClass) {
    return function (children) {
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ bottomClasses, customClass ]) ])([ Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ bottomContentClasses ]) ])(children) ]);
    };
};

// | Show border
var bordered = function (b) {
    return function (props) {
        return {
            variant: props.variant,
            maxWidth: props.maxWidth,
            className: props.className,
            bordered: b
        };
    };
};
export {
    footer,
    footerColumns,
    footerColumn,
    footerBottom,
    footerLink,
    footerSocial,
    footerNewsletter,
    defaultProps,
    variant,
    maxWidth,
    bordered,
    className,
    Default,
    Minimal,
    Centered,
    Dark,
    eqFooterVariant
};
