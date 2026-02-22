// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                    // hydrogen // alertdialog
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | AlertDialog component
// |
// | A modal dialog for confirmations and alerts with action buttons.
// | Based on WAI-ARIA alertdialog role.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Component.AlertDialog as AlertDialog
// |
// | -- Confirmation dialog
// | AlertDialog.alertDialog
// |   [ AlertDialog.open state.showConfirm
// |   , AlertDialog.title "Are you sure?"
// |   , AlertDialog.description "This action cannot be undone."
// |   , AlertDialog.confirmLabel "Delete"
// |   , AlertDialog.cancelLabel "Cancel"
// |   , AlertDialog.variant AlertDialog.Destructive
// |   , AlertDialog.onConfirm HandleConfirm
// |   , AlertDialog.onCancel HandleCancel
// |   ]
// |
// | -- Info dialog (single action)
// | AlertDialog.alertDialog
// |   [ AlertDialog.open state.showInfo
// |   , AlertDialog.title "Information"
// |   , AlertDialog.description "Your session will expire in 5 minutes."
// |   , AlertDialog.confirmLabel "OK"
// |   , AlertDialog.showCancel false
// |   , AlertDialog.onConfirm HandleOK
// |   ]
// |
// | -- With custom content
// | AlertDialog.alertDialogCustom
// |   [ AlertDialog.open state.showCustom
// |   , AlertDialog.onClose HandleClose
// |   ]
// |   [ HH.text "Custom content here" ]
// | ```
import * as DOM_HTML_Indexed_ButtonType from "../DOM.HTML.Indexed.ButtonType/index.js";
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Semigroup from "../Data.Semigroup/index.js";
import * as Halogen_HTML_Core from "../Halogen.HTML.Core/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Events from "../Halogen.HTML.Events/index.js";
import * as Halogen_HTML_Properties from "../Halogen.HTML.Properties/index.js";
import * as Halogen_HTML_Properties_ARIA from "../Halogen.HTML.Properties.ARIA/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";
var append1 = /* #__PURE__ */ Data_Semigroup.append(Data_Semigroup.semigroupArray);
var type_ = /* #__PURE__ */ Halogen_HTML_Properties.type_(Halogen_HTML_Core.isPropButtonType);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // variants
// ═══════════════════════════════════════════════════════════════════════════════
// | AlertDialog variants
var Default = /* #__PURE__ */ (function () {
    function Default() {

    };
    Default.value = new Default();
    return Default;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // variants
// ═══════════════════════════════════════════════════════════════════════════════
// | AlertDialog variants
var Destructive = /* #__PURE__ */ (function () {
    function Destructive() {

    };
    Destructive.value = new Destructive();
    return Destructive;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // variants
// ═══════════════════════════════════════════════════════════════════════════════
// | AlertDialog variants
var Warning = /* #__PURE__ */ (function () {
    function Warning() {

    };
    Warning.value = new Warning();
    return Warning;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // variants
// ═══════════════════════════════════════════════════════════════════════════════
// | AlertDialog variants
var Info = /* #__PURE__ */ (function () {
    function Info() {

    };
    Info.value = new Info();
    return Info;
})();

// | Set variant
var variant = function (v) {
    return function (props) {
        return {
            open: props.open,
            title: props.title,
            description: props.description,
            confirmLabel: props.confirmLabel,
            cancelLabel: props.cancelLabel,
            showCancel: props.showCancel,
            closeOnOverlay: props.closeOnOverlay,
            closeOnEscape: props.closeOnEscape,
            className: props.className,
            onConfirm: props.onConfirm,
            onCancel: props.onCancel,
            onClose: props.onClose,
            variant: v
        };
    };
};

// | Title classes
var titleClasses = "text-lg font-semibold";

// | Set title
var title = function (t) {
    return function (props) {
        return {
            open: props.open,
            description: props.description,
            confirmLabel: props.confirmLabel,
            cancelLabel: props.cancelLabel,
            variant: props.variant,
            showCancel: props.showCancel,
            closeOnOverlay: props.closeOnOverlay,
            closeOnEscape: props.closeOnEscape,
            className: props.className,
            onConfirm: props.onConfirm,
            onCancel: props.onCancel,
            onClose: props.onClose,
            title: t
        };
    };
};

// | Show/hide cancel button
var showCancel = function (s) {
    return function (props) {
        return {
            open: props.open,
            title: props.title,
            description: props.description,
            confirmLabel: props.confirmLabel,
            cancelLabel: props.cancelLabel,
            variant: props.variant,
            closeOnOverlay: props.closeOnOverlay,
            closeOnEscape: props.closeOnEscape,
            className: props.className,
            onConfirm: props.onConfirm,
            onCancel: props.onCancel,
            onClose: props.onClose,
            showCancel: s
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // styling
// ═══════════════════════════════════════════════════════════════════════════════
// | Overlay classes
var overlayClasses = "fixed inset-0 z-50 bg-black/80 animate-in fade-in-0";

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // prop builders
// ═══════════════════════════════════════════════════════════════════════════════
// | Set open state
var open = function (o) {
    return function (props) {
        return {
            title: props.title,
            description: props.description,
            confirmLabel: props.confirmLabel,
            cancelLabel: props.cancelLabel,
            variant: props.variant,
            showCancel: props.showCancel,
            closeOnOverlay: props.closeOnOverlay,
            closeOnEscape: props.closeOnEscape,
            className: props.className,
            onConfirm: props.onConfirm,
            onCancel: props.onCancel,
            onClose: props.onClose,
            open: o
        };
    };
};

// | Set confirm handler
var onConfirm = function (handler) {
    return function (props) {
        return {
            open: props.open,
            title: props.title,
            description: props.description,
            confirmLabel: props.confirmLabel,
            cancelLabel: props.cancelLabel,
            variant: props.variant,
            showCancel: props.showCancel,
            closeOnOverlay: props.closeOnOverlay,
            closeOnEscape: props.closeOnEscape,
            className: props.className,
            onCancel: props.onCancel,
            onClose: props.onClose,
            onConfirm: new Data_Maybe.Just(handler)
        };
    };
};

// | Set close handler (fired on overlay click or escape)
var onClose = function (handler) {
    return function (props) {
        return {
            open: props.open,
            title: props.title,
            description: props.description,
            confirmLabel: props.confirmLabel,
            cancelLabel: props.cancelLabel,
            variant: props.variant,
            showCancel: props.showCancel,
            closeOnOverlay: props.closeOnOverlay,
            closeOnEscape: props.closeOnEscape,
            className: props.className,
            onConfirm: props.onConfirm,
            onCancel: props.onCancel,
            onClose: new Data_Maybe.Just(handler)
        };
    };
};

// | Set cancel handler
var onCancel = function (handler) {
    return function (props) {
        return {
            open: props.open,
            title: props.title,
            description: props.description,
            confirmLabel: props.confirmLabel,
            cancelLabel: props.cancelLabel,
            variant: props.variant,
            showCancel: props.showCancel,
            closeOnOverlay: props.closeOnOverlay,
            closeOnEscape: props.closeOnEscape,
            className: props.className,
            onConfirm: props.onConfirm,
            onClose: props.onClose,
            onCancel: new Data_Maybe.Just(handler)
        };
    };
};

// | Header classes
var headerClasses = "flex flex-col space-y-2 text-center sm:text-left";

// | Footer classes
var footerClasses = "flex flex-col-reverse sm:flex-row sm:justify-end sm:space-x-2";
var eqAlertDialogVariant = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Default && y instanceof Default) {
                return true;
            };
            if (x instanceof Destructive && y instanceof Destructive) {
                return true;
            };
            if (x instanceof Warning && y instanceof Warning) {
                return true;
            };
            if (x instanceof Info && y instanceof Info) {
                return true;
            };
            return false;
        };
    }
};

// | Description classes
var descriptionClasses = "text-sm text-muted-foreground";

// | Set description
var description = function (d) {
    return function (props) {
        return {
            open: props.open,
            title: props.title,
            confirmLabel: props.confirmLabel,
            cancelLabel: props.cancelLabel,
            variant: props.variant,
            showCancel: props.showCancel,
            closeOnOverlay: props.closeOnOverlay,
            closeOnEscape: props.closeOnEscape,
            className: props.className,
            onConfirm: props.onConfirm,
            onCancel: props.onCancel,
            onClose: props.onClose,
            description: d
        };
    };
};

// | Default properties
var defaultProps = /* #__PURE__ */ (function () {
    return {
        open: false,
        title: "",
        description: "",
        confirmLabel: "Confirm",
        cancelLabel: "Cancel",
        variant: Default.value,
        showCancel: true,
        closeOnOverlay: true,
        closeOnEscape: true,
        className: "",
        onConfirm: Data_Maybe.Nothing.value,
        onCancel: Data_Maybe.Nothing.value,
        onClose: Data_Maybe.Nothing.value
    };
})();

// | Content container classes
var contentClasses = "fixed left-[50%] top-[50%] z-50 grid w-full max-w-lg translate-x-[-50%] translate-y-[-50%] gap-4 border bg-background p-6 shadow-lg duration-200 animate-in fade-in-0 zoom-in-95 slide-in-from-left-1/2 slide-in-from-top-[48%] sm:rounded-lg";

// | Set confirm button label
var confirmLabel = function (l) {
    return function (props) {
        return {
            open: props.open,
            title: props.title,
            description: props.description,
            cancelLabel: props.cancelLabel,
            variant: props.variant,
            showCancel: props.showCancel,
            closeOnOverlay: props.closeOnOverlay,
            closeOnEscape: props.closeOnEscape,
            className: props.className,
            onConfirm: props.onConfirm,
            onCancel: props.onCancel,
            onClose: props.onClose,
            confirmLabel: l
        };
    };
};

// | Get confirm button variant classes
var confirmButtonClasses = function (v) {
    if (v instanceof Default) {
        return "bg-primary text-primary-foreground hover:bg-primary/90";
    };
    if (v instanceof Destructive) {
        return "bg-destructive text-destructive-foreground hover:bg-destructive/90";
    };
    if (v instanceof Warning) {
        return "bg-yellow-500 text-white hover:bg-yellow-600";
    };
    if (v instanceof Info) {
        return "bg-blue-500 text-white hover:bg-blue-600";
    };
    throw new Error("Failed pattern match at Hydrogen.Component.AlertDialog (line 104, column 24 - line 112, column 47): " + [ v.constructor.name ]);
};

// | Close on overlay click
var closeOnOverlay = function (c) {
    return function (props) {
        return {
            open: props.open,
            title: props.title,
            description: props.description,
            confirmLabel: props.confirmLabel,
            cancelLabel: props.cancelLabel,
            variant: props.variant,
            showCancel: props.showCancel,
            closeOnEscape: props.closeOnEscape,
            className: props.className,
            onConfirm: props.onConfirm,
            onCancel: props.onCancel,
            onClose: props.onClose,
            closeOnOverlay: c
        };
    };
};

// | Close on escape key
var closeOnEscape = function (c) {
    return function (props) {
        return {
            open: props.open,
            title: props.title,
            description: props.description,
            confirmLabel: props.confirmLabel,
            cancelLabel: props.cancelLabel,
            variant: props.variant,
            showCancel: props.showCancel,
            closeOnOverlay: props.closeOnOverlay,
            className: props.className,
            onConfirm: props.onConfirm,
            onCancel: props.onCancel,
            onClose: props.onClose,
            closeOnEscape: c
        };
    };
};

// | Add custom class
var className = function (c) {
    return function (props) {
        return {
            open: props.open,
            title: props.title,
            description: props.description,
            confirmLabel: props.confirmLabel,
            cancelLabel: props.cancelLabel,
            variant: props.variant,
            showCancel: props.showCancel,
            closeOnOverlay: props.closeOnOverlay,
            closeOnEscape: props.closeOnEscape,
            onConfirm: props.onConfirm,
            onCancel: props.onCancel,
            onClose: props.onClose,
            className: props.className + (" " + c)
        };
    };
};

// | Set cancel button label
var cancelLabel = function (l) {
    return function (props) {
        return {
            open: props.open,
            title: props.title,
            description: props.description,
            confirmLabel: props.confirmLabel,
            variant: props.variant,
            showCancel: props.showCancel,
            closeOnOverlay: props.closeOnOverlay,
            closeOnEscape: props.closeOnEscape,
            className: props.className,
            onConfirm: props.onConfirm,
            onCancel: props.onCancel,
            onClose: props.onClose,
            cancelLabel: l
        };
    };
};

// | Cancel button classes
var cancelButtonClasses = "mt-2 sm:mt-0 border border-input bg-background hover:bg-accent hover:text-accent-foreground";

// | Base button classes
var buttonBaseClasses = "inline-flex items-center justify-center whitespace-nowrap rounded-md text-sm font-medium ring-offset-background transition-colors focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2 disabled:pointer-events-none disabled:opacity-50 h-10 px-4 py-2";

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // components
// ═══════════════════════════════════════════════════════════════════════════════
// | AlertDialog trigger (for use with uncontrolled pattern)
var alertDialogTrigger = function (children) {
    return Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "inline-block" ]) ])(children);
};

// | AlertDialog title
var alertDialogTitle = function (text) {
    return Halogen_HTML_Elements.h2([ Hydrogen_UI_Core.cls([ titleClasses ]), Halogen_HTML_Properties.id("alert-dialog-title") ])([ Halogen_HTML_Core.text(text) ]);
};

// | AlertDialog header
var alertDialogHeader = function (children) {
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ headerClasses ]) ])(children);
};

// | AlertDialog footer
var alertDialogFooter = function (children) {
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ footerClasses ]) ])(children);
};

// | AlertDialog description
var alertDialogDescription = function (text) {
    return Halogen_HTML_Elements.p([ Hydrogen_UI_Core.cls([ descriptionClasses ]), Halogen_HTML_Properties.id("alert-dialog-description") ])([ Halogen_HTML_Core.text(text) ]);
};

// | AlertDialog with custom content
var alertDialogCustom = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        var overlayHandler = (function () {
            if (props.closeOnOverlay) {
                if (props.onClose instanceof Data_Maybe.Just) {
                    return [ Halogen_HTML_Events.onClick(function (v) {
                        return props.onClose.value0;
                    }) ];
                };
                if (props.onClose instanceof Data_Maybe.Nothing) {
                    return [  ];
                };
                throw new Error("Failed pattern match at Hydrogen.Component.AlertDialog (line 425, column 14 - line 427, column 24): " + [ props.onClose.constructor.name ]);
            };
            return [  ];
        })();
        var $31 = !props.open;
        if ($31) {
            return Halogen_HTML_Core.text("");
        };
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "relative z-50" ]) ])([ Halogen_HTML_Elements.div(append1([ Hydrogen_UI_Core.cls([ overlayClasses ]) ])(overlayHandler))([  ]), Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ contentClasses, props.className ]), Halogen_HTML_Properties_ARIA.role("alertdialog"), Halogen_HTML_Properties_ARIA.modal("true") ])(children) ]);
    };
};

// | AlertDialog content wrapper
var alertDialogContent = function (customClass) {
    return function (children) {
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ contentClasses, customClass ]), Halogen_HTML_Properties_ARIA.role("alertdialog"), Halogen_HTML_Properties_ARIA.modal("true") ])(children);
    };
};

// | AlertDialog cancel button
var alertDialogCancel = function (opts) {
    var clickHandler = (function () {
        if (opts.onClick instanceof Data_Maybe.Just) {
            return [ Halogen_HTML_Events.onClick(function (v) {
                return opts.onClick.value0;
            }) ];
        };
        if (opts.onClick instanceof Data_Maybe.Nothing) {
            return [  ];
        };
        throw new Error("Failed pattern match at Hydrogen.Component.AlertDialog (line 332, column 20 - line 334, column 20): " + [ opts.onClick.constructor.name ]);
    })();
    return Halogen_HTML_Elements.button(append1([ Hydrogen_UI_Core.cls([ buttonBaseClasses, cancelButtonClasses ]), type_(DOM_HTML_Indexed_ButtonType.ButtonButton.value) ])(clickHandler))([ Halogen_HTML_Core.text(opts.label) ]);
};

// | AlertDialog action button
var alertDialogAction = function (opts) {
    var clickHandler = (function () {
        if (opts.onClick instanceof Data_Maybe.Just) {
            return [ Halogen_HTML_Events.onClick(function (v) {
                return opts.onClick.value0;
            }) ];
        };
        if (opts.onClick instanceof Data_Maybe.Nothing) {
            return [  ];
        };
        throw new Error("Failed pattern match at Hydrogen.Component.AlertDialog (line 315, column 20 - line 317, column 20): " + [ opts.onClick.constructor.name ]);
    })();
    return Halogen_HTML_Elements.button(append1([ Hydrogen_UI_Core.cls([ buttonBaseClasses, confirmButtonClasses(opts.variant) ]), type_(DOM_HTML_Indexed_ButtonType.ButtonButton.value) ])(clickHandler))([ Halogen_HTML_Core.text(opts.label) ]);
};

// | Full AlertDialog with standard layout
var alertDialog = function (propMods) {
    var props = Data_Array.foldl(function (p) {
        return function (f) {
            return f(p);
        };
    })(defaultProps)(propMods);
    
    // Overlay click handler
var overlayHandler = (function () {
        if (props.closeOnOverlay) {
            if (props.onClose instanceof Data_Maybe.Just) {
                return [ Halogen_HTML_Events.onClick(function (v) {
                    return props.onClose.value0;
                }) ];
            };
            if (props.onClose instanceof Data_Maybe.Nothing) {
                if (props.onCancel instanceof Data_Maybe.Just) {
                    return [ Halogen_HTML_Events.onClick(function (v) {
                        return props.onCancel.value0;
                    }) ];
                };
                if (props.onCancel instanceof Data_Maybe.Nothing) {
                    return [  ];
                };
                throw new Error("Failed pattern match at Hydrogen.Component.AlertDialog (line 354, column 22 - line 356, column 26): " + [ props.onCancel.constructor.name ]);
            };
            throw new Error("Failed pattern match at Hydrogen.Component.AlertDialog (line 352, column 14 - line 356, column 26): " + [ props.onClose.constructor.name ]);
        };
        return [  ];
    })();
    
    // Confirm handler
var confirmHandler = (function () {
        if (props.onConfirm instanceof Data_Maybe.Just) {
            return new Data_Maybe.Just(props.onConfirm.value0);
        };
        if (props.onConfirm instanceof Data_Maybe.Nothing) {
            return Data_Maybe.Nothing.value;
        };
        throw new Error("Failed pattern match at Hydrogen.Component.AlertDialog (line 360, column 22 - line 362, column 25): " + [ props.onConfirm.constructor.name ]);
    })();
    
    // Cancel handler
var cancelHandler = (function () {
        if (props.onCancel instanceof Data_Maybe.Just) {
            return new Data_Maybe.Just(props.onCancel.value0);
        };
        if (props.onCancel instanceof Data_Maybe.Nothing) {
            return props.onClose;
        };
        throw new Error("Failed pattern match at Hydrogen.Component.AlertDialog (line 365, column 21 - line 367, column 31): " + [ props.onCancel.constructor.name ]);
    })();
    var $45 = !props.open;
    if ($45) {
        return Halogen_HTML_Core.text("");
    };
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "relative z-50" ]) ])([ Halogen_HTML_Elements.div(append1([ Hydrogen_UI_Core.cls([ overlayClasses ]) ])(overlayHandler))([  ]), Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ contentClasses, props.className ]), Halogen_HTML_Properties_ARIA.role("alertdialog"), Halogen_HTML_Properties_ARIA.modal("true"), Halogen_HTML_Properties_ARIA.labelledBy("alert-dialog-title"), Halogen_HTML_Properties_ARIA.describedBy("alert-dialog-description") ])([ alertDialogHeader([ alertDialogTitle(props.title), alertDialogDescription(props.description) ]), alertDialogFooter(append1((function () {
        if (props.showCancel) {
            return [ alertDialogCancel({
                label: props.cancelLabel,
                onClick: cancelHandler
            }) ];
        };
        return [  ];
    })())([ alertDialogAction({
        label: props.confirmLabel,
        variant: props.variant,
        onClick: confirmHandler
    }) ])) ]) ]);
};
export {
    alertDialog,
    alertDialogCustom,
    alertDialogTrigger,
    alertDialogContent,
    alertDialogHeader,
    alertDialogFooter,
    alertDialogTitle,
    alertDialogDescription,
    alertDialogAction,
    alertDialogCancel,
    defaultProps,
    open,
    title,
    description,
    confirmLabel,
    cancelLabel,
    variant,
    showCancel,
    closeOnOverlay,
    closeOnEscape,
    className,
    onConfirm,
    onCancel,
    onClose,
    Default,
    Destructive,
    Warning,
    Info,
    eqAlertDialogVariant
};
