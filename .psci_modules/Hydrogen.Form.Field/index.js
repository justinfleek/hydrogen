// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                          // hydrogen // field
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Form field components
// |
// | Pre-composed form fields with labels, hints, and error display.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Form.Field as Field
// |
// | Field.field
// |   { label: "Email"
// |   , hint: Just "We'll never share your email"
// |   , error: if state.emailError then Just "Invalid email" else Nothing
// |   , required: true
// |   }
// |   [ Input.input [ Input.type_ Input.Email, Input.value state.email ] ]
// | ```
import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Semigroup from "../Data.Semigroup/index.js";
import * as Halogen_HTML_Core from "../Halogen.HTML.Core/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Properties from "../Halogen.HTML.Properties/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";
var append = /* #__PURE__ */ Data_Semigroup.append(Data_Semigroup.semigroupArray);
var eq = /* #__PURE__ */ Data_Eq.eq(/* #__PURE__ */ Data_Maybe.eqMaybe(Data_Eq.eqString));

// | Horizontal form row
var formRow = function (children) {
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex flex-col sm:flex-row gap-4" ]) ])(children);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // form layout
// ═══════════════════════════════════════════════════════════════════════════════
// | Vertical form group with spacing
var formGroup = function (children) {
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "space-y-4" ]) ])(children);
};

// | Required indicator
var fieldRequired = /* #__PURE__ */ Halogen_HTML_Elements.span([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "text-destructive ml-1" ]) ])([ /* #__PURE__ */ Halogen_HTML_Core.text("*") ]);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // field parts
// ═══════════════════════════════════════════════════════════════════════════════
// | Field label
var fieldLabel = function (config) {
    return Halogen_HTML_Elements.label(append([ Hydrogen_UI_Core.cls([ "text-sm font-medium leading-none peer-disabled:cursor-not-allowed peer-disabled:opacity-70" ]) ])((function () {
        if (config.id instanceof Data_Maybe.Just) {
            return [ Halogen_HTML_Properties["for"](config.id.value0) ];
        };
        if (config.id instanceof Data_Maybe.Nothing) {
            return [  ];
        };
        throw new Error("Failed pattern match at Hydrogen.Form.Field (line 80, column 12 - line 82, column 22): " + [ config.id.constructor.name ]);
    })()))([ Halogen_HTML_Core.text(config.label), (function () {
        if (config.required) {
            return fieldRequired;
        };
        return Halogen_HTML_Core.text("");
    })() ]);
};

// | Field hint text
var fieldHint = function (hint) {
    return Halogen_HTML_Elements.p([ Hydrogen_UI_Core.cls([ "text-sm text-muted-foreground" ]) ])([ Halogen_HTML_Core.text(hint) ]);
};

// | Field error message
var fieldError = function (err) {
    return Halogen_HTML_Elements.p([ Hydrogen_UI_Core.cls([ "text-sm text-destructive" ]) ])([ Halogen_HTML_Core.text(err) ]);
};

// | Complete form field with label, input, hint, and error
var field = function (config) {
    return function (children) {
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "space-y-2" ]) ])(append([ fieldLabel(config) ])(append(children)(append((function () {
            if (config.hint instanceof Data_Maybe.Just && eq(config.error)(Data_Maybe.Nothing.value)) {
                return [ fieldHint(config.hint.value0) ];
            };
            return [  ];
        })())((function () {
            if (config.error instanceof Data_Maybe.Just) {
                return [ fieldError(config.error.value0) ];
            };
            if (config.error instanceof Data_Maybe.Nothing) {
                return [  ];
            };
            throw new Error("Failed pattern match at Hydrogen.Form.Field (line 66, column 10 - line 68, column 24): " + [ config.error.constructor.name ]);
        })()))));
    };
};
export {
    field,
    fieldLabel,
    fieldHint,
    fieldError,
    fieldRequired,
    formGroup,
    formRow
};
