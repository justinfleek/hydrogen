// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                           // hydrogen // card
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Card component with sections
// |
// | Styled card component inspired by shadcn/ui.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Component.Card as Card
// |
// | -- Basic card
// | Card.card []
// |   [ Card.cardHeader []
// |       [ Card.cardTitle [] [ HH.text "Title" ]
// |       , Card.cardDescription [] [ HH.text "Description" ]
// |       ]
// |   , Card.cardContent []
// |       [ HH.p_ [ HH.text "Content goes here" ] ]
// |   , Card.cardFooter []
// |       [ Button.button [] [ HH.text "Action" ] ]
// |   ]
// | ```
import * as Data_Array from "../Data.Array/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";

// | Default props
var defaultProps = {
    className: ""
};

// | Add custom class
var className = function (c) {
    return function (props) {
        return {
            className: props.className + (" " + c)
        };
    };
};

// | Card title
var cardTitle = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.h3([ Hydrogen_UI_Core.cls([ "text-2xl font-semibold leading-none tracking-tight", props.className ]) ])(children);
    };
};

// | Card header section
var cardHeader = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex flex-col space-y-1.5 p-6", props.className ]) ])(children);
    };
};

// | Card footer section
var cardFooter = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex items-center p-6 pt-0", props.className ]) ])(children);
    };
};

// | Card description
var cardDescription = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.p([ Hydrogen_UI_Core.cls([ "text-sm text-muted-foreground", props.className ]) ])(children);
    };
};

// | Card content section
var cardContent = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "p-6 pt-0", props.className ]) ])(children);
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // components
// ═══════════════════════════════════════════════════════════════════════════════
// | Card container
var card = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "rounded-lg border bg-card text-card-foreground shadow-sm", props.className ]) ])(children);
    };
};
export {
    card,
    cardHeader,
    cardTitle,
    cardDescription,
    cardContent,
    cardFooter,
    className
};
