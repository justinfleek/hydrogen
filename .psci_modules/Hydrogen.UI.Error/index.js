// | Error state UI components
// |
// | Provides consistent error display:
// | - Full-page error states
// | - Error cards
// | - Inline error badges
// | - Empty states (no data)
import * as Halogen_HTML_Core from "../Halogen.HTML.Core/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";

// ============================================================
// ERROR STATES
// ============================================================
// | Full error state with icon and message
// |
// | Centered display for when a major section fails to load
// |
// | ```purescript
// | case data of
// |   Failure err -> errorState err
// |   ...
// | ```
var errorState = function (message) {
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex flex-col items-center justify-center py-12" ]) ])([ Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "w-12 h-12 rounded-full bg-destructive/20 flex items-center justify-center mb-4" ]) ])([ Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "text-destructive text-xl" ]) ])([ Halogen_HTML_Core.text("!") ]) ]), Halogen_HTML_Elements.p([ Hydrogen_UI_Core.cls([ "text-destructive text-sm font-medium mb-2" ]) ])([ Halogen_HTML_Core.text("Failed to load") ]), Halogen_HTML_Elements.p([ Hydrogen_UI_Core.cls([ "text-muted-foreground text-sm text-center max-w-sm" ]) ])([ Halogen_HTML_Core.text(message) ]) ]);
};

// | Simple inline error text
// |
// | Minimal error display for forms or small sections
// |
// | ```purescript
// | errorInline "This field is required"
// | ```
var errorInline = function (message) {
    return Halogen_HTML_Elements.p([ Hydrogen_UI_Core.cls([ "text-destructive text-sm" ]) ])([ Halogen_HTML_Core.text(message) ]);
};

// | Error card (matches card dimensions)
// |
// | For showing errors in card-based layouts
// |
// | ```purescript
// | errorCard "Unable to fetch statistics"
// | ```
var errorCard = function (message) {
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "bg-card border border-destructive/30 rounded-lg p-4" ]) ])([ Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex items-center gap-2 text-destructive mb-1" ]) ])([ Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "text-sm" ]) ])([ Halogen_HTML_Core.text("!") ]), Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "text-sm font-medium" ]) ])([ Halogen_HTML_Core.text("Error") ]) ]), Halogen_HTML_Elements.p([ Hydrogen_UI_Core.cls([ "text-xs text-muted-foreground" ]) ])([ Halogen_HTML_Core.text(message) ]) ]);
};

// | Inline error badge
// |
// | For showing errors inline with other content
// |
// | ```purescript
// | errorBadge "Invalid input"
// | ```
var errorBadge = function (message) {
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex items-center gap-2 px-3 py-2 bg-destructive/10 border border-destructive/30 rounded-md" ]) ])([ Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "text-destructive text-sm" ]) ])([ Halogen_HTML_Core.text("Error:") ]), Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "text-destructive/80 text-sm" ]) ])([ Halogen_HTML_Core.text(message) ]) ]);
};

// ============================================================
// EMPTY STATES
// ============================================================
// | Empty state for when data loads but is empty
// |
// | ```purescript
// | emptyState "No items yet" "Create your first item to get started"
// | ```
var emptyState = function (title) {
    return function (description) {
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex flex-col items-center justify-center py-12 text-center" ]) ])([ Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "w-12 h-12 rounded-full bg-muted flex items-center justify-center mb-4" ]) ])([ Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "text-muted-foreground text-xl" ]) ])([ Halogen_HTML_Core.text("\u2205") ]) ]), Halogen_HTML_Elements.p([ Hydrogen_UI_Core.cls([ "text-foreground font-medium mb-1" ]) ])([ Halogen_HTML_Core.text(title) ]), Halogen_HTML_Elements.p([ Hydrogen_UI_Core.cls([ "text-muted-foreground text-sm max-w-sm" ]) ])([ Halogen_HTML_Core.text(description) ]) ]);
    };
};
export {
    errorState,
    errorCard,
    errorBadge,
    errorInline,
    emptyState
};
