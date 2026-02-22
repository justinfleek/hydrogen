// | Loading state UI components
// |
// | Provides consistent loading indicators and skeleton loaders:
// | - Spinners (various sizes)
// | - Loading cards (skeleton placeholders)
// | - Loading messages
// | - Inline loading indicators
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Halogen_HTML_Core from "../Halogen.HTML.Core/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";
var map = /* #__PURE__ */ Data_Functor.map(Data_Functor.functorArray);

// ============================================================
// SPINNERS
// ============================================================
// | Animated loading spinner with configurable size
// |
// | ```purescript
// | spinner "w-8 h-8"  -- 32x32 spinner
// | spinner "w-4 h-4"  -- 16x16 spinner
// | ```
var spinner = function (size) {
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ size, "animate-spin rounded-full border-2 border-muted-foreground border-t-primary" ]) ])([  ]);
};

// | Large spinner (32x32)
var spinnerLg = /* #__PURE__ */ spinner("w-8 h-8");

// | Medium spinner (24x24)
var spinnerMd = /* #__PURE__ */ spinner("w-6 h-6");

// | Small inline spinner (16x16)
var spinnerSm = /* #__PURE__ */ spinner("w-4 h-4");

// | Skeleton pulse effect for text line
// |
// | ```purescript
// | skeletonText "w-32"  -- 128px wide text placeholder
// | skeletonText "w-full"  -- Full width
// | ```
var skeletonText = function (width) {
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "h-4 bg-muted rounded animate-pulse", width ]) ])([  ]);
};

// | Skeleton for a table row with specified number of columns
// |
// | ```purescript
// | skeletonRow 4  -- Row with 4 column placeholders
// | ```
var skeletonRow = function (cols) {
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex items-center gap-4 p-4 border-b border-border animate-pulse" ]) ])(map(function (v) {
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "h-4 flex-1 bg-muted rounded" ]) ])([  ]);
    })(Data_Array.range(1)(cols)));
};

// ============================================================
// LOADING STATES
// ============================================================
// | Centered loading state with spinner and message
// |
// | ```purescript
// | loadingState "Loading your data..."
// | ```
var loadingState = function (message) {
    return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex flex-col items-center justify-center py-12 text-muted-foreground" ]) ])([ spinnerLg, Halogen_HTML_Elements.p([ Hydrogen_UI_Core.cls([ "mt-4 text-sm" ]) ])([ Halogen_HTML_Core.text(message) ]) ]);
};

// | Inline loading indicator with spinner and "Loading..." text
// |
// | Useful for inline sections or buttons
var loadingInline = /* #__PURE__ */ Halogen_HTML_Elements.div([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "flex items-center gap-2 text-muted-foreground" ]) ])([ spinnerSm, /* #__PURE__ */ Halogen_HTML_Elements.span([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "text-sm" ]) ])([ /* #__PURE__ */ Halogen_HTML_Core.text("Loading...") ]) ]);

// | Loading placeholder for larger content cards
var loadingCardLarge = /* #__PURE__ */ Halogen_HTML_Elements.div([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "bg-card border border-border rounded-lg p-6 animate-pulse" ]) ])([ /* #__PURE__ */ Halogen_HTML_Elements.div([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "h-5 w-32 bg-muted rounded mb-4" ]) ])([  ]), /* #__PURE__ */ Halogen_HTML_Elements.div([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "space-y-3" ]) ])([ /* #__PURE__ */ Halogen_HTML_Elements.div([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "h-4 w-full bg-muted rounded" ]) ])([  ]), /* #__PURE__ */ Halogen_HTML_Elements.div([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "h-4 w-3/4 bg-muted rounded" ]) ])([  ]), /* #__PURE__ */ Halogen_HTML_Elements.div([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "h-4 w-1/2 bg-muted rounded" ]) ])([  ]) ]) ]);

// ============================================================
// SKELETON LOADERS
// ============================================================
// | Loading placeholder card (matches typical stat card dimensions)
// |
// | Shows animated pulse effect while content loads
var loadingCard = /* #__PURE__ */ Halogen_HTML_Elements.div([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "bg-card border border-border rounded-lg p-4 animate-pulse" ]) ])([ /* #__PURE__ */ Halogen_HTML_Elements.div([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "h-4 w-24 bg-muted rounded mb-2" ]) ])([  ]), /* #__PURE__ */ Halogen_HTML_Elements.div([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "h-8 w-16 bg-muted rounded mb-1" ]) ])([  ]), /* #__PURE__ */ Halogen_HTML_Elements.div([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "h-3 w-20 bg-muted rounded" ]) ])([  ]) ]);
export {
    spinner,
    spinnerSm,
    spinnerMd,
    spinnerLg,
    loadingState,
    loadingInline,
    loadingCard,
    loadingCardLarge,
    skeletonText,
    skeletonRow
};
