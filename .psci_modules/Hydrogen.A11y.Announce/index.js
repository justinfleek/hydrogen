// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                       // hydrogen // announce
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Screen reader announcements
// |
// | ARIA live regions for dynamic content announcements.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.A11y.Announce as Announce
// |
// | -- Polite announcement (doesn't interrupt)
// | Announce.liveRegion Announce.Polite []
// |   [ HH.text "Item added to cart" ]
// |
// | -- Assertive announcement (interrupts)
// | Announce.liveRegion Announce.Assertive []
// |   [ HH.text "Error: Invalid input" ]
// |
// | -- Status message
// | Announce.status [ HH.text "Loading..." ]
// |
// | -- Alert message
// | Announce.alert [ HH.text "Changes saved" ]
// | ```
import * as Data_Array from "../Data.Array/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Properties_ARIA from "../Halogen.HTML.Properties.ARIA/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // live regions
// ═══════════════════════════════════════════════════════════════════════════════
// | Live region politeness level
var Off = /* #__PURE__ */ (function () {
    function Off() {

    };
    Off.value = new Off();
    return Off;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // live regions
// ═══════════════════════════════════════════════════════════════════════════════
// | Live region politeness level
var Polite = /* #__PURE__ */ (function () {
    function Polite() {

    };
    Polite.value = new Polite();
    return Polite;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // live regions
// ═══════════════════════════════════════════════════════════════════════════════
// | Live region politeness level
var Assertive = /* #__PURE__ */ (function () {
    function Assertive() {

    };
    Assertive.value = new Assertive();
    return Assertive;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // visibility
// ═══════════════════════════════════════════════════════════════════════════════
// | Visually hide content but keep it accessible to screen readers
// |
// | Use for labels, descriptions, or additional context.
var visuallyHidden = function (children) {
    return Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "sr-only" ]) ])(children);
};

// | Timer region
// |
// | For countdown timers.
var timer = function (children) {
    return Halogen_HTML_Elements.div([ Halogen_HTML_Properties_ARIA.role("timer"), Halogen_HTML_Properties_ARIA.live("off") ])(children);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                       // semantic announcements
// ═══════════════════════════════════════════════════════════════════════════════
// | Status message (polite announcement)
// |
// | For non-critical status updates.
var status = function (children) {
    return Halogen_HTML_Elements.div([ Halogen_HTML_Properties_ARIA.role("status"), Halogen_HTML_Properties_ARIA.live("polite"), Halogen_HTML_Properties_ARIA.atomic("true") ])(children);
};

// | Tailwind sr-only class string
var srOnly = "sr-only";
var politenessValue = function (v) {
    if (v instanceof Off) {
        return "off";
    };
    if (v instanceof Polite) {
        return "polite";
    };
    if (v instanceof Assertive) {
        return "assertive";
    };
    throw new Error("Failed pattern match at Hydrogen.A11y.Announce (line 63, column 19 - line 66, column 27): " + [ v.constructor.name ]);
};

// | Marquee region (auto-updating)
// |
// | For stock tickers, news scrollers, etc.
var marquee = function (children) {
    return Halogen_HTML_Elements.div([ Halogen_HTML_Properties_ARIA.role("marquee"), Halogen_HTML_Properties_ARIA.live("off") ])(children);
};

// | Log region (polite, not atomic)
// |
// | For chat logs, activity feeds, etc.
var log = function (children) {
    return Halogen_HTML_Elements.div([ Halogen_HTML_Properties_ARIA.role("log"), Halogen_HTML_Properties_ARIA.live("polite"), Halogen_HTML_Properties_ARIA.atomic("false") ])(children);
};
var eqPoliteness = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Off && y instanceof Off) {
                return true;
            };
            if (x instanceof Polite && y instanceof Polite) {
                return true;
            };
            if (x instanceof Assertive && y instanceof Assertive) {
                return true;
            };
            return false;
        };
    }
};
var defaultProps = {
    className: ""
};

// | ARIA live region for dynamic announcements
// |
// | Content changes are announced to screen readers.
var liveRegion = function (politeness) {
    return function (propMods) {
        return function (children) {
            var props = Data_Array.foldl(function (p) {
                return function (f) {
                    return f(p);
                };
            })(defaultProps)(propMods);
            return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ props.className ]), Halogen_HTML_Properties_ARIA.live(politenessValue(politeness)), Halogen_HTML_Properties_ARIA.atomic("true") ])(children);
        };
    };
};

// | Alert message (assertive announcement)
// |
// | For important, time-sensitive information.
var alert = function (children) {
    return Halogen_HTML_Elements.div([ Halogen_HTML_Properties_ARIA.role("alert"), Halogen_HTML_Properties_ARIA.live("assertive"), Halogen_HTML_Properties_ARIA.atomic("true") ])(children);
};
export {
    liveRegion,
    Off,
    Polite,
    Assertive,
    status,
    alert,
    log,
    timer,
    marquee,
    visuallyHidden,
    srOnly,
    eqPoliteness
};
