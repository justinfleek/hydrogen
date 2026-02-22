// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                      // hydrogen // schema // color // contrast
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Color contrast and accessibility.
// |
// | WCAG (Web Content Accessibility Guidelines) contrast requirements:
// | - **AA Large**: 3:1 minimum for large text (18pt+ or 14pt bold)
// | - **AA**: 4.5:1 minimum for normal text
// | - **AAA**: 7:1 minimum for enhanced accessibility
// |
// | This module provides accurate contrast calculation per WCAG 2.1 spec.
import * as Data_Int from "../Data.Int/index.js";
import * as Data_Ordering from "../Data.Ordering/index.js";
import * as Hydrogen_Math_Core from "../Hydrogen.Math.Core/index.js";
import * as Hydrogen_Schema_Color_Channel from "../Hydrogen.Schema.Color.Channel/index.js";
import * as Hydrogen_Schema_Color_RGB from "../Hydrogen.Schema.Color.RGB/index.js";

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // wcag levels
// ═══════════════════════════════════════════════════════════════════════════════
// | WCAG contrast levels
var WCAGFail = /* #__PURE__ */ (function () {
    function WCAGFail() {

    };
    WCAGFail.value = new WCAGFail();
    return WCAGFail;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // wcag levels
// ═══════════════════════════════════════════════════════════════════════════════
// | WCAG contrast levels
var WCAGAA_Large = /* #__PURE__ */ (function () {
    function WCAGAA_Large() {

    };
    WCAGAA_Large.value = new WCAGAA_Large();
    return WCAGAA_Large;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // wcag levels
// ═══════════════════════════════════════════════════════════════════════════════
// | WCAG contrast levels
var WCAGAA = /* #__PURE__ */ (function () {
    function WCAGAA() {

    };
    WCAGAA.value = new WCAGAA();
    return WCAGAA;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // wcag levels
// ═══════════════════════════════════════════════════════════════════════════════
// | WCAG contrast levels
var WCAGAAA_Large = /* #__PURE__ */ (function () {
    function WCAGAAA_Large() {

    };
    WCAGAAA_Large.value = new WCAGAAA_Large();
    return WCAGAAA_Large;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // wcag levels
// ═══════════════════════════════════════════════════════════════════════════════
// | WCAG contrast levels
var WCAGAAA = /* #__PURE__ */ (function () {
    function WCAGAAA() {

    };
    WCAGAAA.value = new WCAGAAA();
    return WCAGAAA;
})();
var showWCAGLevel = {
    show: function (v) {
        if (v instanceof WCAGFail) {
            return "Fail";
        };
        if (v instanceof WCAGAA_Large) {
            return "AA (Large Text)";
        };
        if (v instanceof WCAGAA) {
            return "AA";
        };
        if (v instanceof WCAGAAA_Large) {
            return "AAA (Large Text)";
        };
        if (v instanceof WCAGAAA) {
            return "AAA";
        };
        throw new Error("Failed pattern match at Hydrogen.Schema.Color.Contrast (line 55, column 10 - line 60, column 21): " + [ v.constructor.name ]);
    }
};

// | Minimum contrast ratios for each level
var minContrastFor = function (v) {
    if (v instanceof WCAGFail) {
        return 1.0;
    };
    if (v instanceof WCAGAA_Large) {
        return 3.0;
    };
    if (v instanceof WCAGAA) {
        return 4.5;
    };
    if (v instanceof WCAGAAA_Large) {
        return 4.5;
    };
    if (v instanceof WCAGAAA) {
        return 7.0;
    };
    throw new Error("Failed pattern match at Hydrogen.Schema.Color.Contrast (line 64, column 18 - line 69, column 17): " + [ v.constructor.name ]);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // luminance
// ═══════════════════════════════════════════════════════════════════════════════
// | Relative luminance per WCAG 2.1 specification
// |
// | Returns a value between 0 (darkest black) and 1 (lightest white)
var luminanceRGB = function (color) {
    var toLinear = function (c) {
        var c$prime = Data_Int.toNumber(c) / 255.0;
        var $14 = c$prime <= 3.928e-2;
        if ($14) {
            return c$prime / 12.92;
        };
        return Hydrogen_Math_Core.pow((c$prime + 5.5e-2) / 1.055)(2.4);
    };
    var r = Hydrogen_Schema_Color_Channel.unwrap(Hydrogen_Schema_Color_RGB.red(color));
    var g = Hydrogen_Schema_Color_Channel.unwrap(Hydrogen_Schema_Color_RGB.green(color));
    var b = Hydrogen_Schema_Color_Channel.unwrap(Hydrogen_Schema_Color_RGB.blue(color));
    return 0.2126 * toLinear(r) + 0.7152 * toLinear(g) + 7.22e-2 * toLinear(b);
};

// | Alias for luminanceRGB (WCAG terminology)
var relativeLuminance = luminanceRGB;

// | Suggest black or white foreground for best contrast
var suggestForeground = function (background) {
    var l = luminanceRGB(background);
    var $15 = l > 0.179;
    if ($15) {
        return Hydrogen_Schema_Color_RGB.rgb(0)(0)(0);
    };
    return Hydrogen_Schema_Color_RGB.rgb(255)(255)(255);
};
var eqWCAGLevel = {
    eq: function (x) {
        return function (y) {
            if (x instanceof WCAGFail && y instanceof WCAGFail) {
                return true;
            };
            if (x instanceof WCAGAA_Large && y instanceof WCAGAA_Large) {
                return true;
            };
            if (x instanceof WCAGAA && y instanceof WCAGAA) {
                return true;
            };
            if (x instanceof WCAGAAA_Large && y instanceof WCAGAAA_Large) {
                return true;
            };
            if (x instanceof WCAGAAA && y instanceof WCAGAAA) {
                return true;
            };
            return false;
        };
    }
};
var ordWCAGLevel = {
    compare: function (x) {
        return function (y) {
            if (x instanceof WCAGFail && y instanceof WCAGFail) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof WCAGFail) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof WCAGFail) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof WCAGAA_Large && y instanceof WCAGAA_Large) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof WCAGAA_Large) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof WCAGAA_Large) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof WCAGAA && y instanceof WCAGAA) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof WCAGAA) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof WCAGAA) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof WCAGAAA_Large && y instanceof WCAGAAA_Large) {
                return Data_Ordering.EQ.value;
            };
            if (x instanceof WCAGAAA_Large) {
                return Data_Ordering.LT.value;
            };
            if (y instanceof WCAGAAA_Large) {
                return Data_Ordering.GT.value;
            };
            if (x instanceof WCAGAAA && y instanceof WCAGAAA) {
                return Data_Ordering.EQ.value;
            };
            throw new Error("Failed pattern match at Hydrogen.Schema.Color.Contrast (line 0, column 0 - line 0, column 0): " + [ x.constructor.name, y.constructor.name ]);
        };
    },
    Eq0: function () {
        return eqWCAGLevel;
    }
};

// | Calculate WCAG contrast ratio between two colors
// |
// | Returns a value between 1:1 (identical) and 21:1 (black/white)
var contrastRatio = function (c1) {
    return function (c2) {
        var l2 = luminanceRGB(c2);
        var l1 = luminanceRGB(c1);
        var lighter = Hydrogen_Math_Core.max(l1)(l2);
        var darker = Hydrogen_Math_Core.min(l1)(l2);
        return (lighter + 5.0e-2) / (darker + 5.0e-2);
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                        // accessibility checks
// ═══════════════════════════════════════════════════════════════════════════════
// | Check if contrast meets a WCAG level
var meetsWCAG = function (level) {
    return function (c1) {
        return function (c2) {
            return contrastRatio(c1)(c2) >= minContrastFor(level);
        };
    };
};

// | Get full contrast information between two colors
var contrastBetween = function (c1) {
    return function (c2) {
        var ratio = contrastRatio(c1)(c2);
        var level = (function () {
            var $20 = ratio >= 7.0;
            if ($20) {
                return WCAGAAA.value;
            };
            var $21 = ratio >= 4.5;
            if ($21) {
                return WCAGAA.value;
            };
            var $22 = ratio >= 3.0;
            if ($22) {
                return WCAGAA_Large.value;
            };
            return WCAGFail.value;
        })();
        return {
            ratio: ratio,
            level: level
        };
    };
};
export {
    WCAGFail,
    WCAGAA_Large,
    WCAGAA,
    WCAGAAA_Large,
    WCAGAAA,
    contrastRatio,
    contrastBetween,
    meetsWCAG,
    suggestForeground,
    luminanceRGB,
    relativeLuminance,
    eqWCAGLevel,
    ordWCAGLevel,
    showWCAGLevel
};
