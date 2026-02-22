// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                       // hydrogen // schema // color // palette
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Color palette generation and semantic roles.
// |
// | Tools for building systematic color palettes:
// | - **Tints**: Lighter variations (add white)
// | - **Shades**: Darker variations (add black)
// | - **Tones**: Less saturated variations (add gray)
// | - **Roles**: Semantic meaning in a design system
import * as Data_Array from "../Data.Array/index.js";
import * as Data_EuclideanRing from "../Data.EuclideanRing/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Data_Int from "../Data.Int/index.js";
import * as Data_Semigroup from "../Data.Semigroup/index.js";
import * as Hydrogen_Schema_Color_HSL from "../Hydrogen.Schema.Color.HSL/index.js";
import * as Hydrogen_Schema_Color_Hue from "../Hydrogen.Schema.Color.Hue/index.js";
import * as Hydrogen_Schema_Color_Lightness from "../Hydrogen.Schema.Color.Lightness/index.js";
import * as Hydrogen_Schema_Color_Saturation from "../Hydrogen.Schema.Color.Saturation/index.js";
var map = /* #__PURE__ */ Data_Functor.map(Data_Functor.functorArray);
var append = /* #__PURE__ */ Data_Semigroup.append(Data_Semigroup.semigroupArray);
var div1 = /* #__PURE__ */ Data_EuclideanRing.div(Data_EuclideanRing.euclideanRingInt);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // semantic roles
// ═══════════════════════════════════════════════════════════════════════════════
// | Semantic role of a color in a design system
var Primary = /* #__PURE__ */ (function () {
    function Primary() {

    };
    Primary.value = new Primary();
    return Primary;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // semantic roles
// ═══════════════════════════════════════════════════════════════════════════════
// | Semantic role of a color in a design system
var Secondary = /* #__PURE__ */ (function () {
    function Secondary() {

    };
    Secondary.value = new Secondary();
    return Secondary;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // semantic roles
// ═══════════════════════════════════════════════════════════════════════════════
// | Semantic role of a color in a design system
var Accent = /* #__PURE__ */ (function () {
    function Accent() {

    };
    Accent.value = new Accent();
    return Accent;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // semantic roles
// ═══════════════════════════════════════════════════════════════════════════════
// | Semantic role of a color in a design system
var Background = /* #__PURE__ */ (function () {
    function Background() {

    };
    Background.value = new Background();
    return Background;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // semantic roles
// ═══════════════════════════════════════════════════════════════════════════════
// | Semantic role of a color in a design system
var Surface = /* #__PURE__ */ (function () {
    function Surface() {

    };
    Surface.value = new Surface();
    return Surface;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // semantic roles
// ═══════════════════════════════════════════════════════════════════════════════
// | Semantic role of a color in a design system
var OnPrimary = /* #__PURE__ */ (function () {
    function OnPrimary() {

    };
    OnPrimary.value = new OnPrimary();
    return OnPrimary;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // semantic roles
// ═══════════════════════════════════════════════════════════════════════════════
// | Semantic role of a color in a design system
var OnSecondary = /* #__PURE__ */ (function () {
    function OnSecondary() {

    };
    OnSecondary.value = new OnSecondary();
    return OnSecondary;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // semantic roles
// ═══════════════════════════════════════════════════════════════════════════════
// | Semantic role of a color in a design system
var OnBackground = /* #__PURE__ */ (function () {
    function OnBackground() {

    };
    OnBackground.value = new OnBackground();
    return OnBackground;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // semantic roles
// ═══════════════════════════════════════════════════════════════════════════════
// | Semantic role of a color in a design system
var OnSurface = /* #__PURE__ */ (function () {
    function OnSurface() {

    };
    OnSurface.value = new OnSurface();
    return OnSurface;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // semantic roles
// ═══════════════════════════════════════════════════════════════════════════════
// | Semantic role of a color in a design system
var Neutral = /* #__PURE__ */ (function () {
    function Neutral() {

    };
    Neutral.value = new Neutral();
    return Neutral;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // semantic roles
// ═══════════════════════════════════════════════════════════════════════════════
// | Semantic role of a color in a design system
var Success = /* #__PURE__ */ (function () {
    function Success() {

    };
    Success.value = new Success();
    return Success;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // semantic roles
// ═══════════════════════════════════════════════════════════════════════════════
// | Semantic role of a color in a design system
var Warning = /* #__PURE__ */ (function () {
    function Warning() {

    };
    Warning.value = new Warning();
    return Warning;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // semantic roles
// ═══════════════════════════════════════════════════════════════════════════════
// | Semantic role of a color in a design system
var $$Error = /* #__PURE__ */ (function () {
    function $$Error() {

    };
    $$Error.value = new $$Error();
    return $$Error;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // semantic roles
// ═══════════════════════════════════════════════════════════════════════════════
// | Semantic role of a color in a design system
var Info = /* #__PURE__ */ (function () {
    function Info() {

    };
    Info.value = new Info();
    return Info;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // semantic roles
// ═══════════════════════════════════════════════════════════════════════════════
// | Semantic role of a color in a design system
var Unassigned = /* #__PURE__ */ (function () {
    function Unassigned() {

    };
    Unassigned.value = new Unassigned();
    return Unassigned;
})();

// | Generate tones (less saturated versions) of a color
// |
// | Adds gray to create progressively more muted variations.
var tones = function (count) {
    return function (color) {
        var s = Hydrogen_Schema_Color_Saturation.unwrap(Hydrogen_Schema_Color_HSL.saturation(color));
        var step = Data_Int.toNumber(s) / Data_Int.toNumber(count + 1 | 0);
        var l = Hydrogen_Schema_Color_Lightness.unwrap(Hydrogen_Schema_Color_HSL.lightness(color));
        var h = Hydrogen_Schema_Color_Hue.unwrap(Hydrogen_Schema_Color_HSL.hue(color));
        var makeColor = function (i) {
            return Hydrogen_Schema_Color_HSL.hsl(h)(s - Data_Int.round(step * Data_Int.toNumber(i)) | 0)(l);
        };
        return map(makeColor)(Data_Array.range(1)(count));
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                           // palette generation
// ═══════════════════════════════════════════════════════════════════════════════
// | Generate tints (lighter versions) of a color
// |
// | Adds white to create progressively lighter variations.
var tints = function (count) {
    return function (color) {
        var s = Hydrogen_Schema_Color_Saturation.unwrap(Hydrogen_Schema_Color_HSL.saturation(color));
        var l = Hydrogen_Schema_Color_Lightness.unwrap(Hydrogen_Schema_Color_HSL.lightness(color));
        var step = Data_Int.toNumber(100 - l | 0) / Data_Int.toNumber(count + 1 | 0);
        var h = Hydrogen_Schema_Color_Hue.unwrap(Hydrogen_Schema_Color_HSL.hue(color));
        var makeColor = function (i) {
            return Hydrogen_Schema_Color_HSL.hsl(h)(s)(l + Data_Int.round(step * Data_Int.toNumber(i)) | 0);
        };
        return map(makeColor)(Data_Array.range(1)(count));
    };
};
var showRole = {
    show: function (v) {
        if (v instanceof Primary) {
            return "primary";
        };
        if (v instanceof Secondary) {
            return "secondary";
        };
        if (v instanceof Accent) {
            return "accent";
        };
        if (v instanceof Background) {
            return "background";
        };
        if (v instanceof Surface) {
            return "surface";
        };
        if (v instanceof OnPrimary) {
            return "on-primary";
        };
        if (v instanceof OnSecondary) {
            return "on-secondary";
        };
        if (v instanceof OnBackground) {
            return "on-background";
        };
        if (v instanceof OnSurface) {
            return "on-surface";
        };
        if (v instanceof Neutral) {
            return "neutral";
        };
        if (v instanceof Success) {
            return "success";
        };
        if (v instanceof Warning) {
            return "warning";
        };
        if (v instanceof $$Error) {
            return "error";
        };
        if (v instanceof Info) {
            return "info";
        };
        if (v instanceof Unassigned) {
            return "unassigned";
        };
        throw new Error("Failed pattern match at Hydrogen.Schema.Color.Palette (line 80, column 10 - line 95, column 31): " + [ v.constructor.name ]);
    }
};

// | Generate shades (darker versions) of a color
// |
// | Adds black to create progressively darker variations.
var shades = function (count) {
    return function (color) {
        var s = Hydrogen_Schema_Color_Saturation.unwrap(Hydrogen_Schema_Color_HSL.saturation(color));
        var l = Hydrogen_Schema_Color_Lightness.unwrap(Hydrogen_Schema_Color_HSL.lightness(color));
        var step = Data_Int.toNumber(l) / Data_Int.toNumber(count + 1 | 0);
        var h = Hydrogen_Schema_Color_Hue.unwrap(Hydrogen_Schema_Color_HSL.hue(color));
        var makeColor = function (i) {
            return Hydrogen_Schema_Color_HSL.hsl(h)(s)(l - Data_Int.round(step * Data_Int.toNumber(i)) | 0);
        };
        return map(makeColor)(Data_Array.range(1)(count));
    };
};

// | Generate a monochromatic palette
// |
// | Combines tints and shades for a full value range.
var monochromatic = function (count) {
    return function (color) {
        return append(tints(div1(count)(2))(color))(shades(div1(count)(2))(color));
    };
};

// | Create palette from colors (all unassigned)
var fromColors = /* #__PURE__ */ map(function (color) {
    return {
        color: color,
        role: Unassigned.value
    };
});
var eqRole = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Primary && y instanceof Primary) {
                return true;
            };
            if (x instanceof Secondary && y instanceof Secondary) {
                return true;
            };
            if (x instanceof Accent && y instanceof Accent) {
                return true;
            };
            if (x instanceof Background && y instanceof Background) {
                return true;
            };
            if (x instanceof Surface && y instanceof Surface) {
                return true;
            };
            if (x instanceof OnPrimary && y instanceof OnPrimary) {
                return true;
            };
            if (x instanceof OnSecondary && y instanceof OnSecondary) {
                return true;
            };
            if (x instanceof OnBackground && y instanceof OnBackground) {
                return true;
            };
            if (x instanceof OnSurface && y instanceof OnSurface) {
                return true;
            };
            if (x instanceof Neutral && y instanceof Neutral) {
                return true;
            };
            if (x instanceof Success && y instanceof Success) {
                return true;
            };
            if (x instanceof Warning && y instanceof Warning) {
                return true;
            };
            if (x instanceof $$Error && y instanceof $$Error) {
                return true;
            };
            if (x instanceof Info && y instanceof Info) {
                return true;
            };
            if (x instanceof Unassigned && y instanceof Unassigned) {
                return true;
            };
            return false;
        };
    }
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                         // palette construction
// ═══════════════════════════════════════════════════════════════════════════════
// | Empty palette
var emptyPalette = [  ];

// | Add a color with role to palette
var addColor = function (role) {
    return function (color) {
        return function (palette) {
            return Data_Array.cons({
                color: color,
                role: role
            })(palette);
        };
    };
};
export {
    Primary,
    Secondary,
    Accent,
    Background,
    Surface,
    OnPrimary,
    OnSecondary,
    OnBackground,
    OnSurface,
    Neutral,
    Success,
    Warning,
    $$Error as Error,
    Info,
    Unassigned,
    tints,
    shades,
    tones,
    monochromatic,
    emptyPalette,
    addColor,
    fromColors,
    eqRole,
    showRole
};
