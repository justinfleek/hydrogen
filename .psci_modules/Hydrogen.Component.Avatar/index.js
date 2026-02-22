// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                         // hydrogen // avatar
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Avatar component
// |
// | User avatar with image and fallback support.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Component.Avatar as Avatar
// |
// | -- With image
// | Avatar.avatar [ Avatar.size Avatar.Md ]
// |   [ Avatar.avatarImage [ Avatar.src "/user.jpg", Avatar.alt "User" ]
// |   , Avatar.avatarFallback [] [ HH.text "JD" ]
// |   ]
// |
// | -- Fallback only
// | Avatar.avatar []
// |   [ Avatar.avatarFallback [] [ HH.text "AB" ] ]
// | ```
import * as Data_Array from "../Data.Array/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Halogen_HTML_Properties from "../Halogen.HTML.Properties/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // sizes
// ═══════════════════════════════════════════════════════════════════════════════
// | Avatar sizes
var Xs = /* #__PURE__ */ (function () {
    function Xs() {

    };
    Xs.value = new Xs();
    return Xs;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // sizes
// ═══════════════════════════════════════════════════════════════════════════════
// | Avatar sizes
var Sm = /* #__PURE__ */ (function () {
    function Sm() {

    };
    Sm.value = new Sm();
    return Sm;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // sizes
// ═══════════════════════════════════════════════════════════════════════════════
// | Avatar sizes
var Md = /* #__PURE__ */ (function () {
    function Md() {

    };
    Md.value = new Md();
    return Md;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // sizes
// ═══════════════════════════════════════════════════════════════════════════════
// | Avatar sizes
var Lg = /* #__PURE__ */ (function () {
    function Lg() {

    };
    Lg.value = new Lg();
    return Lg;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // sizes
// ═══════════════════════════════════════════════════════════════════════════════
// | Avatar sizes
var Xl = /* #__PURE__ */ (function () {
    function Xl() {

    };
    Xl.value = new Xl();
    return Xl;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // sizes
// ═══════════════════════════════════════════════════════════════════════════════
// | Avatar sizes
var Xxl = /* #__PURE__ */ (function () {
    function Xxl() {

    };
    Xxl.value = new Xxl();
    return Xxl;
})();

// | Set image source
var src = function (s) {
    return function (props) {
        return {
            alt: props.alt,
            className: props.className,
            src: s
        };
    };
};
var sizeClasses = function (v) {
    if (v instanceof Xs) {
        return "h-6 w-6";
    };
    if (v instanceof Sm) {
        return "h-8 w-8";
    };
    if (v instanceof Md) {
        return "h-10 w-10";
    };
    if (v instanceof Lg) {
        return "h-12 w-12";
    };
    if (v instanceof Xl) {
        return "h-16 w-16";
    };
    if (v instanceof Xxl) {
        return "h-24 w-24";
    };
    throw new Error("Failed pattern match at Hydrogen.Component.Avatar (line 65, column 15 - line 71, column 21): " + [ v.constructor.name ]);
};

// | Set avatar size
var size = function (s) {
    return function (props) {
        return {
            className: props.className,
            size: s
        };
    };
};
var eqAvatarSize = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Xs && y instanceof Xs) {
                return true;
            };
            if (x instanceof Sm && y instanceof Sm) {
                return true;
            };
            if (x instanceof Md && y instanceof Md) {
                return true;
            };
            if (x instanceof Lg && y instanceof Lg) {
                return true;
            };
            if (x instanceof Xl && y instanceof Xl) {
                return true;
            };
            if (x instanceof Xxl && y instanceof Xxl) {
                return true;
            };
            return false;
        };
    }
};
var defaultImageProps = {
    src: "",
    alt: "",
    className: ""
};
var defaultAvatarProps = /* #__PURE__ */ (function () {
    return {
        size: Md.value,
        className: ""
    };
})();

// | Add custom class
var className = function (c) {
    return function (props) {
        return {
            size: props.size,
            className: props.className + (" " + c)
        };
    };
};

// | Avatar image
var avatarImage = function (propMods) {
    var props = Data_Array.foldl(function (p) {
        return function (f) {
            return f(p);
        };
    })(defaultImageProps)(propMods);
    return Halogen_HTML_Elements.img([ Hydrogen_UI_Core.cls([ "aspect-square h-full w-full", props.className ]), Halogen_HTML_Properties.src(props.src), Halogen_HTML_Properties.alt(props.alt) ]);
};

// | Avatar fallback (shown when image fails or isn't provided)
var avatarFallback = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultAvatarProps)(propMods);
        return Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "flex h-full w-full items-center justify-center rounded-full bg-muted text-muted-foreground", props.className ]) ])(children);
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // components
// ═══════════════════════════════════════════════════════════════════════════════
// | Avatar container
var avatar = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultAvatarProps)(propMods);
        return Halogen_HTML_Elements.span([ Hydrogen_UI_Core.cls([ "relative flex shrink-0 overflow-hidden rounded-full", sizeClasses(props.size), props.className ]) ])(children);
    };
};

// | Set image alt text
var alt = function (a) {
    return function (props) {
        return {
            src: props.src,
            className: props.className,
            alt: a
        };
    };
};
export {
    avatar,
    avatarImage,
    avatarFallback,
    size,
    className,
    src,
    alt,
    Xs,
    Sm,
    Md,
    Lg,
    Xl,
    Xxl,
    eqAvatarSize
};
