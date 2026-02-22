// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                            // hydrogen // css
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | CSS class utilities and combinators
// |
// | This module provides utilities for building Tailwind class strings
// | in a type-safe, composable way.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Style.Css as Css
// |
// | -- Combine classes
// | Css.cx [ "flex", "items-center", "gap-4" ]  -- "flex items-center gap-4"
// |
// | -- Conditional classes
// | Css.cx [ "btn", Css.when isActive "btn-active" ]
// |
// | -- Responsive variants
// | Css.sm "hidden"   -- "sm:hidden"
// | Css.md "flex"     -- "md:flex"
// |
// | -- State variants
// | Css.hover "bg-primary"    -- "hover:bg-primary"
// | Css.focus "ring-2"        -- "focus:ring-2"
// | ```
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Either from "../Data.Either/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_String_Common from "../Data.String.Common/index.js";

// | 2XL breakpoint (1536px)
var xxl = function (cls) {
    return "2xl:" + cls;
};

// | Extra large breakpoint (1280px)
var xl = function (cls) {
    return "xl:" + cls;
};

// | Conditionally include a class
// |
// | ```purescript
// | cx [ "btn", when isActive "btn-active" ]
// | ```
var when = function (v) {
    return function (v1) {
        if (v) {
            return v1;
        };
        if (!v) {
            return "";
        };
        throw new Error("Failed pattern match at Hydrogen.Style.Css (line 113, column 1 - line 113, column 36): " + [ v.constructor.name, v1.constructor.name ]);
    };
};

// | :valid
var valid = function (cls) {
    return "valid:" + cls;
};

// | Conditionally include a class (inverse of when)
var unless = function (cond) {
    return when(!cond);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // responsive variants
// ═══════════════════════════════════════════════════════════════════════════════
// | Small breakpoint (640px)
var sm = function (cls) {
    return "sm:" + cls;
};

// | ::selection pseudo element
var selection = function (cls) {
    return "selection:" + cls;
};

// | :required
var required = function (cls) {
    return "required:" + cls;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // print
// ═══════════════════════════════════════════════════════════════════════════════
// | @media print
var print = function (cls) {
    return "print:" + cls;
};

// | ::placeholder pseudo element
var placeholder = function (cls) {
    return "placeholder:" + cls;
};

// | When sibling with .peer is hovered
var peerHover = function (cls) {
    return "peer-hover:" + cls;
};

// | When sibling with .peer is focused
var peerFocus = function (cls) {
    return "peer-focus:" + cls;
};

// | :nth-child(odd)
var odd = function (cls) {
    return "odd:" + cls;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // reduced motion
// ═══════════════════════════════════════════════════════════════════════════════
// | @media (prefers-reduced-motion: no-preference)
var motionSafe = function (cls) {
    return "motion-safe:" + cls;
};

// | @media (prefers-reduced-motion: reduce)
var motionReduce = function (cls) {
    return "motion-reduce:" + cls;
};

// | Medium breakpoint (768px)
var md = function (cls) {
    return "md:" + cls;
};

// | Include a class based on Maybe
// |
// | ```purescript
// | cx [ "base", maybe "" identity maybeClass ]
// | ```
var maybe = function ($$default) {
    return function (f) {
        return Data_Maybe.maybe($$default)(f);
    };
};

// | Large breakpoint (1024px)
var lg = function (cls) {
    return "lg:" + cls;
};

// | :last-child
var last = function (cls) {
    return "last:" + cls;
};

// | :invalid
var invalid = function (cls) {
    return "invalid:" + cls;
};

// | :indeterminate
var indeterminate = function (cls) {
    return "indeterminate:" + cls;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // state variants
// ═══════════════════════════════════════════════════════════════════════════════
// | Hover state
var hover = function (cls) {
    return "hover:" + cls;
};

// | When parent with .group is hovered
var groupHover = function (cls) {
    return "group-hover:" + cls;
};

// | When parent with .group is focused
var groupFocus = function (cls) {
    return "group-focus:" + cls;
};

// | Focus within (child focused)
var focusWithin = function (cls) {
    return "focus-within:" + cls;
};

// | Focus visible (keyboard focus)
var focusVisible = function (cls) {
    return "focus-visible:" + cls;
};

// | Focus state
var focus = function (cls) {
    return "focus:" + cls;
};

// | ::first-line pseudo element
var firstLine = function (cls) {
    return "first-line:" + cls;
};

// | ::first-letter pseudo element
var firstLetter = function (cls) {
    return "first-letter:" + cls;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // pseudo classes
// ═══════════════════════════════════════════════════════════════════════════════
// | :first-child
var first = function (cls) {
    return "first:" + cls;
};

// | :nth-child(even)
var even = function (cls) {
    return "even:" + cls;
};

// | :empty
var empty = function (cls) {
    return "empty:" + cls;
};

// | Include a class based on Either
var either = function (v) {
    return function (v1) {
        return function (v2) {
            if (v2 instanceof Data_Either.Left) {
                return v(v2.value0);
            };
            if (v2 instanceof Data_Either.Right) {
                return v1(v2.value0);
            };
            throw new Error("Failed pattern match at Hydrogen.Style.Css (line 130, column 1 - line 130, column 77): " + [ v.constructor.name, v1.constructor.name, v2.constructor.name ]);
        };
    };
};

// | Disabled state
var disabled = function (cls) {
    return "disabled:" + cls;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // class combinators
// ═══════════════════════════════════════════════════════════════════════════════
// | Combine multiple class strings, filtering empty ones
// |
// | ```purescript
// | cx [ "flex", "items-center", "", "gap-4" ]
// | -- "flex items-center gap-4"
// | ```
var cx = /* #__PURE__ */ (function () {
    var $15 = Data_String_Common.joinWith(" ");
    var $16 = Data_Array.filter(function ($18) {
        return !Data_String_Common["null"]($18);
    });
    return function ($17) {
        return $15($16($17));
    };
})();

// | Alias for cx
var classes = cx;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // form states
// ═══════════════════════════════════════════════════════════════════════════════
// | :checked
var checked = function (cls) {
    return "checked:" + cls;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                             // pseudo elements
// ═══════════════════════════════════════════════════════════════════════════════
// | ::before pseudo element
var before = function (cls) {
    return "before:" + cls;
};

// | Arbitrary property (for uncommon CSS)
// |
// | ```purescript
// | arbitraryProperty "clip-path" "polygon(...)"
// | -- "[clip-path:polygon(...)]"
// | ```
var arbitraryProperty = function (property) {
    return function (value) {
        return "[" + (property + (":" + (value + "]")));
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // arbitrary values
// ═══════════════════════════════════════════════════════════════════════════════
// | Arbitrary value
// |
// | ```purescript
// | arbitrary "w" "137px"  -- "w-[137px]"
// | ```
var arbitrary = function (property) {
    return function (value) {
        return property + ("-[" + (value + "]"));
    };
};

// | ::after pseudo element
var after = function (cls) {
    return "after:" + cls;
};

// | Active (pressed) state
var active = function (cls) {
    return "active:" + cls;
};
export {
    cx,
    classes,
    when,
    unless,
    maybe,
    either,
    sm,
    md,
    lg,
    xl,
    xxl,
    hover,
    focus,
    active,
    disabled,
    focusVisible,
    focusWithin,
    groupHover,
    groupFocus,
    peerHover,
    peerFocus,
    before,
    after,
    placeholder,
    selection,
    firstLetter,
    firstLine,
    first,
    last,
    odd,
    even,
    empty,
    checked,
    indeterminate,
    required,
    invalid,
    valid,
    motionSafe,
    motionReduce,
    print,
    arbitrary,
    arbitraryProperty
};
