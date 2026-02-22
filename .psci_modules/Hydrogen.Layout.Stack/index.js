// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                          // hydrogen // stack
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Stack layout components
// |
// | Elm-UI inspired layout primitives for flexbox layouts.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Layout.Stack as Stack
// |
// | -- Vertical stack with gap
// | Stack.vstack [ Stack.gap Stack.G4 ]
// |   [ child1, child2, child3 ]
// |
// | -- Horizontal stack centered
// | Stack.hstack [ Stack.gap Stack.G2, Stack.align Stack.Center ]
// |   [ left, center, right ]
// |
// | -- Centered content
// | Stack.center []
// |   [ content ]
// | ```
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Halogen_HTML_Elements from "../Halogen.HTML.Elements/index.js";
import * as Hydrogen_UI_Core from "../Hydrogen.UI.Core/index.js";
var map = /* #__PURE__ */ Data_Functor.map(Data_Functor.functorArray);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // justification
// ═══════════════════════════════════════════════════════════════════════════════
// | Justification (main-axis)
var JustifyStart = /* #__PURE__ */ (function () {
    function JustifyStart() {

    };
    JustifyStart.value = new JustifyStart();
    return JustifyStart;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // justification
// ═══════════════════════════════════════════════════════════════════════════════
// | Justification (main-axis)
var JustifyCenter = /* #__PURE__ */ (function () {
    function JustifyCenter() {

    };
    JustifyCenter.value = new JustifyCenter();
    return JustifyCenter;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // justification
// ═══════════════════════════════════════════════════════════════════════════════
// | Justification (main-axis)
var JustifyEnd = /* #__PURE__ */ (function () {
    function JustifyEnd() {

    };
    JustifyEnd.value = new JustifyEnd();
    return JustifyEnd;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // justification
// ═══════════════════════════════════════════════════════════════════════════════
// | Justification (main-axis)
var JustifyBetween = /* #__PURE__ */ (function () {
    function JustifyBetween() {

    };
    JustifyBetween.value = new JustifyBetween();
    return JustifyBetween;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // justification
// ═══════════════════════════════════════════════════════════════════════════════
// | Justification (main-axis)
var JustifyAround = /* #__PURE__ */ (function () {
    function JustifyAround() {

    };
    JustifyAround.value = new JustifyAround();
    return JustifyAround;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // justification
// ═══════════════════════════════════════════════════════════════════════════════
// | Justification (main-axis)
var JustifyEvenly = /* #__PURE__ */ (function () {
    function JustifyEvenly() {

    };
    JustifyEvenly.value = new JustifyEvenly();
    return JustifyEvenly;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                         // gap
// ═══════════════════════════════════════════════════════════════════════════════
// | Gap sizes
var G0 = /* #__PURE__ */ (function () {
    function G0() {

    };
    G0.value = new G0();
    return G0;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                         // gap
// ═══════════════════════════════════════════════════════════════════════════════
// | Gap sizes
var G1 = /* #__PURE__ */ (function () {
    function G1() {

    };
    G1.value = new G1();
    return G1;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                         // gap
// ═══════════════════════════════════════════════════════════════════════════════
// | Gap sizes
var G2 = /* #__PURE__ */ (function () {
    function G2() {

    };
    G2.value = new G2();
    return G2;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                         // gap
// ═══════════════════════════════════════════════════════════════════════════════
// | Gap sizes
var G3 = /* #__PURE__ */ (function () {
    function G3() {

    };
    G3.value = new G3();
    return G3;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                         // gap
// ═══════════════════════════════════════════════════════════════════════════════
// | Gap sizes
var G4 = /* #__PURE__ */ (function () {
    function G4() {

    };
    G4.value = new G4();
    return G4;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                         // gap
// ═══════════════════════════════════════════════════════════════════════════════
// | Gap sizes
var G5 = /* #__PURE__ */ (function () {
    function G5() {

    };
    G5.value = new G5();
    return G5;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                         // gap
// ═══════════════════════════════════════════════════════════════════════════════
// | Gap sizes
var G6 = /* #__PURE__ */ (function () {
    function G6() {

    };
    G6.value = new G6();
    return G6;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                         // gap
// ═══════════════════════════════════════════════════════════════════════════════
// | Gap sizes
var G8 = /* #__PURE__ */ (function () {
    function G8() {

    };
    G8.value = new G8();
    return G8;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                         // gap
// ═══════════════════════════════════════════════════════════════════════════════
// | Gap sizes
var G10 = /* #__PURE__ */ (function () {
    function G10() {

    };
    G10.value = new G10();
    return G10;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                         // gap
// ═══════════════════════════════════════════════════════════════════════════════
// | Gap sizes
var G12 = /* #__PURE__ */ (function () {
    function G12() {

    };
    G12.value = new G12();
    return G12;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                         // gap
// ═══════════════════════════════════════════════════════════════════════════════
// | Gap sizes
var G16 = /* #__PURE__ */ (function () {
    function G16() {

    };
    G16.value = new G16();
    return G16;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // alignment
// ═══════════════════════════════════════════════════════════════════════════════
// | Alignment (cross-axis)
var Start = /* #__PURE__ */ (function () {
    function Start() {

    };
    Start.value = new Start();
    return Start;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // alignment
// ═══════════════════════════════════════════════════════════════════════════════
// | Alignment (cross-axis)
var Center = /* #__PURE__ */ (function () {
    function Center() {

    };
    Center.value = new Center();
    return Center;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // alignment
// ═══════════════════════════════════════════════════════════════════════════════
// | Alignment (cross-axis)
var End = /* #__PURE__ */ (function () {
    function End() {

    };
    End.value = new End();
    return End;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // alignment
// ═══════════════════════════════════════════════════════════════════════════════
// | Alignment (cross-axis)
var Stretch = /* #__PURE__ */ (function () {
    function Stretch() {

    };
    Stretch.value = new Stretch();
    return Stretch;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // alignment
// ═══════════════════════════════════════════════════════════════════════════════
// | Alignment (cross-axis)
var Baseline = /* #__PURE__ */ (function () {
    function Baseline() {

    };
    Baseline.value = new Baseline();
    return Baseline;
})();

// | Enable wrapping
var wrap = function (w) {
    return function (props) {
        return {
            gap: props.gap,
            align: props.align,
            justify: props.justify,
            reverse: props.reverse,
            className: props.className,
            wrap: w
        };
    };
};

// | Flexible spacer (pushes content apart)
var spacer = /* #__PURE__ */ Halogen_HTML_Elements.div([ /* #__PURE__ */ Hydrogen_UI_Core.cls([ "flex-1" ]) ])([  ]);

// | Reverse order
var reverse = function (r) {
    return function (props) {
        return {
            gap: props.gap,
            align: props.align,
            justify: props.justify,
            wrap: props.wrap,
            className: props.className,
            reverse: r
        };
    };
};
var justifyClass = function (v) {
    if (v instanceof JustifyStart) {
        return "justify-start";
    };
    if (v instanceof JustifyCenter) {
        return "justify-center";
    };
    if (v instanceof JustifyEnd) {
        return "justify-end";
    };
    if (v instanceof JustifyBetween) {
        return "justify-between";
    };
    if (v instanceof JustifyAround) {
        return "justify-around";
    };
    if (v instanceof JustifyEvenly) {
        return "justify-evenly";
    };
    throw new Error("Failed pattern match at Hydrogen.Layout.Stack (line 128, column 16 - line 134, column 36): " + [ v.constructor.name ]);
};

// | Set justification
var justify = function (j) {
    return function (props) {
        return {
            gap: props.gap,
            align: props.align,
            wrap: props.wrap,
            reverse: props.reverse,
            className: props.className,
            justify: j
        };
    };
};
var gapClass = function (v) {
    if (v instanceof G0) {
        return "gap-0";
    };
    if (v instanceof G1) {
        return "gap-1";
    };
    if (v instanceof G2) {
        return "gap-2";
    };
    if (v instanceof G3) {
        return "gap-3";
    };
    if (v instanceof G4) {
        return "gap-4";
    };
    if (v instanceof G5) {
        return "gap-5";
    };
    if (v instanceof G6) {
        return "gap-6";
    };
    if (v instanceof G8) {
        return "gap-8";
    };
    if (v instanceof G10) {
        return "gap-10";
    };
    if (v instanceof G12) {
        return "gap-12";
    };
    if (v instanceof G16) {
        return "gap-16";
    };
    throw new Error("Failed pattern match at Hydrogen.Layout.Stack (line 77, column 12 - line 88, column 18): " + [ v.constructor.name ]);
};

// | Set gap
var gap = function (g) {
    return function (props) {
        return {
            align: props.align,
            justify: props.justify,
            wrap: props.wrap,
            reverse: props.reverse,
            className: props.className,
            gap: g
        };
    };
};
var eqJustification = {
    eq: function (x) {
        return function (y) {
            if (x instanceof JustifyStart && y instanceof JustifyStart) {
                return true;
            };
            if (x instanceof JustifyCenter && y instanceof JustifyCenter) {
                return true;
            };
            if (x instanceof JustifyEnd && y instanceof JustifyEnd) {
                return true;
            };
            if (x instanceof JustifyBetween && y instanceof JustifyBetween) {
                return true;
            };
            if (x instanceof JustifyAround && y instanceof JustifyAround) {
                return true;
            };
            if (x instanceof JustifyEvenly && y instanceof JustifyEvenly) {
                return true;
            };
            return false;
        };
    }
};
var eqGap = {
    eq: function (x) {
        return function (y) {
            if (x instanceof G0 && y instanceof G0) {
                return true;
            };
            if (x instanceof G1 && y instanceof G1) {
                return true;
            };
            if (x instanceof G2 && y instanceof G2) {
                return true;
            };
            if (x instanceof G3 && y instanceof G3) {
                return true;
            };
            if (x instanceof G4 && y instanceof G4) {
                return true;
            };
            if (x instanceof G5 && y instanceof G5) {
                return true;
            };
            if (x instanceof G6 && y instanceof G6) {
                return true;
            };
            if (x instanceof G8 && y instanceof G8) {
                return true;
            };
            if (x instanceof G10 && y instanceof G10) {
                return true;
            };
            if (x instanceof G12 && y instanceof G12) {
                return true;
            };
            if (x instanceof G16 && y instanceof G16) {
                return true;
            };
            return false;
        };
    }
};
var eqAlignment = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Start && y instanceof Start) {
                return true;
            };
            if (x instanceof Center && y instanceof Center) {
                return true;
            };
            if (x instanceof End && y instanceof End) {
                return true;
            };
            if (x instanceof Stretch && y instanceof Stretch) {
                return true;
            };
            if (x instanceof Baseline && y instanceof Baseline) {
                return true;
            };
            return false;
        };
    }
};
var defaultProps = /* #__PURE__ */ (function () {
    return {
        gap: G0.value,
        align: Stretch.value,
        justify: JustifyStart.value,
        wrap: false,
        reverse: false,
        className: ""
    };
})();

// | Z-stack (absolute positioned layers)
var zstack = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "relative", props.className ]) ])(map(function (child) {
            return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "absolute inset-0" ]) ])([ child ]);
        })(children));
    };
};

// | Add custom class
var className = function (c) {
    return function (props) {
        return {
            gap: props.gap,
            align: props.align,
            justify: props.justify,
            wrap: props.wrap,
            reverse: props.reverse,
            className: props.className + (" " + c)
        };
    };
};

// | Center content both horizontally and vertically
var center = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex items-center justify-center", props.className ]) ])(children);
    };
};
var alignClass = function (v) {
    if (v instanceof Start) {
        return "items-start";
    };
    if (v instanceof Center) {
        return "items-center";
    };
    if (v instanceof End) {
        return "items-end";
    };
    if (v instanceof Stretch) {
        return "items-stretch";
    };
    if (v instanceof Baseline) {
        return "items-baseline";
    };
    throw new Error("Failed pattern match at Hydrogen.Layout.Stack (line 105, column 14 - line 110, column 31): " + [ v.constructor.name ]);
};

// | Horizontal stack (row)
var hstack = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        var wrapClass = (function () {
            if (props.wrap) {
                return "flex-wrap";
            };
            return "";
        })();
        var direction = (function () {
            if (props.reverse) {
                return "flex-row-reverse";
            };
            return "flex-row";
        })();
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex", direction, gapClass(props.gap), alignClass(props.align), justifyClass(props.justify), wrapClass, props.className ]) ])(children);
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // components
// ═══════════════════════════════════════════════════════════════════════════════
// | Vertical stack (column)
var vstack = function (propMods) {
    return function (children) {
        var props = Data_Array.foldl(function (p) {
            return function (f) {
                return f(p);
            };
        })(defaultProps)(propMods);
        var wrapClass = (function () {
            if (props.wrap) {
                return "flex-wrap";
            };
            return "";
        })();
        var direction = (function () {
            if (props.reverse) {
                return "flex-col-reverse";
            };
            return "flex-col";
        })();
        return Halogen_HTML_Elements.div([ Hydrogen_UI_Core.cls([ "flex", direction, gapClass(props.gap), alignClass(props.align), justifyClass(props.justify), wrapClass, props.className ]) ])(children);
    };
};

// | Set alignment
var align = function (a) {
    return function (props) {
        return {
            gap: props.gap,
            justify: props.justify,
            wrap: props.wrap,
            reverse: props.reverse,
            className: props.className,
            align: a
        };
    };
};
export {
    vstack,
    hstack,
    zstack,
    center,
    spacer,
    gap,
    align,
    justify,
    wrap,
    reverse,
    className,
    G0,
    G1,
    G2,
    G3,
    G4,
    G5,
    G6,
    G8,
    G10,
    G12,
    G16,
    Start,
    Center,
    End,
    Stretch,
    Baseline,
    JustifyStart,
    JustifyCenter,
    JustifyEnd,
    JustifyBetween,
    JustifyAround,
    JustifyEvenly,
    eqGap,
    eqAlignment,
    eqJustification
};
