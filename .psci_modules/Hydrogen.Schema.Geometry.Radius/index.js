// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                            // hydrogen // schema // geometry
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Border radius and corner primitives for the Hydrogen Schema.
// |
// | Shape defines personality. This module provides type-safe
// | border radius and corner definitions.
// |
// | ## Design Principles
// |
// | 1. **Scale-based**: Consistent radius scale across UI
// | 2. **Per-corner control**: Each corner can be different
// | 3. **Semantic naming**: none, sm, md, lg, full
// | 4. **Composable**: Mix and match corners
import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Int from "../Data.Int/index.js";
import * as Data_Show from "../Data.Show/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showInt);
var show1 = /* #__PURE__ */ Data_Show.show(Data_Show.showNumber);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // core types
// ═══════════════════════════════════════════════════════════════════════════════
// | Border radius value
var RadiusPx = /* #__PURE__ */ (function () {
    function RadiusPx(value0) {
        this.value0 = value0;
    };
    RadiusPx.create = function (value0) {
        return new RadiusPx(value0);
    };
    return RadiusPx;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // core types
// ═══════════════════════════════════════════════════════════════════════════════
// | Border radius value
var RadiusPercent = /* #__PURE__ */ (function () {
    function RadiusPercent(value0) {
        this.value0 = value0;
    };
    RadiusPercent.create = function (value0) {
        return new RadiusPercent(value0);
    };
    return RadiusPercent;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // core types
// ═══════════════════════════════════════════════════════════════════════════════
// | Border radius value
var RadiusRem = /* #__PURE__ */ (function () {
    function RadiusRem(value0) {
        this.value0 = value0;
    };
    RadiusRem.create = function (value0) {
        return new RadiusRem(value0);
    };
    return RadiusRem;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // core types
// ═══════════════════════════════════════════════════════════════════════════════
// | Border radius value
var RadiusFull = /* #__PURE__ */ (function () {
    function RadiusFull() {

    };
    RadiusFull.value = new RadiusFull();
    return RadiusFull;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // core types
// ═══════════════════════════════════════════════════════════════════════════════
// | Border radius value
var RadiusNone = /* #__PURE__ */ (function () {
    function RadiusNone() {

    };
    RadiusNone.value = new RadiusNone();
    return RadiusNone;
})();

// | Extra small radius (2px)
var xs = /* #__PURE__ */ (function () {
    return new RadiusPx(2.0);
})();

// | 2x extra large radius (16px)
var xl2 = /* #__PURE__ */ (function () {
    return new RadiusPx(16.0);
})();

// | Extra large radius (12px)
var xl = /* #__PURE__ */ (function () {
    return new RadiusPx(12.0);
})();

// | Small radius (4px)
var sm = /* #__PURE__ */ (function () {
    return new RadiusPx(4.0);
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // helpers
// ═══════════════════════════════════════════════════════════════════════════════
// | Show number cleanly
var showNum = function (n) {
    var rounded = Data_Int.round(n);
    var $18 = Data_Int.toNumber(rounded) === n;
    if ($18) {
        return show(rounded);
    };
    return show1(n);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // conversion
// ═══════════════════════════════════════════════════════════════════════════════
// | Convert radius to CSS string
var toCss = function (v) {
    if (v instanceof RadiusPx) {
        return showNum(v.value0) + "px";
    };
    if (v instanceof RadiusPercent) {
        return showNum(v.value0) + "%";
    };
    if (v instanceof RadiusRem) {
        return showNum(v.value0) + "rem";
    };
    if (v instanceof RadiusFull) {
        return "9999px";
    };
    if (v instanceof RadiusNone) {
        return "0";
    };
    throw new Error("Failed pattern match at Hydrogen.Schema.Geometry.Radius (line 212, column 9 - line 217, column 20): " + [ v.constructor.name ]);
};
var showRadius = {
    show: toCss
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // operations
// ═══════════════════════════════════════════════════════════════════════════════
// | Scale radius by a factor
var scale = function (factor) {
    return function (v) {
        if (v instanceof RadiusPx) {
            return new RadiusPx(v.value0 * factor);
        };
        if (v instanceof RadiusPercent) {
            return new RadiusPercent(v.value0 * factor);
        };
        if (v instanceof RadiusRem) {
            return new RadiusRem(v.value0 * factor);
        };
        if (v instanceof RadiusFull) {
            return RadiusFull.value;
        };
        if (v instanceof RadiusNone) {
            return RadiusNone.value;
        };
        throw new Error("Failed pattern match at Hydrogen.Schema.Geometry.Radius (line 191, column 16 - line 196, column 27): " + [ v.constructor.name ]);
    };
};

// | Create radius in rem
var rem = /* #__PURE__ */ (function () {
    return RadiusRem.create;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                         // radius constructors
// ═══════════════════════════════════════════════════════════════════════════════
// | Create radius in pixels
var px = /* #__PURE__ */ (function () {
    return RadiusPx.create;
})();

// | Create radius in percentage
var percent = /* #__PURE__ */ (function () {
    return RadiusPercent.create;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // semantic scale
// ═══════════════════════════════════════════════════════════════════════════════
// | No radius (sharp corners)
var none = /* #__PURE__ */ (function () {
    return RadiusNone.value;
})();

// | Medium radius (6px)
var md = /* #__PURE__ */ (function () {
    return new RadiusPx(6.0);
})();

// | Large radius (8px)
var lg = /* #__PURE__ */ (function () {
    return new RadiusPx(8.0);
})();

// | Halve the radius
var half = /* #__PURE__ */ scale(0.5);

// | Full radius (pill shape)
var full = /* #__PURE__ */ (function () {
    return RadiusFull.value;
})();
var eqRadius = {
    eq: function (x) {
        return function (y) {
            if (x instanceof RadiusPx && y instanceof RadiusPx) {
                return x.value0 === y.value0;
            };
            if (x instanceof RadiusPercent && y instanceof RadiusPercent) {
                return x.value0 === y.value0;
            };
            if (x instanceof RadiusRem && y instanceof RadiusRem) {
                return x.value0 === y.value0;
            };
            if (x instanceof RadiusFull && y instanceof RadiusFull) {
                return true;
            };
            if (x instanceof RadiusNone && y instanceof RadiusNone) {
                return true;
            };
            return false;
        };
    }
};
var eq1 = /* #__PURE__ */ Data_Eq.eq(eqRadius);

// | Double the radius
var $$double = /* #__PURE__ */ scale(2.0);

// | Convert corners to CSS border-radius string
var cornersToCss = function (v) {
    var topSame = eq1(v.topLeft)(v.topRight);
    var bottomSame = eq1(v.bottomRight)(v.bottomLeft);
    var allSame = eq1(v.topLeft)(v.topRight) && (eq1(v.topRight)(v.bottomRight) && eq1(v.bottomRight)(v.bottomLeft));
    if (allSame) {
        return toCss(v.topLeft);
    };
    var $37 = topSame && bottomSame;
    if ($37) {
        return toCss(v.topLeft) + (" " + toCss(v.bottomRight));
    };
    return toCss(v.topLeft) + (" " + (toCss(v.topRight) + (" " + (toCss(v.bottomRight) + (" " + toCss(v.bottomLeft))))));
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                         // corner constructors
// ═══════════════════════════════════════════════════════════════════════════════
// | Create corners with different radius for each
var corners = function (topLeft) {
    return function (topRight) {
        return function (bottomRight) {
            return function (bottomLeft) {
                return {
                    topLeft: topLeft,
                    topRight: topRight,
                    bottomRight: bottomRight,
                    bottomLeft: bottomLeft
                };
            };
        };
    };
};

// | Same radius on all corners
var cornersAll = function (r) {
    return corners(r)(r)(r)(r);
};

// | Radius only on bottom corners
var cornersBottom = function (r) {
    return corners(none)(none)(r)(r);
};

// | Radius only on bottom-left
var cornersBottomLeft = function (r) {
    return corners(none)(none)(none)(r);
};

// | Radius only on bottom-right
var cornersBottomRight = function (r) {
    return corners(none)(none)(r)(none);
};

// | Radius only on left corners
var cornersLeft = function (r) {
    return corners(r)(none)(none)(r);
};

// | Radius only on right corners
var cornersRight = function (r) {
    return corners(none)(r)(r)(none);
};

// | Radius only on top corners
var cornersTop = function (r) {
    return corners(r)(r)(none)(none);
};

// | Radius only on top-left
var cornersTopLeft = function (r) {
    return corners(r)(none)(none)(none);
};

// | Radius only on top-right
var cornersTopRight = function (r) {
    return corners(none)(r)(none)(none);
};
export {
    RadiusPx,
    RadiusPercent,
    RadiusRem,
    RadiusFull,
    RadiusNone,
    px,
    percent,
    rem,
    none,
    xs,
    sm,
    md,
    lg,
    xl,
    xl2,
    full,
    corners,
    cornersAll,
    cornersTop,
    cornersBottom,
    cornersLeft,
    cornersRight,
    cornersTopLeft,
    cornersTopRight,
    cornersBottomLeft,
    cornersBottomRight,
    scale,
    $$double as double,
    half,
    toCss,
    cornersToCss,
    eqRadius,
    showRadius
};
