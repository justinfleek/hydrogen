// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                    // hydrogen // schema // color // gradient
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Gradient - color transitions and blending.
// |
// | Supports multiple gradient types:
// | - **Linear**: Color transition along a line
// | - **Radial**: Color transition from center outward
// | - **Conic**: Color transition around a circle
// | - **Mesh**: 4-color bilinear interpolation with control points
// |
// | All gradients use ColorStop to define color positions along the gradient.
import * as Data_Array from "../Data.Array/index.js";
import * as Data_Eq from "../Data.Eq/index.js";
import * as Data_Functor from "../Data.Functor/index.js";
import * as Data_Int from "../Data.Int/index.js";
import * as Data_Maybe from "../Data.Maybe/index.js";
import * as Data_Number from "../Data.Number/index.js";
import * as Data_Ord from "../Data.Ord/index.js";
import * as Data_Ordering from "../Data.Ordering/index.js";
import * as Data_Semigroup from "../Data.Semigroup/index.js";
import * as Data_Show from "../Data.Show/index.js";
import * as Hydrogen_Schema_Bounded from "../Hydrogen.Schema.Bounded/index.js";
import * as Hydrogen_Schema_Color_Channel from "../Hydrogen.Schema.Color.Channel/index.js";
import * as Hydrogen_Schema_Color_RGB from "../Hydrogen.Schema.Color.RGB/index.js";
var append = /* #__PURE__ */ Data_Semigroup.append(Data_Semigroup.semigroupArray);
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showNumber);
var map = /* #__PURE__ */ Data_Functor.map(Data_Functor.functorArray);
var compare = /* #__PURE__ */ Data_Ord.compare(Data_Ord.ordNumber);
var eq1 = /* #__PURE__ */ Data_Eq.eq(Hydrogen_Schema_Color_RGB.eqRGB);
var compare1 = /* #__PURE__ */ Data_Ord.compare(Hydrogen_Schema_Color_RGB.ordRGB);

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                        // ratio
// ═══════════════════════════════════════════════════════════════════════════════
// | Ratio - normalized position value (0.0 to 1.0)
// |
// | Used for gradient stop positions, where:
// | - 0.0 = start of gradient
// | - 0.5 = middle
// | - 1.0 = end of gradient
var Ratio = function (x) {
    return x;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // mesh gradient
// ═══════════════════════════════════════════════════════════════════════════════
// | MeshGradient - bilinear interpolation between 4 corner colors
// |
// | Like Illustrator's mesh gradient but simplified to 4 control points.
// | Each corner has a color and blend strength.
// | Position controls where the color influence reaches (0.0-1.0 from corner)
var MeshGradient = function (x) {
    return x;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // colorstop
// ═══════════════════════════════════════════════════════════════════════════════
// | ColorStop - a color at a specific position in a gradient
// |
// | Defines both the color and where it appears along the gradient path.
var ColorStop = function (x) {
    return x;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // conic gradient
// ═══════════════════════════════════════════════════════════════════════════════
// | ConicGradient - color transition around a circle
// |
// | Like a color wheel, starting at a specific angle and rotating around center
var ConicGradient = function (x) {
    return x;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // linear gradient
// ═══════════════════════════════════════════════════════════════════════════════
// | LinearGradient - color transition along a line
// |
// | Angle is in degrees (0 = to top, 90 = to right, 180 = to bottom, 270 = to left)
var LinearGradient = function (x) {
    return x;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // radial gradient
// ═══════════════════════════════════════════════════════════════════════════════
// | RadialGradient - color transition from center point outward
// |
// | Center position is in percentage (0.0-1.0 for both x and y)
// | Size is the radius in CSS terms (can be keyword or explicit)
var RadialGradient = function (x) {
    return x;
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // gradient
// ═══════════════════════════════════════════════════════════════════════════════
// | Gradient - sum type for all gradient variants
var Linear = /* #__PURE__ */ (function () {
    function Linear(value0) {
        this.value0 = value0;
    };
    Linear.create = function (value0) {
        return new Linear(value0);
    };
    return Linear;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // gradient
// ═══════════════════════════════════════════════════════════════════════════════
// | Gradient - sum type for all gradient variants
var Radial = /* #__PURE__ */ (function () {
    function Radial(value0) {
        this.value0 = value0;
    };
    Radial.create = function (value0) {
        return new Radial(value0);
    };
    return Radial;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // gradient
// ═══════════════════════════════════════════════════════════════════════════════
// | Gradient - sum type for all gradient variants
var Conic = /* #__PURE__ */ (function () {
    function Conic(value0) {
        this.value0 = value0;
    };
    Conic.create = function (value0) {
        return new Conic(value0);
    };
    return Conic;
})();

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // gradient
// ═══════════════════════════════════════════════════════════════════════════════
// | Gradient - sum type for all gradient variants
var Mesh = /* #__PURE__ */ (function () {
    function Mesh(value0) {
        this.value0 = value0;
    };
    Mesh.create = function (value0) {
        return new Mesh(value0);
    };
    return Mesh;
})();

// Helper: Update element at index
var updateAt = function (idx) {
    return function (val) {
        return function (arr) {
            var v = Data_Array.index(arr)(idx);
            if (v instanceof Data_Maybe.Nothing) {
                return arr;
            };
            if (v instanceof Data_Maybe.Just) {
                var before = Data_Array.take(idx)(arr);
                var after = Data_Array.drop(idx + 1 | 0)(arr);
                return append(before)(append([ val ])(after));
            };
            throw new Error("Failed pattern match at Hydrogen.Schema.Color.Gradient (line 388, column 3 - line 393, column 34): " + [ v.constructor.name ]);
        };
    };
};

// | Update color stop at a specific index
var updateStop = function (idx) {
    return function (stop) {
        return function (v) {
            if (v instanceof Linear) {
                return new Linear({
                    angle: v.value0.angle,
                    stops: updateAt(idx)(stop)(v.value0.stops)
                });
            };
            if (v instanceof Radial) {
                return new Radial({
                    centerX: v.value0.centerX,
                    centerY: v.value0.centerY,
                    stops: updateAt(idx)(stop)(v.value0.stops)
                });
            };
            if (v instanceof Conic) {
                return new Conic({
                    centerX: v.value0.centerX,
                    centerY: v.value0.centerY,
                    startAngle: v.value0.startAngle,
                    stops: updateAt(idx)(stop)(v.value0.stops)
                });
            };
            if (v instanceof Mesh) {
                return new Mesh(v.value0);
            };
            throw new Error("Failed pattern match at Hydrogen.Schema.Color.Gradient (line 343, column 23 - line 347, column 19): " + [ v.constructor.name ]);
        };
    };
};

// | Extract the raw Number value
var unwrapRatio = function (v) {
    return v;
};

// | Create a ratio without clamping (use when value is known valid)
var unsafeRatio = Ratio;
var showRatio = {
    show: function (v) {
        return show(v);
    }
};

// Helper: Remove element at index
var removeAt = function (idx) {
    return function (arr) {
        var before = Data_Array.take(idx)(arr);
        var after = Data_Array.drop(idx + 1 | 0)(arr);
        return append(before)(after);
    };
};

// | Remove color stop at a specific index
var removeStopAt = function (idx) {
    return function (v) {
        if (v instanceof Linear) {
            return new Linear({
                angle: v.value0.angle,
                stops: removeAt(idx)(v.value0.stops)
            });
        };
        if (v instanceof Radial) {
            return new Radial({
                centerX: v.value0.centerX,
                centerY: v.value0.centerY,
                stops: removeAt(idx)(v.value0.stops)
            });
        };
        if (v instanceof Conic) {
            return new Conic({
                centerX: v.value0.centerX,
                centerY: v.value0.centerY,
                startAngle: v.value0.startAngle,
                stops: removeAt(idx)(v.value0.stops)
            });
        };
        if (v instanceof Mesh) {
            return new Mesh(v.value0);
        };
        throw new Error("Failed pattern match at Hydrogen.Schema.Color.Gradient (line 335, column 20 - line 339, column 19): " + [ v.constructor.name ]);
    };
};

// | Convert ratio to percentage (0-100)
var ratioToPercent = function (v) {
    return v * 100.0;
};
var showColorStop = {
    show: function (v) {
        return Hydrogen_Schema_Color_RGB.rgbToCss(v.color) + (" " + (show(ratioToPercent(v.position)) + "%"));
    }
};

// | Convert array of color stops to CSS format
var stopsToCSS = function (stops) {
    var stopToCSS = function (v) {
        return Hydrogen_Schema_Color_RGB.rgbToCss(v.color) + (" " + (show(ratioToPercent(v.position)) + "%"));
    };
    var joinWith = function (sep) {
        return function (arr) {
            var v = Data_Array.uncons(arr);
            if (v instanceof Data_Maybe.Nothing) {
                return "";
            };
            if (v instanceof Data_Maybe.Just) {
                return Data_Array.foldl(function (acc) {
                    return function (y) {
                        return acc + (sep + y);
                    };
                })(v.value0.head)(v.value0.tail);
            };
            throw new Error("Failed pattern match at Hydrogen.Schema.Color.Gradient (line 317, column 22 - line 319, column 73): " + [ v.constructor.name ]);
        };
    };
    var stopStrings = map(stopToCSS)(stops);
    return joinWith(", ")(stopStrings);
};

// | Create a ratio, clamping to 0.0-1.0
var ratio = function (n) {
    return Hydrogen_Schema_Bounded.clampNumber(0.0)(1.0)(n);
};

// Helper: Reverse stop positions
var reverseStops = /* #__PURE__ */ (function () {
    var reverseStop = function (v) {
        return {
            color: v.color,
            position: ratio(1.0 - unwrapRatio(v.position))
        };
    };
    return map(reverseStop);
})();

// | Reverse gradient direction
var reverseGradient = function (v) {
    if (v instanceof Linear) {
        return new Linear({
            angle: v.value0.angle + 180.0,
            stops: reverseStops(v.value0.stops)
        });
    };
    if (v instanceof Radial) {
        return new Radial(v.value0);
    };
    if (v instanceof Conic) {
        return new Conic({
            centerX: v.value0.centerX,
            centerY: v.value0.centerY,
            startAngle: v.value0.startAngle,
            stops: reverseStops(v.value0.stops)
        });
    };
    if (v instanceof Mesh) {
        return new Mesh(v.value0);
    };
    throw new Error("Failed pattern match at Hydrogen.Schema.Color.Gradient (line 351, column 19 - line 360, column 19): " + [ v.constructor.name ]);
};

// | Convert radial gradient to CSS  
var radialToCss = function (v) {
    return "radial-gradient(circle at " + (show(ratioToPercent(v.centerX)) + ("% " + (show(ratioToPercent(v.centerY)) + ("%, " + (stopsToCSS(v.stops) + ")")))));
};

// | Create a mesh gradient with equal blend (0.5) for all corners
var meshGradient = function (tl) {
    return function (tr) {
        return function (bl) {
            return function (br) {
                return {
                    topLeft: tl,
                    topRight: tr,
                    bottomLeft: bl,
                    bottomRight: br,
                    topLeftBlend: ratio(0.5),
                    topRightBlend: ratio(0.5),
                    bottomLeftBlend: ratio(0.5),
                    bottomRightBlend: ratio(0.5)
                };
            };
        };
    };
};

// | Convert linear gradient to CSS
var linearToCss = function (v) {
    return "linear-gradient(" + (show(v.angle) + ("deg, " + (stopsToCSS(v.stops) + ")")));
};

// | Get stops from a gradient
var getStops = function (v) {
    if (v instanceof Linear) {
        return v.value0.stops;
    };
    if (v instanceof Radial) {
        return v.value0.stops;
    };
    if (v instanceof Conic) {
        return v.value0.stops;
    };
    if (v instanceof Mesh) {
        return [  ];
    };
    throw new Error("Failed pattern match at Hydrogen.Schema.Color.Gradient (line 364, column 12 - line 368, column 15): " + [ v.constructor.name ]);
};
var eqRatio = {
    eq: function (x) {
        return function (y) {
            return x === y;
        };
    }
};
var eq2 = /* #__PURE__ */ Data_Eq.eq(eqRatio);
var ordRatio = {
    compare: function (x) {
        return function (y) {
            return compare(x)(y);
        };
    },
    Eq0: function () {
        return eqRatio;
    }
};
var greaterThanOrEq = /* #__PURE__ */ Data_Ord.greaterThanOrEq(ordRatio);
var lessThanOrEq = /* #__PURE__ */ Data_Ord.lessThanOrEq(ordRatio);
var compare2 = /* #__PURE__ */ Data_Ord.compare(ordRatio);

// | Find the two stops that bracket a position
var findStopSegment = function (pos) {
    return function (stops) {
        var go = function ($copy_arr) {
            var $tco_done = false;
            var $tco_result;
            function $tco_loop(arr) {
                var v = Data_Array.uncons(arr);
                if (v instanceof Data_Maybe.Nothing) {
                    $tco_done = true;
                    return Data_Maybe.Nothing.value;
                };
                if (v instanceof Data_Maybe.Just) {
                    var v1 = Data_Array.uncons(v.value0.tail);
                    if (v1 instanceof Data_Maybe.Nothing) {
                        $tco_done = true;
                        return Data_Maybe.Nothing.value;
                    };
                    if (v1 instanceof Data_Maybe.Just) {
                        var $153 = greaterThanOrEq(pos)(v.value0.head.position) && lessThanOrEq(pos)(v1.value0.head.position);
                        if ($153) {
                            $tco_done = true;
                            return new Data_Maybe.Just({
                                before: v.value0.head,
                                after: v1.value0.head
                            });
                        };
                        $copy_arr = v.value0.tail;
                        return;
                    };
                    throw new Error("Failed pattern match at Hydrogen.Schema.Color.Gradient (line 472, column 7 - line 479, column 28): " + [ v1.constructor.name ]);
                };
                throw new Error("Failed pattern match at Hydrogen.Schema.Color.Gradient (line 469, column 12 - line 479, column 28): " + [ v.constructor.name ]);
            };
            while (!$tco_done) {
                $tco_result = $tco_loop($copy_arr);
            };
            return $tco_result;
        };
        return go(stops);
    };
};

// | Sort color stops by position
var sortStops = /* #__PURE__ */ (function () {
    var compareStops = function (v) {
        return function (v1) {
            return compare2(v.position)(v1.position);
        };
    };
    return Data_Array.sortBy(compareStops);
})();

// | Create a linear gradient with default angle (180 degrees = top to bottom)
var linearGradient = function (stops) {
    return {
        angle: 180.0,
        stops: sortStops(stops)
    };
};

// | Create a linear gradient with specific angle
var linearGradientFromAngle = function (angle) {
    return function (stops) {
        return {
            angle: angle,
            stops: sortStops(stops)
        };
    };
};

// | Create a radial gradient centered at (0.5, 0.5)
var radialGradient = function (stops) {
    return {
        centerX: ratio(0.5),
        centerY: ratio(0.5),
        stops: sortStops(stops)
    };
};

// | Set stops for a gradient
var setStops = function (stops) {
    return function (v) {
        if (v instanceof Linear) {
            return new Linear({
                angle: v.value0.angle,
                stops: sortStops(stops)
            });
        };
        if (v instanceof Radial) {
            return new Radial({
                centerX: v.value0.centerX,
                centerY: v.value0.centerY,
                stops: sortStops(stops)
            });
        };
        if (v instanceof Conic) {
            return new Conic({
                centerX: v.value0.centerX,
                centerY: v.value0.centerY,
                startAngle: v.value0.startAngle,
                stops: sortStops(stops)
            });
        };
        if (v instanceof Mesh) {
            return new Mesh(v.value0);
        };
        throw new Error("Failed pattern match at Hydrogen.Schema.Color.Gradient (line 372, column 18 - line 376, column 19): " + [ v.constructor.name ]);
    };
};
var eqMeshGradient = {
    eq: function (x) {
        return function (y) {
            return eq1(x.bottomLeft)(y.bottomLeft) && eq2(x.bottomLeftBlend)(y.bottomLeftBlend) && eq1(x.bottomRight)(y.bottomRight) && eq2(x.bottomRightBlend)(y.bottomRightBlend) && eq1(x.topLeft)(y.topLeft) && eq2(x.topLeftBlend)(y.topLeftBlend) && eq1(x.topRight)(y.topRight) && eq2(x.topRightBlend)(y.topRightBlend);
        };
    }
};
var eq3 = /* #__PURE__ */ Data_Eq.eq(eqMeshGradient);
var eqColorStop = {
    eq: function (x) {
        return function (y) {
            return eq1(x.color)(y.color) && eq2(x.position)(y.position);
        };
    }
};
var eq4 = /* #__PURE__ */ Data_Eq.eq(/* #__PURE__ */ Data_Eq.eqArray(eqColorStop));
var eqConicGradient = {
    eq: function (x) {
        return function (y) {
            return eq2(x.centerX)(y.centerX) && eq2(x.centerY)(y.centerY) && x.startAngle === y.startAngle && eq4(x.stops)(y.stops);
        };
    }
};
var eq5 = /* #__PURE__ */ Data_Eq.eq(eqConicGradient);
var eqLinearGradient = {
    eq: function (x) {
        return function (y) {
            return x.angle === y.angle && eq4(x.stops)(y.stops);
        };
    }
};
var eq6 = /* #__PURE__ */ Data_Eq.eq(eqLinearGradient);
var eqRadialGradient = {
    eq: function (x) {
        return function (y) {
            return eq2(x.centerX)(y.centerX) && eq2(x.centerY)(y.centerY) && eq4(x.stops)(y.stops);
        };
    }
};
var eq7 = /* #__PURE__ */ Data_Eq.eq(eqRadialGradient);
var eqGradient = {
    eq: function (x) {
        return function (y) {
            if (x instanceof Linear && y instanceof Linear) {
                return eq6(x.value0)(y.value0);
            };
            if (x instanceof Radial && y instanceof Radial) {
                return eq7(x.value0)(y.value0);
            };
            if (x instanceof Conic && y instanceof Conic) {
                return eq5(x.value0)(y.value0);
            };
            if (x instanceof Mesh && y instanceof Mesh) {
                return eq3(x.value0)(y.value0);
            };
            return false;
        };
    }
};
var ordColorStop = {
    compare: function (x) {
        return function (y) {
            var v = compare1(x.color)(y.color);
            if (v instanceof Data_Ordering.LT) {
                return Data_Ordering.LT.value;
            };
            if (v instanceof Data_Ordering.GT) {
                return Data_Ordering.GT.value;
            };
            return compare2(x.position)(y.position);
        };
    },
    Eq0: function () {
        return eqColorStop;
    }
};

// | Convert conic gradient to CSS
var conicToCss = function (v) {
    return "conic-gradient(from " + (show(v.startAngle) + ("deg at " + (show(ratioToPercent(v.centerX)) + ("% " + (show(ratioToPercent(v.centerY)) + ("%, " + (stopsToCSS(v.stops) + ")")))))));
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // css output
// ═══════════════════════════════════════════════════════════════════════════════
// | Convert gradient to CSS
var toCss = function (v) {
    if (v instanceof Linear) {
        return linearToCss(v.value0);
    };
    if (v instanceof Radial) {
        return radialToCss(v.value0);
    };
    if (v instanceof Conic) {
        return conicToCss(v.value0);
    };
    if (v instanceof Mesh) {
        return "/* Mesh gradients require Canvas API or SVG - no CSS equivalent */";
    };
    throw new Error("Failed pattern match at Hydrogen.Schema.Color.Gradient (line 280, column 1 - line 280, column 28): " + [ v.constructor.name ]);
};

// | Create a conic gradient centered at (0.5, 0.5) starting from top
var conicGradient = function (stops) {
    return {
        centerX: ratio(0.5),
        centerY: ratio(0.5),
        startAngle: 0.0,
        stops: sortStops(stops)
    };
};

// | Create a color stop at a specific position
var colorStop = function (color) {
    return function (pos) {
        return {
            color: color,
            position: ratio(pos)
        };
    };
};

// | Alias for colorStop with flipped arguments
var colorStopAt = function (pos) {
    return function (color) {
        return colorStop(color)(pos);
    };
};

// | Blend two RGB colors with weight (0.0 = all first, 1.0 = all second)
var blendRGB = function (weight) {
    return function (c1) {
        return function (c2) {
            var w = Data_Number.max(0.0)(Data_Number.min(1.0)(weight));
            var r2 = Hydrogen_Schema_Color_Channel.toNumber(Hydrogen_Schema_Color_RGB.red(c2));
            var r1 = Hydrogen_Schema_Color_Channel.toNumber(Hydrogen_Schema_Color_RGB.red(c1));
            var rFinal = Data_Int.round(r1 * (1.0 - w) + r2 * w);
            var g2 = Hydrogen_Schema_Color_Channel.toNumber(Hydrogen_Schema_Color_RGB.green(c2));
            var g1 = Hydrogen_Schema_Color_Channel.toNumber(Hydrogen_Schema_Color_RGB.green(c1));
            var gFinal = Data_Int.round(g1 * (1.0 - w) + g2 * w);
            var b2 = Hydrogen_Schema_Color_Channel.toNumber(Hydrogen_Schema_Color_RGB.blue(c2));
            var b1 = Hydrogen_Schema_Color_Channel.toNumber(Hydrogen_Schema_Color_RGB.blue(c1));
            var bFinal = Data_Int.round(b1 * (1.0 - w) + b2 * w);
            return Hydrogen_Schema_Color_RGB.rgbFromChannels(Hydrogen_Schema_Color_Channel.channel(rFinal))(Hydrogen_Schema_Color_Channel.channel(gFinal))(Hydrogen_Schema_Color_Channel.channel(bFinal));
        };
    };
};

// | Interpolate color between stops at a specific position
var interpolateStops = function (pos) {
    return function (stops) {
        var v = findStopSegment(pos)(stops);
        if (v instanceof Data_Maybe.Nothing) {
            var v1 = Data_Array.uncons(stops);
            if (v1 instanceof Data_Maybe.Nothing) {
                return Hydrogen_Schema_Color_RGB.rgb(0)(0)(0);
            };
            if (v1 instanceof Data_Maybe.Just) {
                return v1.value0.head.color;
            };
            throw new Error("Failed pattern match at Hydrogen.Schema.Color.Gradient (line 453, column 7 - line 455, column 54): " + [ v1.constructor.name ]);
        };
        if (v instanceof Data_Maybe.Just) {
            
            // Calculate interpolation factor between the two stops
var range = unwrapRatio(v.value0.after.position) - unwrapRatio(v.value0.before.position);
            var offset = unwrapRatio(pos) - unwrapRatio(v.value0.before.position);
            var t = (function () {
                var $200 = range === 0.0;
                if ($200) {
                    return 0.0;
                };
                return offset / range;
            })();
            return blendRGB(t)(v.value0.before.color)(v.value0.after.color);
        };
        throw new Error("Failed pattern match at Hydrogen.Schema.Color.Gradient (line 450, column 3 - line 463, column 35): " + [ v.constructor.name ]);
    };
};

// | Sample color at angle position in conic gradient (0.0-1.0 = 0-360 degrees)
var sampleConicAt = function (pos) {
    return function (v) {
        return interpolateStops(ratio(pos))(v.stops);
    };
};

// | Sample color at position in linear gradient
var sampleLinearAt = function (pos) {
    return function (v) {
        return interpolateStops(ratio(pos))(v.stops);
    };
};

// | Sample color at position in radial gradient (0.0 = center, 1.0 = edge)
var sampleRadialAt = function (pos) {
    return function (v) {
        return interpolateStops(ratio(pos))(v.stops);
    };
};

// | Sample color at 2D position in mesh gradient (both coordinates 0.0-1.0)
var sampleMeshAt = function (x) {
    return function (y) {
        return function (v) {
            var yClamped = Data_Number.max(0.0)(Data_Number.min(1.0)(y));
            
            // Bilinear interpolation between 4 corners
var xClamped = Data_Number.max(0.0)(Data_Number.min(1.0)(x));
            
            // Get blend factors (simplified - full implementation would use blend ratios)
var xBlend = xClamped;
            
            // Interpolate top edge
var topColor = blendRGB(1.0 - xBlend)(v.topLeft)(blendRGB(xBlend)(v.topRight)(v.topRight));
            
            // Interpolate bottom edge  
var bottomColor = blendRGB(1.0 - xBlend)(v.bottomLeft)(blendRGB(xBlend)(v.bottomRight)(v.bottomRight));
            
            // Interpolate vertically
var finalColor = blendRGB(1.0 - yClamped)(topColor)(blendRGB(yClamped)(bottomColor)(bottomColor));
            return finalColor;
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // color sampling
// ═══════════════════════════════════════════════════════════════════════════════
// | Sample color at a specific position in a gradient
var sampleAt = function (pos) {
    return function (v) {
        if (v instanceof Linear) {
            return sampleLinearAt(pos)(v.value0);
        };
        if (v instanceof Radial) {
            return sampleRadialAt(pos)(v.value0);
        };
        if (v instanceof Conic) {
            return sampleConicAt(pos)(v.value0);
        };
        if (v instanceof Mesh) {
            return sampleMeshAt(0.5)(0.5)(v.value0);
        };
        throw new Error("Failed pattern match at Hydrogen.Schema.Color.Gradient (line 407, column 16 - line 411, column 35): " + [ v.constructor.name ]);
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                           // gradient manipulation
// ═══════════════════════════════════════════════════════════════════════════════
// | Add a color stop to a gradient
var addStop = function (stop) {
    return function (v) {
        if (v instanceof Linear) {
            return new Linear({
                angle: v.value0.angle,
                stops: sortStops(append(v.value0.stops)([ stop ]))
            });
        };
        if (v instanceof Radial) {
            return new Radial({
                centerX: v.value0.centerX,
                centerY: v.value0.centerY,
                stops: sortStops(append(v.value0.stops)([ stop ]))
            });
        };
        if (v instanceof Conic) {
            return new Conic({
                centerX: v.value0.centerX,
                centerY: v.value0.centerY,
                startAngle: v.value0.startAngle,
                stops: sortStops(append(v.value0.stops)([ stop ]))
            });
        };
        if (v instanceof Mesh) {
            return new Mesh(v.value0);
        };
        throw new Error("Failed pattern match at Hydrogen.Schema.Color.Gradient (line 327, column 16 - line 331, column 19): " + [ v.constructor.name ]);
    };
};
export {
    ColorStop,
    Linear,
    Radial,
    Conic,
    Mesh,
    ratio,
    unsafeRatio,
    unwrapRatio,
    ratioToPercent,
    colorStop,
    colorStopAt,
    linearGradient,
    linearGradientFromAngle,
    radialGradient,
    conicGradient,
    meshGradient,
    addStop,
    removeStopAt,
    updateStop,
    reverseGradient,
    getStops,
    setStops,
    sampleAt,
    sampleLinearAt,
    sampleRadialAt,
    sampleConicAt,
    sampleMeshAt,
    toCss,
    linearToCss,
    radialToCss,
    conicToCss,
    eqRatio,
    ordRatio,
    showRatio,
    eqColorStop,
    ordColorStop,
    showColorStop,
    eqLinearGradient,
    eqRadialGradient,
    eqConicGradient,
    eqMeshGradient,
    eqGradient
};
