// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                         // hydrogen // spring
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Spring physics animations
// |
// | Physics-based spring animation calculations.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.Motion.Spring as Spring
// |
// | -- Create a spring config
// | let spring = Spring.springConfig 170.0 26.0  -- stiffness, damping
// |
// | -- Preset springs
// | Spring.springDefault
// | Spring.springGentle
// | Spring.springWobbly
// | Spring.springStiff
// |
// | -- Calculate spring value at time t
// | Spring.springValue spring 0.0 1.0 0.5  -- from, to, progress
// | ```
import * as Data_Number from "../Data.Number/index.js";
import * as Data_Show from "../Data.Show/index.js";
var show = /* #__PURE__ */ Data_Show.show(Data_Show.showNumber);

// | Calculate spring velocity at time t
var springVelocity = function (config) {
    return function (from) {
        return function (to) {
            return function (t) {
                var delta = to - from;
                var dampingRatio = config.damping / (2.0 * Data_Number.sqrt(config.stiffness * config.mass));
                var angularFreq = Data_Number.sqrt(config.stiffness / config.mass);
                var dampedFreq = angularFreq * Data_Number.sqrt(1.0 - dampingRatio * dampingRatio);
                var expDecay = Data_Number.exp(-dampingRatio * angularFreq * t);
                var $10 = dampingRatio >= 1.0;
                if ($10) {
                    return delta * angularFreq * angularFreq * t * expDecay;
                };
                return delta * expDecay * dampedFreq * Data_Number.sin(dampedFreq * t);
            };
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // spring calculation
// ═══════════════════════════════════════════════════════════════════════════════
// | Calculate spring value at time t (0 to 1)
// |
// | Uses damped harmonic oscillator equation.
var springValue = function (config) {
    return function (from) {
        return function (to) {
            return function (t) {
                var delta = to - from;
                var dampingRatio = config.damping / (2.0 * Data_Number.sqrt(config.stiffness * config.mass));
                var angularFreq = Data_Number.sqrt(config.stiffness / config.mass);
                
                // Underdamped (bouncy) case
var dampedFreq = angularFreq * Data_Number.sqrt(1.0 - dampingRatio * dampingRatio);
                
                // Exponential decay
var expDecay = Data_Number.exp(-dampingRatio * angularFreq * t);
                
                // Oscillation
var oscillation = Data_Number.cos(dampedFreq * t) + ((dampingRatio * angularFreq) / dampedFreq) * Data_Number.sin(dampedFreq * t);
                var $11 = dampingRatio >= 1.0;
                if ($11) {
                    return to - delta * expDecay * (1.0 + angularFreq * t);
                };
                return to - delta * expDecay * oscillation;
            };
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // css spring
// ═══════════════════════════════════════════════════════════════════════════════
// | Approximate spring as cubic-bezier for CSS transitions
// |
// | Note: This is an approximation - true spring physics requires JS.
var springToCubicBezier = function (config) {
    
    // Approximate cubic bezier values based on damping
var x1 = 0.25;
    var dampingRatio = config.damping / (2.0 * Data_Number.sqrt(config.stiffness * config.mass));
    var y1 = (function () {
        var $12 = dampingRatio < 0.5;
        if ($12) {
            return 0.1;
        };
        return 0.25;
    })();
    var y2 = (function () {
        var $13 = dampingRatio < 0.5;
        if ($13) {
            return 1.5;
        };
        return 1.0;
    })();
    return "cubic-bezier(" + (show(x1) + (", " + (show(y1) + (", " + (show(0.25) + (", " + (show(y2) + ")")))))));
};

// | Create a spring configuration
var springConfig = function (stiffness) {
    return function (damping) {
        return {
            stiffness: stiffness,
            damping: damping,
            mass: 1.0,
            velocity: 0.0,
            precision: 1.0e-2
        };
    };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // presets
// ═══════════════════════════════════════════════════════════════════════════════
// | Default spring (balanced)
var springDefault = /* #__PURE__ */ springConfig(170.0)(26.0);

// | Gentle spring (smooth, no bounce)
var springGentle = /* #__PURE__ */ springConfig(120.0)(14.0);

// | Molasses (very slow, heavy)
var springMolasses = /* #__PURE__ */ springConfig(280.0)(120.0);

// | Slow spring (gradual)
var springSlow = /* #__PURE__ */ springConfig(280.0)(60.0);

// | Stiff spring (fast, minimal bounce)
var springStiff = /* #__PURE__ */ springConfig(210.0)(20.0);

// | Wobbly spring (bouncy)
var springWobbly = /* #__PURE__ */ springConfig(180.0)(12.0);

// | Check if spring is at rest (within precision threshold)
var isAtRest = function (config) {
    return function (from) {
        return function (to) {
            return function (t) {
                var currentVelocity = springVelocity(config)(from)(to)(t);
                var currentValue = springValue(config)(from)(to)(t);
                return Data_Number.abs(currentValue - to) < config.precision && Data_Number.abs(currentVelocity) < config.precision;
            };
        };
    };
};
export {
    springConfig,
    springDefault,
    springGentle,
    springWobbly,
    springStiff,
    springSlow,
    springMolasses,
    springValue,
    springVelocity,
    isAtRest,
    springToCubicBezier
};
