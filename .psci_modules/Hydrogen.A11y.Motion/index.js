// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                         // hydrogen // motion
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// | Reduced motion support
// |
// | Utilities for respecting user's motion preferences.
// |
// | ## Usage
// |
// | ```purescript
// | import Hydrogen.A11y.Motion as Motion
// |
// | -- Only animate when user allows motion
// | Motion.motionSafe "animate-spin"
// | -- "motion-safe:animate-spin"
// |
// | -- Disable animations when reduced motion preferred
// | Motion.motionReduce "animate-none"
// | -- "motion-reduce:animate-none"
// |
// | -- Combined approach
// | Motion.withReducedMotion "animate-bounce" "animate-none"
// | -- "motion-safe:animate-bounce motion-reduce:animate-none"
// | ```

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // presets
// ═══════════════════════════════════════════════════════════════════════════════
// | Safe transition that respects reduced motion
// |
// | Uses instant transition when reduced motion is preferred.
var safeTransition = "motion-safe:transition-all motion-safe:duration-200 motion-reduce:transition-none";

// | Reduced animation preset
// |
// | Common pattern for reduced motion fallback.
var reducedAnimation = "motion-reduce:animate-none motion-reduce:transition-none";

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // motion prefixes
// ═══════════════════════════════════════════════════════════════════════════════
// | Apply class only when reduced motion is NOT preferred
// |
// | Use for animations that should be disabled when user prefers reduced motion.
var motionSafe = function (cls) {
    return "motion-safe:" + cls;
};

// | Apply class only when reduced motion IS preferred
// |
// | Use for fallback styles when animations are disabled.
var motionReduce = function (cls) {
    return "motion-reduce:" + cls;
};

// | Safe animation that respects reduced motion
// |
// | Disables animation when reduced motion is preferred.
var safeAnimation = function (animationClass) {
    return motionSafe(animationClass) + (" " + motionReduce("animate-none"));
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // combined
// ═══════════════════════════════════════════════════════════════════════════════
// | Apply animated class normally, fallback when reduced motion preferred
// |
// | ```purescript
// | withReducedMotion "animate-spin" "animate-none"
// | -- Uses spin animation normally, no animation when reduced motion preferred
// | ```
var withReducedMotion = function (normalClass) {
    return function (reducedClass) {
        return motionSafe(normalClass) + (" " + motionReduce(reducedClass));
    };
};
export {
    motionSafe,
    motionReduce,
    withReducedMotion,
    safeTransition,
    safeAnimation,
    reducedAnimation
};
