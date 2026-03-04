//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                        // hydrogen // runtime // core // easing
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! # Pure Easing Functions
//!
//! **Zero JavaScript. Zero browser APIs. Zero side effects.**
//!
//! Easing functions map normalized time [0,1] to normalized progress [0,1].
//! This module matches the PureScript `Hydrogen.Schema.Temporal.Easing` types.
//!
//! ## Easing Categories
//!
//! - **Linear**: Constant velocity, no acceleration
//! - **Polynomial**: Quadratic, Cubic, Quartic, Quintic power curves
//! - **Trigonometric**: Sine-based smooth curves
//! - **Exponential**: Dramatic acceleration/deceleration
//! - **Circular**: Arc-based curves
//! - **Back**: Overshoots target before settling
//! - **Elastic**: Spring-like oscillation
//! - **Bounce**: Ball bounce physics
//! - **CubicBezier**: CSS-compatible bezier curves
//!
//! ## Mathematical Properties
//!
//! All easing functions satisfy:
//! - `f(0) = 0` (starts at zero)
//! - `f(1) = 1` (ends at one)
//! - Input clamped to [0,1] before evaluation
//!
//! Note: Elastic and Back easings may temporarily exceed [0,1] during animation,
//! but always return to exactly 0 at start and 1 at end.
//!
//! ## Relationship to PureScript Schema
//!
//! This module corresponds to:
//! - `Hydrogen.Schema.Temporal.Easing`
//! - `Hydrogen.Schema.Temporal.CubicBezierEasing`
//! - `Hydrogen.Schema.Temporal.ProceduralEasing`

use std::f64::consts::PI;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // easing function
// ═══════════════════════════════════════════════════════════════════════════════

/// Standard easing function type.
///
/// Matches `Hydrogen.Schema.Temporal.Easing` from PureScript.
/// All easing functions map t ∈ [0,1] → [0,1] (with possible overshoot for
/// Elastic/Back variants).
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Easing {
    // ─────────────────────────────────────────────────────────────── Linear
    /// Constant velocity: f(t) = t
    Linear,

    // ─────────────────────────────────────────────────────────────── Quadratic
    /// Quadratic ease-in: f(t) = t²
    EaseInQuad,
    /// Quadratic ease-out: f(t) = t(2-t)
    EaseOutQuad,
    /// Quadratic ease-in-out
    EaseInOutQuad,

    // ─────────────────────────────────────────────────────────────── Cubic
    /// Cubic ease-in: f(t) = t³
    EaseInCubic,
    /// Cubic ease-out: f(t) = 1 + (t-1)³
    EaseOutCubic,
    /// Cubic ease-in-out
    EaseInOutCubic,

    // ─────────────────────────────────────────────────────────────── Quartic
    /// Quartic ease-in: f(t) = t⁴
    EaseInQuart,
    /// Quartic ease-out
    EaseOutQuart,
    /// Quartic ease-in-out
    EaseInOutQuart,

    // ─────────────────────────────────────────────────────────────── Quintic
    /// Quintic ease-in: f(t) = t⁵
    EaseInQuint,
    /// Quintic ease-out
    EaseOutQuint,
    /// Quintic ease-in-out
    EaseInOutQuint,

    // ─────────────────────────────────────────────────────────────── Sine
    /// Sine ease-in: f(t) = 1 - cos(t × π/2)
    EaseInSine,
    /// Sine ease-out: f(t) = sin(t × π/2)
    EaseOutSine,
    /// Sine ease-in-out
    EaseInOutSine,

    // ─────────────────────────────────────────────────────────────── Exponential
    /// Exponential ease-in: f(t) = 2^(10(t-1))
    EaseInExpo,
    /// Exponential ease-out
    EaseOutExpo,
    /// Exponential ease-in-out
    EaseInOutExpo,

    // ─────────────────────────────────────────────────────────────── Circular
    /// Circular ease-in: f(t) = 1 - √(1-t²)
    EaseInCirc,
    /// Circular ease-out
    EaseOutCirc,
    /// Circular ease-in-out
    EaseInOutCirc,

    // ─────────────────────────────────────────────────────────────── Back
    /// Back ease-in: overshoots backward before accelerating
    EaseInBack,
    /// Back ease-out: overshoots target before settling
    EaseOutBack,
    /// Back ease-in-out
    EaseInOutBack,

    // ─────────────────────────────────────────────────────────────── Elastic
    /// Elastic ease-in: spring oscillation at start
    EaseInElastic,
    /// Elastic ease-out: spring oscillation settling at end
    EaseOutElastic,
    /// Elastic ease-in-out
    EaseInOutElastic,

    // ─────────────────────────────────────────────────────────────── Bounce
    /// Bounce ease-in: ball drop at start
    EaseInBounce,
    /// Bounce ease-out: ball drop settling at end
    EaseOutBounce,
    /// Bounce ease-in-out
    EaseInOutBounce,

    // ─────────────────────────────────────────────────────────────── Bezier
    /// CSS-compatible cubic bezier: (x1, y1, x2, y2)
    ///
    /// Control points define the shape:
    /// - (0.25, 0.1, 0.25, 1.0) = CSS `ease`
    /// - (0.42, 0.0, 1.0, 1.0) = CSS `ease-in`
    /// - (0.0, 0.0, 0.58, 1.0) = CSS `ease-out`
    /// - (0.42, 0.0, 0.58, 1.0) = CSS `ease-in-out`
    CubicBezier { x1: f64, y1: f64, x2: f64, y2: f64 },
}

impl Default for Easing {
    fn default() -> Self {
        Easing::Linear
    }
}

impl Easing {
    /// Evaluate the easing function at time t.
    ///
    /// Input is clamped to [0, 1] before evaluation.
    /// Output is typically in [0, 1] but may exceed for Elastic/Back variants.
    pub fn eval(&self, t: f64) -> f64 {
        // Clamp input to valid range
        let t = t.clamp(0.0, 1.0);

        match self {
            // Linear
            Easing::Linear => t,

            // Quadratic
            Easing::EaseInQuad => t * t,
            Easing::EaseOutQuad => t * (2.0 - t),
            Easing::EaseInOutQuad => {
                if t < 0.5 {
                    2.0 * t * t
                } else {
                    -1.0 + (4.0 - 2.0 * t) * t
                }
            }

            // Cubic
            Easing::EaseInCubic => t * t * t,
            Easing::EaseOutCubic => {
                let t1 = t - 1.0;
                t1 * t1 * t1 + 1.0
            }
            Easing::EaseInOutCubic => {
                if t < 0.5 {
                    4.0 * t * t * t
                } else {
                    (t - 1.0) * (2.0 * t - 2.0) * (2.0 * t - 2.0) + 1.0
                }
            }

            // Quartic
            Easing::EaseInQuart => t * t * t * t,
            Easing::EaseOutQuart => {
                let t1 = t - 1.0;
                1.0 - t1 * t1 * t1 * t1
            }
            Easing::EaseInOutQuart => {
                if t < 0.5 {
                    8.0 * t * t * t * t
                } else {
                    let t1 = t - 1.0;
                    1.0 - 8.0 * t1 * t1 * t1 * t1
                }
            }

            // Quintic
            Easing::EaseInQuint => t * t * t * t * t,
            Easing::EaseOutQuint => {
                let t1 = t - 1.0;
                1.0 + t1 * t1 * t1 * t1 * t1
            }
            Easing::EaseInOutQuint => {
                if t < 0.5 {
                    16.0 * t * t * t * t * t
                } else {
                    let t1 = t - 1.0;
                    1.0 + 16.0 * t1 * t1 * t1 * t1 * t1
                }
            }

            // Sine
            Easing::EaseInSine => 1.0 - (t * PI / 2.0).cos(),
            Easing::EaseOutSine => (t * PI / 2.0).sin(),
            Easing::EaseInOutSine => -((t * PI).cos() - 1.0) / 2.0,

            // Exponential
            Easing::EaseInExpo => {
                if t == 0.0 {
                    0.0
                } else {
                    2.0_f64.powf(10.0 * (t - 1.0))
                }
            }
            Easing::EaseOutExpo => {
                if t == 1.0 {
                    1.0
                } else {
                    1.0 - 2.0_f64.powf(-10.0 * t)
                }
            }
            Easing::EaseInOutExpo => {
                if t == 0.0 {
                    0.0
                } else if t == 1.0 {
                    1.0
                } else if t < 0.5 {
                    2.0_f64.powf(20.0 * t - 10.0) / 2.0
                } else {
                    (2.0 - 2.0_f64.powf(-20.0 * t + 10.0)) / 2.0
                }
            }

            // Circular
            Easing::EaseInCirc => 1.0 - (1.0 - t * t).sqrt(),
            Easing::EaseOutCirc => (1.0 - (t - 1.0) * (t - 1.0)).sqrt(),
            Easing::EaseInOutCirc => {
                if t < 0.5 {
                    (1.0 - (1.0 - 4.0 * t * t).sqrt()) / 2.0
                } else {
                    ((1.0 - (-2.0 * t + 2.0).powi(2)).sqrt() + 1.0) / 2.0
                }
            }

            // Back (with overshoot constant c1 = 1.70158)
            Easing::EaseInBack => {
                const C1: f64 = 1.70158;
                const C3: f64 = C1 + 1.0;
                C3 * t * t * t - C1 * t * t
            }
            Easing::EaseOutBack => {
                const C1: f64 = 1.70158;
                const C3: f64 = C1 + 1.0;
                let t1 = t - 1.0;
                1.0 + C3 * t1 * t1 * t1 + C1 * t1 * t1
            }
            Easing::EaseInOutBack => {
                const C1: f64 = 1.70158;
                const C2: f64 = C1 * 1.525;
                if t < 0.5 {
                    (2.0 * t).powi(2) * ((C2 + 1.0) * 2.0 * t - C2) / 2.0
                } else {
                    ((2.0 * t - 2.0).powi(2) * ((C2 + 1.0) * (t * 2.0 - 2.0) + C2) + 2.0) / 2.0
                }
            }

            // Elastic (spring oscillation)
            Easing::EaseInElastic => {
                const C4: f64 = (2.0 * PI) / 3.0;
                if t == 0.0 {
                    0.0
                } else if t == 1.0 {
                    1.0
                } else {
                    -2.0_f64.powf(10.0 * t - 10.0) * ((t * 10.0 - 10.75) * C4).sin()
                }
            }
            Easing::EaseOutElastic => {
                const C4: f64 = (2.0 * PI) / 3.0;
                if t == 0.0 {
                    0.0
                } else if t == 1.0 {
                    1.0
                } else {
                    2.0_f64.powf(-10.0 * t) * ((t * 10.0 - 0.75) * C4).sin() + 1.0
                }
            }
            Easing::EaseInOutElastic => {
                const C5: f64 = (2.0 * PI) / 4.5;
                if t == 0.0 {
                    0.0
                } else if t == 1.0 {
                    1.0
                } else if t < 0.5 {
                    -(2.0_f64.powf(20.0 * t - 10.0) * ((20.0 * t - 11.125) * C5).sin()) / 2.0
                } else {
                    (2.0_f64.powf(-20.0 * t + 10.0) * ((20.0 * t - 11.125) * C5).sin()) / 2.0 + 1.0
                }
            }

            // Bounce (ball drop physics)
            Easing::EaseInBounce => 1.0 - Easing::EaseOutBounce.eval(1.0 - t),
            Easing::EaseOutBounce => bounce_out(t),
            Easing::EaseInOutBounce => {
                if t < 0.5 {
                    (1.0 - bounce_out(1.0 - 2.0 * t)) / 2.0
                } else {
                    (1.0 + bounce_out(2.0 * t - 1.0)) / 2.0
                }
            }

            // Cubic Bezier
            Easing::CubicBezier { x1, y1, x2, y2 } => cubic_bezier_eval(*x1, *y1, *x2, *y2, t),
        }
    }

    /// Evaluate and clamp result to [0, 1].
    ///
    /// Useful when the result must be in range (e.g., for opacity).
    pub fn eval_clamped(&self, t: f64) -> f64 {
        self.eval(t).clamp(0.0, 1.0)
    }

    /// Check if this easing may overshoot [0, 1] range.
    pub const fn may_overshoot(&self) -> bool {
        matches!(
            self,
            Easing::EaseInBack
                | Easing::EaseOutBack
                | Easing::EaseInOutBack
                | Easing::EaseInElastic
                | Easing::EaseOutElastic
                | Easing::EaseInOutElastic
        )
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // css preset easings
// ═══════════════════════════════════════════════════════════════════════════════

/// CSS `ease` preset: (0.25, 0.1, 0.25, 1.0)
pub const CSS_EASE: Easing = Easing::CubicBezier {
    x1: 0.25,
    y1: 0.1,
    x2: 0.25,
    y2: 1.0,
};

/// CSS `ease-in` preset: (0.42, 0.0, 1.0, 1.0)
pub const CSS_EASE_IN: Easing = Easing::CubicBezier {
    x1: 0.42,
    y1: 0.0,
    x2: 1.0,
    y2: 1.0,
};

/// CSS `ease-out` preset: (0.0, 0.0, 0.58, 1.0)
pub const CSS_EASE_OUT: Easing = Easing::CubicBezier {
    x1: 0.0,
    y1: 0.0,
    x2: 0.58,
    y2: 1.0,
};

/// CSS `ease-in-out` preset: (0.42, 0.0, 0.58, 1.0)
pub const CSS_EASE_IN_OUT: Easing = Easing::CubicBezier {
    x1: 0.42,
    y1: 0.0,
    x2: 0.58,
    y2: 1.0,
};

/// CSS `linear` as bezier: (0.0, 0.0, 1.0, 1.0)
pub const CSS_LINEAR: Easing = Easing::CubicBezier {
    x1: 0.0,
    y1: 0.0,
    x2: 1.0,
    y2: 1.0,
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // helper functions
// ═══════════════════════════════════════════════════════════════════════════════

/// Bounce out implementation (ball drop physics).
fn bounce_out(t: f64) -> f64 {
    const N1: f64 = 7.5625;
    const D1: f64 = 2.75;

    if t < 1.0 / D1 {
        N1 * t * t
    } else if t < 2.0 / D1 {
        let t1 = t - 1.5 / D1;
        N1 * t1 * t1 + 0.75
    } else if t < 2.5 / D1 {
        let t1 = t - 2.25 / D1;
        N1 * t1 * t1 + 0.9375
    } else {
        let t1 = t - 2.625 / D1;
        N1 * t1 * t1 + 0.984375
    }
}

/// Evaluate cubic bezier curve at time t.
///
/// Uses Newton-Raphson iteration to find the parameter for a given x,
/// then evaluates y at that parameter.
fn cubic_bezier_eval(x1: f64, y1: f64, x2: f64, y2: f64, t: f64) -> f64 {
    // For linear bezier, shortcut
    if x1 == y1 && x2 == y2 {
        return t;
    }

    // Newton-Raphson iteration to find bezier parameter for x = t
    let mut guess = t;
    for _ in 0..8 {
        let x = bezier_sample(x1, x2, guess);
        let dx = bezier_slope(x1, x2, guess);
        if dx.abs() < 1e-6 {
            break;
        }
        guess -= (x - t) / dx;
        guess = guess.clamp(0.0, 1.0);
    }

    // Evaluate y at found parameter
    bezier_sample(y1, y2, guess)
}

/// Sample a 1D bezier curve at parameter t.
/// The curve goes from 0 to 1 with control points at p1 and p2.
fn bezier_sample(p1: f64, p2: f64, t: f64) -> f64 {
    // B(t) = 3(1-t)²t·p1 + 3(1-t)t²·p2 + t³
    let t2 = t * t;
    let t3 = t2 * t;
    let mt = 1.0 - t;
    let mt2 = mt * mt;

    3.0 * mt2 * t * p1 + 3.0 * mt * t2 * p2 + t3
}

/// Derivative of bezier curve at parameter t.
fn bezier_slope(p1: f64, p2: f64, t: f64) -> f64 {
    // B'(t) = 3(1-t)²·p1 + 6(1-t)t·(p2-p1) + 3t²·(1-p2)
    let t2 = t * t;
    let mt = 1.0 - t;
    let mt2 = mt * mt;

    3.0 * mt2 * p1 + 6.0 * mt * t * (p2 - p1) + 3.0 * t2 * (1.0 - p2)
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                           // interpolation utils
// ═══════════════════════════════════════════════════════════════════════════════

/// Linear interpolation between two values.
///
/// Returns `a` when `t = 0`, `b` when `t = 1`.
pub fn lerp(a: f64, b: f64, t: f64) -> f64 {
    a + (b - a) * t
}

/// Apply easing to an interpolation.
///
/// Equivalent to `lerp(a, b, easing.eval(t))`.
pub fn ease_lerp(a: f64, b: f64, t: f64, easing: Easing) -> f64 {
    lerp(a, b, easing.eval(t))
}

/// Map a value from one range to another.
///
/// Equivalent to linear interpolation from `out_min` to `out_max`
/// based on where `value` falls in `[in_min, in_max]`.
pub fn map_range(value: f64, in_min: f64, in_max: f64, out_min: f64, out_max: f64) -> f64 {
    let t = if (in_max - in_min).abs() < 1e-10 {
        0.0
    } else {
        (value - in_min) / (in_max - in_min)
    };
    lerp(out_min, out_max, t)
}

/// Map a value from one range to another with easing.
pub fn map_range_eased(
    value: f64,
    in_min: f64,
    in_max: f64,
    out_min: f64,
    out_max: f64,
    easing: Easing,
) -> f64 {
    let t = if (in_max - in_min).abs() < 1e-10 {
        0.0
    } else {
        (value - in_min) / (in_max - in_min)
    };
    ease_lerp(out_min, out_max, t, easing)
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                      // tests
// ═══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    /// All easings must satisfy f(0) = 0 and f(1) = 1
    #[test]
    fn test_easing_endpoints() {
        let easings = [
            Easing::Linear,
            Easing::EaseInQuad,
            Easing::EaseOutQuad,
            Easing::EaseInOutQuad,
            Easing::EaseInCubic,
            Easing::EaseOutCubic,
            Easing::EaseInOutCubic,
            Easing::EaseInQuart,
            Easing::EaseOutQuart,
            Easing::EaseInOutQuart,
            Easing::EaseInQuint,
            Easing::EaseOutQuint,
            Easing::EaseInOutQuint,
            Easing::EaseInSine,
            Easing::EaseOutSine,
            Easing::EaseInOutSine,
            Easing::EaseInExpo,
            Easing::EaseOutExpo,
            Easing::EaseInOutExpo,
            Easing::EaseInCirc,
            Easing::EaseOutCirc,
            Easing::EaseInOutCirc,
            Easing::EaseInBack,
            Easing::EaseOutBack,
            Easing::EaseInOutBack,
            Easing::EaseInElastic,
            Easing::EaseOutElastic,
            Easing::EaseInOutElastic,
            Easing::EaseInBounce,
            Easing::EaseOutBounce,
            Easing::EaseInOutBounce,
            CSS_EASE,
            CSS_EASE_IN,
            CSS_EASE_OUT,
            CSS_EASE_IN_OUT,
        ];

        for easing in easings {
            let at_zero = easing.eval(0.0);
            let at_one = easing.eval(1.0);

            assert!(
                (at_zero - 0.0).abs() < 1e-10,
                "{:?}.eval(0) = {} (expected 0)",
                easing,
                at_zero
            );
            assert!(
                (at_one - 1.0).abs() < 1e-10,
                "{:?}.eval(1) = {} (expected 1)",
                easing,
                at_one
            );
        }
    }

    #[test]
    fn test_linear() {
        assert_eq!(Easing::Linear.eval(0.0), 0.0);
        assert_eq!(Easing::Linear.eval(0.5), 0.5);
        assert_eq!(Easing::Linear.eval(1.0), 1.0);
    }

    #[test]
    fn test_quadratic() {
        // Ease-in: slow start
        assert!(Easing::EaseInQuad.eval(0.5) < 0.5);

        // Ease-out: slow end
        assert!(Easing::EaseOutQuad.eval(0.5) > 0.5);

        // Ease-in-out: symmetric
        let mid = Easing::EaseInOutQuad.eval(0.5);
        assert!((mid - 0.5).abs() < 0.01);
    }

    #[test]
    fn test_back_overshoot() {
        // Back easing should overshoot
        assert!(Easing::EaseInBack.may_overshoot());
        assert!(Easing::EaseOutBack.may_overshoot());

        // EaseInBack goes negative before positive
        assert!(Easing::EaseInBack.eval(0.2) < 0.0);

        // EaseOutBack exceeds 1.0 before settling
        assert!(Easing::EaseOutBack.eval(0.8) > 1.0);
    }

    #[test]
    fn test_elastic_overshoot() {
        assert!(Easing::EaseOutElastic.may_overshoot());

        // Elastic oscillates around target
        let mid = Easing::EaseOutElastic.eval(0.3);
        assert!(mid > 1.0, "Expected overshoot, got {}", mid);
    }

    #[test]
    fn test_clamped() {
        // Clamped version should never exceed [0, 1]
        for t in [0.0, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 1.0] {
            let result = Easing::EaseOutBack.eval_clamped(t);
            assert!(result >= 0.0 && result <= 1.0);
        }
    }

    #[test]
    fn test_input_clamping() {
        // Values outside [0, 1] should be clamped
        assert_eq!(Easing::Linear.eval(-0.5), 0.0);
        assert_eq!(Easing::Linear.eval(1.5), 1.0);
    }

    #[test]
    fn test_cubic_bezier_linear() {
        // Linear bezier should return input unchanged
        let linear = Easing::CubicBezier {
            x1: 0.0,
            y1: 0.0,
            x2: 1.0,
            y2: 1.0,
        };
        for i in 0..=10 {
            let t = i as f64 / 10.0;
            let result = linear.eval(t);
            assert!(
                (result - t).abs() < 0.01,
                "linear bezier at {} = {} (expected {})",
                t,
                result,
                t
            );
        }
    }

    #[test]
    fn test_lerp() {
        assert_eq!(lerp(0.0, 100.0, 0.0), 0.0);
        assert_eq!(lerp(0.0, 100.0, 0.5), 50.0);
        assert_eq!(lerp(0.0, 100.0, 1.0), 100.0);
        assert_eq!(lerp(-50.0, 50.0, 0.5), 0.0);
    }

    #[test]
    fn test_map_range() {
        assert_eq!(map_range(50.0, 0.0, 100.0, 0.0, 1.0), 0.5);
        assert_eq!(map_range(0.0, 0.0, 100.0, 200.0, 400.0), 200.0);
        assert_eq!(map_range(100.0, 0.0, 100.0, 200.0, 400.0), 400.0);
    }
}
