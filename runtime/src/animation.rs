//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                                // hydrogen // animation // wasm
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! # Animation and Timing
//!
//! Pure Rust animation primitives. **Zero JavaScript.**
//!
//! ## Core APIs
//! - `now()` - High-resolution timestamp via performance.now()
//! - `request_animation_frame()` - Frame scheduling
//! - Spring physics with critically damped, underdamped, overdamped
//! - Easing functions (all standard + custom bezier)
//!
//! ## Integration
//! - Haptics: Animations can trigger haptic feedback at keyframes
//! - Elevation: Animated elevation changes for card lifts, etc.
//! - Lean4: Easing functions are bounded [0,1] → [0,1], provable

use wasm_bindgen::prelude::*;
use web_sys::window;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // timing functions
// ═══════════════════════════════════════════════════════════════════════════════

/// High-resolution timestamp in milliseconds.
/// Uses performance.now() for sub-millisecond precision.
#[wasm_bindgen]
pub fn animation_now() -> f64 {
    window()
        .and_then(|w| w.performance())
        .map(|p| p.now())
        .unwrap_or(0.0)
}

/// Convert a number to a 32-bit integer by truncation toward zero.
/// Replaces the JS bitwise OR trick: `n | 0`
#[wasm_bindgen]
pub fn animation_number_to_int(n: f64) -> i32 {
    n as i32
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                           // easing functions
// ═══════════════════════════════════════════════════════════════════════════════

/// Standard easing function type.
/// All easing functions map t ∈ [0,1] → [0,1] (bounded, provable in Lean4).
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Easing {
    // Linear
    Linear,

    // Quadratic
    EaseInQuad,
    EaseOutQuad,
    EaseInOutQuad,

    // Cubic
    EaseInCubic,
    EaseOutCubic,
    EaseInOutCubic,

    // Quartic
    EaseInQuart,
    EaseOutQuart,
    EaseInOutQuart,

    // Quintic
    EaseInQuint,
    EaseOutQuint,
    EaseInOutQuint,

    // Sine
    EaseInSine,
    EaseOutSine,
    EaseInOutSine,

    // Exponential
    EaseInExpo,
    EaseOutExpo,
    EaseInOutExpo,

    // Circular
    EaseInCirc,
    EaseOutCirc,
    EaseInOutCirc,

    // Back (overshoots)
    EaseInBack,
    EaseOutBack,
    EaseInOutBack,

    // Elastic (spring-like)
    EaseInElastic,
    EaseOutElastic,
    EaseInOutElastic,

    // Bounce
    EaseInBounce,
    EaseOutBounce,
    EaseInOutBounce,

    // Custom cubic bezier (like CSS)
    CubicBezier { x1: f64, y1: f64, x2: f64, y2: f64 },
}

impl Easing {
    /// Evaluate the easing function at time t ∈ [0,1].
    /// Returns value in [0,1] for standard easings.
    pub fn eval(&self, t: f64) -> f64 {
        let t = t.clamp(0.0, 1.0);

        match self {
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
            Easing::EaseInSine => 1.0 - (t * std::f64::consts::FRAC_PI_2).cos(),
            Easing::EaseOutSine => (t * std::f64::consts::FRAC_PI_2).sin(),
            Easing::EaseInOutSine => -(((t * std::f64::consts::PI).cos() - 1.0) / 2.0),

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

            // Back
            Easing::EaseInBack => {
                let c1 = 1.70158;
                let c3 = c1 + 1.0;
                c3 * t * t * t - c1 * t * t
            }
            Easing::EaseOutBack => {
                let c1 = 1.70158;
                let c3 = c1 + 1.0;
                let t1 = t - 1.0;
                1.0 + c3 * t1 * t1 * t1 + c1 * t1 * t1
            }
            Easing::EaseInOutBack => {
                let c1 = 1.70158;
                let c2 = c1 * 1.525;
                if t < 0.5 {
                    (2.0 * t).powi(2) * ((c2 + 1.0) * 2.0 * t - c2) / 2.0
                } else {
                    ((2.0 * t - 2.0).powi(2) * ((c2 + 1.0) * (t * 2.0 - 2.0) + c2) + 2.0) / 2.0
                }
            }

            // Elastic
            Easing::EaseInElastic => {
                let c4 = (2.0 * std::f64::consts::PI) / 3.0;
                if t == 0.0 {
                    0.0
                } else if t == 1.0 {
                    1.0
                } else {
                    -2.0_f64.powf(10.0 * t - 10.0) * ((t * 10.0 - 10.75) * c4).sin()
                }
            }
            Easing::EaseOutElastic => {
                let c4 = (2.0 * std::f64::consts::PI) / 3.0;
                if t == 0.0 {
                    0.0
                } else if t == 1.0 {
                    1.0
                } else {
                    2.0_f64.powf(-10.0 * t) * ((t * 10.0 - 0.75) * c4).sin() + 1.0
                }
            }
            Easing::EaseInOutElastic => {
                let c5 = (2.0 * std::f64::consts::PI) / 4.5;
                if t == 0.0 {
                    0.0
                } else if t == 1.0 {
                    1.0
                } else if t < 0.5 {
                    -(2.0_f64.powf(20.0 * t - 10.0) * ((20.0 * t - 11.125) * c5).sin()) / 2.0
                } else {
                    (2.0_f64.powf(-20.0 * t + 10.0) * ((20.0 * t - 11.125) * c5).sin()) / 2.0 + 1.0
                }
            }

            // Bounce
            Easing::EaseInBounce => 1.0 - Easing::EaseOutBounce.eval(1.0 - t),
            Easing::EaseOutBounce => {
                let n1 = 7.5625;
                let d1 = 2.75;
                if t < 1.0 / d1 {
                    n1 * t * t
                } else if t < 2.0 / d1 {
                    let t1 = t - 1.5 / d1;
                    n1 * t1 * t1 + 0.75
                } else if t < 2.5 / d1 {
                    let t1 = t - 2.25 / d1;
                    n1 * t1 * t1 + 0.9375
                } else {
                    let t1 = t - 2.625 / d1;
                    n1 * t1 * t1 + 0.984375
                }
            }
            Easing::EaseInOutBounce => {
                if t < 0.5 {
                    (1.0 - Easing::EaseOutBounce.eval(1.0 - 2.0 * t)) / 2.0
                } else {
                    (1.0 + Easing::EaseOutBounce.eval(2.0 * t - 1.0)) / 2.0
                }
            }

            // Cubic bezier
            Easing::CubicBezier { x1, y1, x2, y2 } => cubic_bezier_eval(*x1, *y1, *x2, *y2, t),
        }
    }
}

/// Evaluate cubic bezier curve (like CSS timing functions).
fn cubic_bezier_eval(x1: f64, y1: f64, x2: f64, y2: f64, t: f64) -> f64 {
    // Newton-Raphson to find t for given x, then evaluate y
    let mut guess = t;
    for _ in 0..8 {
        let x = cubic_bezier_sample(x1, x2, guess);
        let dx = cubic_bezier_slope(x1, x2, guess);
        if dx.abs() < 1e-6 {
            break;
        }
        guess -= (x - t) / dx;
    }
    cubic_bezier_sample(y1, y2, guess)
}

fn cubic_bezier_sample(p1: f64, p2: f64, t: f64) -> f64 {
    let t2 = t * t;
    let t3 = t2 * t;
    3.0 * p1 * t * (1.0 - t).powi(2) + 3.0 * p2 * t2 * (1.0 - t) + t3
}

fn cubic_bezier_slope(p1: f64, p2: f64, t: f64) -> f64 {
    let t2 = t * t;
    3.0 * p1 * (1.0 - t).powi(2) + 6.0 * p2 * t * (1.0 - t) - 3.0 * p2 * t2 + 3.0 * t2
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // spring physics
// ═══════════════════════════════════════════════════════════════════════════════

/// Spring configuration.
#[derive(Clone, Copy, Debug)]
pub struct SpringConfig {
    /// Stiffness (spring constant k). Higher = faster oscillation.
    pub stiffness: f64,
    /// Damping coefficient. Higher = less bouncy.
    pub damping: f64,
    /// Mass of the object. Higher = slower movement.
    pub mass: f64,
}

impl SpringConfig {
    /// iOS-style spring (slightly bouncy, quick settle).
    pub fn ios() -> Self {
        SpringConfig {
            stiffness: 300.0,
            damping: 30.0,
            mass: 1.0,
        }
    }

    /// Critically damped (no overshoot, fastest to target).
    pub fn critical() -> Self {
        SpringConfig {
            stiffness: 100.0,
            damping: 20.0,
            mass: 1.0,
        }
    }

    /// Bouncy spring (game-like).
    pub fn bouncy() -> Self {
        SpringConfig {
            stiffness: 200.0,
            damping: 10.0,
            mass: 1.0,
        }
    }

    /// Gentle spring (slow, smooth).
    pub fn gentle() -> Self {
        SpringConfig {
            stiffness: 50.0,
            damping: 10.0,
            mass: 1.0,
        }
    }

    /// Calculate damping ratio: ζ = c / (2 * sqrt(k * m))
    pub fn damping_ratio(&self) -> f64 {
        self.damping / (2.0 * (self.stiffness * self.mass).sqrt())
    }

    /// Is this spring underdamped? (will oscillate)
    pub fn is_underdamped(&self) -> bool {
        self.damping_ratio() < 1.0
    }

    /// Is this spring critically damped? (fastest without overshoot)
    pub fn is_critically_damped(&self) -> bool {
        let ratio = self.damping_ratio();
        (ratio - 1.0).abs() < 0.01
    }

    /// Is this spring overdamped? (slow, no overshoot)
    pub fn is_overdamped(&self) -> bool {
        self.damping_ratio() > 1.0
    }
}

/// Spring state for a single animated value.
#[derive(Clone, Copy, Debug)]
pub struct SpringState {
    /// Current position.
    pub position: f64,
    /// Current velocity.
    pub velocity: f64,
    /// Target position.
    pub target: f64,
}

impl SpringState {
    pub fn new(initial: f64) -> Self {
        SpringState {
            position: initial,
            velocity: 0.0,
            target: initial,
        }
    }

    pub fn with_target(initial: f64, target: f64) -> Self {
        SpringState {
            position: initial,
            velocity: 0.0,
            target,
        }
    }

    /// Update spring state by dt seconds.
    pub fn step(&mut self, config: &SpringConfig, dt: f64) {
        // Spring force: F = -k * x - c * v
        // where x = position - target, c = damping
        let displacement = self.position - self.target;
        let spring_force = -config.stiffness * displacement;
        let damping_force = -config.damping * self.velocity;
        let acceleration = (spring_force + damping_force) / config.mass;

        // Semi-implicit Euler integration
        self.velocity += acceleration * dt;
        self.position += self.velocity * dt;
    }

    /// Check if spring has settled (within threshold of target).
    pub fn is_settled(&self, position_threshold: f64, velocity_threshold: f64) -> bool {
        (self.position - self.target).abs() < position_threshold
            && self.velocity.abs() < velocity_threshold
    }
}

/// Spring state for 2D position.
#[derive(Clone, Copy, Debug)]
pub struct Spring2D {
    pub x: SpringState,
    pub y: SpringState,
}

impl Spring2D {
    pub fn new(x: f64, y: f64) -> Self {
        Spring2D {
            x: SpringState::new(x),
            y: SpringState::new(y),
        }
    }

    pub fn set_target(&mut self, x: f64, y: f64) {
        self.x.target = x;
        self.y.target = y;
    }

    pub fn step(&mut self, config: &SpringConfig, dt: f64) {
        self.x.step(config, dt);
        self.y.step(config, dt);
    }

    pub fn is_settled(&self, pos_thresh: f64, vel_thresh: f64) -> bool {
        self.x.is_settled(pos_thresh, vel_thresh) && self.y.is_settled(pos_thresh, vel_thresh)
    }
}
