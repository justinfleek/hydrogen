//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                        // hydrogen // runtime // core // spring
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! # Pure Spring Physics
//!
//! **Zero JavaScript. Zero browser APIs. Zero side effects.**
//!
//! Physics-based animation using the damped harmonic oscillator model.
//! This module matches the PureScript `Hydrogen.Schema.Temporal.Spring` types.
//!
//! ## The Spring Model
//!
//! Based on the damped harmonic oscillator equation:
//!
//! ```text
//! F = -kx - cv + ma
//! ```
//!
//! Where:
//! - **k** = stiffness (spring constant, higher = snappier)
//! - **c** = damping (friction, higher = less bouncy)
//! - **m** = mass (inertia, higher = slower response)
//! - **v** = velocity (current rate of change)
//! - **x** = displacement (distance from target)
//!
//! ## Damping Ratio
//!
//! The damping ratio ζ = c / (2√(km)) determines behavior:
//!
//! - **ζ < 1**: Underdamped (oscillates/bounces)
//! - **ζ = 1**: Critically damped (fastest settle, no overshoot)
//! - **ζ > 1**: Overdamped (slow settle, no overshoot)
//!
//! ## Usage
//!
//! ```rust,ignore
//! let mut state = SpringState::new(0.0, 100.0); // from 0 to 100
//! let config = SpringConfig::STIFF;
//!
//! // Each frame:
//! state.step(&config, delta_seconds);
//! let current_value = state.position;
//! let is_done = state.is_settled(&config);
//! ```
//!
//! ## Relationship to PureScript Schema
//!
//! This module corresponds to:
//! - `Hydrogen.Schema.Temporal.Spring` (atoms: Mass, Stiffness, Damping, etc.)
//! - `Hydrogen.Schema.Temporal.SpringConfig` (molecule)

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // spring config
// ═══════════════════════════════════════════════════════════════════════════════

/// Spring physics configuration.
///
/// Defines the physical properties of a spring: how stiff it is, how much
/// it dampens, and how heavy the attached mass is.
///
/// All values are bounded to prevent invalid physics:
/// - `stiffness`: 0.01 to 10000.0
/// - `damping`: 0.0 to 1000.0
/// - `mass`: 0.01 to 1000.0
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct SpringConfig {
    /// Spring constant k (stiffness).
    /// Higher = faster oscillation, snappier feel.
    /// Typical range: 100-500.
    pub stiffness: f64,

    /// Damping coefficient c.
    /// Higher = less bouncy, faster settle.
    /// Typical range: 10-50.
    pub damping: f64,

    /// Mass of the attached object.
    /// Higher = slower acceleration/deceleration.
    /// Typical: 1.0.
    pub mass: f64,

    /// Rest threshold for position (displacement from target).
    /// Animation is "settled" when both position and velocity are below thresholds.
    pub rest_delta: f64,

    /// Rest threshold for velocity.
    /// Animation is "settled" when both position and velocity are below thresholds.
    pub rest_velocity: f64,
}

impl Default for SpringConfig {
    fn default() -> Self {
        SpringConfig::DEFAULT
    }
}

impl SpringConfig {
    // ─────────────────────────────────────────────────────────────── Constants

    /// Default spring (balanced, slightly bouncy).
    pub const DEFAULT: SpringConfig = SpringConfig {
        stiffness: 170.0,
        damping: 26.0,
        mass: 1.0,
        rest_delta: 0.01,
        rest_velocity: 0.01,
    };

    /// Gentle spring: slow, smooth, minimal bounce.
    /// Good for: background elements, subtle transitions.
    pub const GENTLE: SpringConfig = SpringConfig {
        stiffness: 120.0,
        damping: 14.0,
        mass: 1.0,
        rest_delta: 0.01,
        rest_velocity: 0.01,
    };

    /// Wobbly spring: fast, bouncy, playful.
    /// Good for: playful UI, notifications, attention-grabbing.
    pub const WOBBLY: SpringConfig = SpringConfig {
        stiffness: 180.0,
        damping: 12.0,
        mass: 1.0,
        rest_delta: 0.01,
        rest_velocity: 0.01,
    };

    /// Stiff spring: snappy, responsive, minimal overshoot.
    /// Good for: buttons, toggles, responsive UI.
    pub const STIFF: SpringConfig = SpringConfig {
        stiffness: 400.0,
        damping: 30.0,
        mass: 1.0,
        rest_delta: 0.01,
        rest_velocity: 0.01,
    };

    /// Slow spring: dramatic, lazy motion.
    /// Good for: page transitions, hero animations.
    pub const SLOW: SpringConfig = SpringConfig {
        stiffness: 100.0,
        damping: 20.0,
        mass: 1.0,
        rest_delta: 0.01,
        rest_velocity: 0.01,
    };

    /// Molasses spring: very slow, syrupy feel.
    /// Good for: dramatic reveals, emphasis.
    pub const MOLASSES: SpringConfig = SpringConfig {
        stiffness: 80.0,
        damping: 25.0,
        mass: 1.0,
        rest_delta: 0.01,
        rest_velocity: 0.01,
    };

    /// iOS-style spring (slightly bouncy, quick settle).
    pub const IOS: SpringConfig = SpringConfig {
        stiffness: 300.0,
        damping: 30.0,
        mass: 1.0,
        rest_delta: 0.01,
        rest_velocity: 0.01,
    };

    // ─────────────────────────────────────────────────────────────── Constructor

    /// Create a new spring configuration with bounds validation.
    ///
    /// Values are clamped to valid ranges:
    /// - stiffness: [0.01, 10000.0]
    /// - damping: [0.0, 1000.0]
    /// - mass: [0.01, 1000.0]
    pub fn new(stiffness: f64, damping: f64, mass: f64) -> Self {
        SpringConfig {
            stiffness: stiffness.clamp(0.01, 10000.0),
            damping: damping.clamp(0.0, 1000.0),
            mass: mass.clamp(0.01, 1000.0),
            rest_delta: 0.01,
            rest_velocity: 0.01,
        }
    }

    /// Create with custom rest thresholds.
    pub fn with_rest_thresholds(
        stiffness: f64,
        damping: f64,
        mass: f64,
        rest_delta: f64,
        rest_velocity: f64,
    ) -> Self {
        SpringConfig {
            stiffness: stiffness.clamp(0.01, 10000.0),
            damping: damping.clamp(0.0, 1000.0),
            mass: mass.clamp(0.01, 1000.0),
            rest_delta: rest_delta.clamp(0.0001, 100.0),
            rest_velocity: rest_velocity.clamp(0.0001, 100.0),
        }
    }

    /// Create a critically damped spring (fastest settle without overshoot).
    ///
    /// Critical damping = 2 × √(mass × stiffness)
    pub fn critically_damped(stiffness: f64, mass: f64) -> Self {
        let stiffness = stiffness.clamp(0.01, 10000.0);
        let mass = mass.clamp(0.01, 1000.0);
        let critical_damping = 2.0 * (mass * stiffness).sqrt();

        SpringConfig {
            stiffness,
            damping: critical_damping,
            mass,
            rest_delta: 0.01,
            rest_velocity: 0.01,
        }
    }

    // ─────────────────────────────────────────────────────────────── Properties

    /// Calculate the damping ratio ζ = c / (2√(km)).
    ///
    /// - ζ < 1: Underdamped (oscillates)
    /// - ζ = 1: Critically damped (fastest non-oscillating)
    /// - ζ > 1: Overdamped (slow, non-oscillating)
    pub fn damping_ratio(&self) -> f64 {
        let critical = 2.0 * (self.mass * self.stiffness).sqrt();
        if critical > 0.0 {
            self.damping / critical
        } else {
            1.0 // Fallback for edge cases
        }
    }

    /// Calculate the natural (undamped) frequency ω₀ = √(k/m).
    ///
    /// This is the frequency at which the spring would oscillate
    /// with zero damping (in radians per second).
    pub fn natural_frequency(&self) -> f64 {
        (self.stiffness / self.mass).sqrt()
    }

    /// Calculate the damped frequency ωd = ω₀√(1 - ζ²).
    ///
    /// This is the actual oscillation frequency for underdamped springs.
    /// Returns 0 for critically/overdamped springs.
    pub fn damped_frequency(&self) -> f64 {
        let zeta = self.damping_ratio();
        if zeta >= 1.0 {
            0.0
        } else {
            self.natural_frequency() * (1.0 - zeta * zeta).sqrt()
        }
    }

    /// Check if spring is underdamped (will oscillate/bounce).
    pub fn is_underdamped(&self) -> bool {
        self.damping_ratio() < 1.0
    }

    /// Check if spring is overdamped (slow settle, no oscillation).
    pub fn is_overdamped(&self) -> bool {
        self.damping_ratio() > 1.0
    }

    /// Check if spring is critically damped (fastest settle without oscillation).
    pub fn is_critically_damped(&self) -> bool {
        let ratio = self.damping_ratio();
        ratio > 0.99 && ratio < 1.01
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // spring state
// ═══════════════════════════════════════════════════════════════════════════════

/// State of a spring-animated value.
///
/// Represents the current position, velocity, and target of a spring animation.
/// Call `step()` each frame to advance the simulation.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct SpringState {
    /// Current position (animated value).
    pub position: f64,

    /// Current velocity (rate of change per second).
    pub velocity: f64,

    /// Target position (where the spring is pulling toward).
    pub target: f64,
}

impl Default for SpringState {
    fn default() -> Self {
        SpringState::new(0.0, 0.0)
    }
}

impl SpringState {
    /// Create a new spring state at rest.
    ///
    /// Position and target are both set to the initial value.
    pub fn new(initial: f64, target: f64) -> Self {
        SpringState {
            position: initial,
            velocity: 0.0,
            target,
        }
    }

    /// Create spring state at a position, with the same target.
    pub fn at(position: f64) -> Self {
        SpringState {
            position,
            velocity: 0.0,
            target: position,
        }
    }

    /// Create spring state with initial velocity (for "throwing" animations).
    pub fn with_velocity(position: f64, target: f64, velocity: f64) -> Self {
        SpringState {
            position,
            velocity,
            target,
        }
    }

    /// Set a new target, keeping current position and velocity.
    ///
    /// This is how you animate to a new value: just change the target.
    pub fn set_target(&mut self, target: f64) {
        self.target = target;
    }

    /// Jump immediately to a position (resets velocity).
    ///
    /// Use when you need to teleport without animation.
    pub fn jump_to(&mut self, position: f64) {
        self.position = position;
        self.velocity = 0.0;
    }

    /// Jump to target immediately (ends animation).
    pub fn snap_to_target(&mut self) {
        self.position = self.target;
        self.velocity = 0.0;
    }

    /// Advance the spring simulation by `dt` seconds.
    ///
    /// Uses semi-implicit Euler integration for stability.
    ///
    /// # Arguments
    ///
    /// * `config` - Spring configuration (stiffness, damping, mass)
    /// * `dt` - Time step in seconds (e.g., 0.016 for 60fps)
    pub fn step(&mut self, config: &SpringConfig, dt: f64) {
        // Clamp dt to prevent instability with large time steps
        let dt = dt.clamp(0.0, 0.1);

        if dt <= 0.0 {
            return;
        }

        // Spring force: F = -k * x
        let displacement = self.position - self.target;
        let spring_force = -config.stiffness * displacement;

        // Damping force: F = -c * v
        let damping_force = -config.damping * self.velocity;

        // Total acceleration: a = F / m
        let acceleration = (spring_force + damping_force) / config.mass;

        // Semi-implicit Euler integration:
        // First update velocity, then use new velocity to update position
        self.velocity += acceleration * dt;
        self.position += self.velocity * dt;

        // Snap to target if very close (prevents floating-point drift)
        if self.is_settled(config) {
            self.position = self.target;
            self.velocity = 0.0;
        }
    }

    /// Check if the spring has settled to its target.
    ///
    /// Returns true when both position and velocity are below thresholds.
    pub fn is_settled(&self, config: &SpringConfig) -> bool {
        let displacement = (self.position - self.target).abs();
        let velocity = self.velocity.abs();

        displacement < config.rest_delta && velocity < config.rest_velocity
    }

    /// Get the current displacement from target.
    pub fn displacement(&self) -> f64 {
        self.position - self.target
    }

    /// Get the progress toward target (0 = at start, 1 = at target).
    ///
    /// Note: May exceed 1.0 or be negative for overshooting springs.
    pub fn progress(&self, start: f64) -> f64 {
        let total = self.target - start;
        if total.abs() < 1e-10 {
            1.0 // Already at target
        } else {
            (self.position - start) / total
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // spring 2d
// ═══════════════════════════════════════════════════════════════════════════════

/// State of a 2D spring-animated point.
///
/// Useful for animating positions, sizes, or any 2D vector.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Spring2D {
    /// X-axis spring state.
    pub x: SpringState,
    /// Y-axis spring state.
    pub y: SpringState,
}

impl Default for Spring2D {
    fn default() -> Self {
        Spring2D::new(0.0, 0.0, 0.0, 0.0)
    }
}

impl Spring2D {
    /// Create a new 2D spring state.
    pub fn new(x: f64, y: f64, target_x: f64, target_y: f64) -> Self {
        Spring2D {
            x: SpringState::new(x, target_x),
            y: SpringState::new(y, target_y),
        }
    }

    /// Create at a position with same target.
    pub fn at(x: f64, y: f64) -> Self {
        Spring2D {
            x: SpringState::at(x),
            y: SpringState::at(y),
        }
    }

    /// Set new target position.
    pub fn set_target(&mut self, x: f64, y: f64) {
        self.x.set_target(x);
        self.y.set_target(y);
    }

    /// Jump immediately to a position.
    pub fn jump_to(&mut self, x: f64, y: f64) {
        self.x.jump_to(x);
        self.y.jump_to(y);
    }

    /// Snap to target immediately.
    pub fn snap_to_target(&mut self) {
        self.x.snap_to_target();
        self.y.snap_to_target();
    }

    /// Advance the simulation.
    pub fn step(&mut self, config: &SpringConfig, dt: f64) {
        self.x.step(config, dt);
        self.y.step(config, dt);
    }

    /// Check if both axes have settled.
    pub fn is_settled(&self, config: &SpringConfig) -> bool {
        self.x.is_settled(config) && self.y.is_settled(config)
    }

    /// Get current position as tuple.
    pub fn position(&self) -> (f64, f64) {
        (self.x.position, self.y.position)
    }

    /// Get target position as tuple.
    pub fn target(&self) -> (f64, f64) {
        (self.x.target, self.y.target)
    }

    /// Get distance from target.
    pub fn distance_to_target(&self) -> f64 {
        let dx = self.x.displacement();
        let dy = self.y.displacement();
        (dx * dx + dy * dy).sqrt()
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // spring 3d
// ═══════════════════════════════════════════════════════════════════════════════

/// State of a 3D spring-animated point.
///
/// Useful for 3D position animations, camera movements, etc.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Spring3D {
    /// X-axis spring state.
    pub x: SpringState,
    /// Y-axis spring state.
    pub y: SpringState,
    /// Z-axis spring state.
    pub z: SpringState,
}

impl Default for Spring3D {
    fn default() -> Self {
        Spring3D::at(0.0, 0.0, 0.0)
    }
}

impl Spring3D {
    /// Create a new 3D spring state.
    pub fn new(x: f64, y: f64, z: f64, target_x: f64, target_y: f64, target_z: f64) -> Self {
        Spring3D {
            x: SpringState::new(x, target_x),
            y: SpringState::new(y, target_y),
            z: SpringState::new(z, target_z),
        }
    }

    /// Create at a position with same target.
    pub fn at(x: f64, y: f64, z: f64) -> Self {
        Spring3D {
            x: SpringState::at(x),
            y: SpringState::at(y),
            z: SpringState::at(z),
        }
    }

    /// Set new target position.
    pub fn set_target(&mut self, x: f64, y: f64, z: f64) {
        self.x.set_target(x);
        self.y.set_target(y);
        self.z.set_target(z);
    }

    /// Jump immediately to a position.
    pub fn jump_to(&mut self, x: f64, y: f64, z: f64) {
        self.x.jump_to(x);
        self.y.jump_to(y);
        self.z.jump_to(z);
    }

    /// Snap to target immediately.
    pub fn snap_to_target(&mut self) {
        self.x.snap_to_target();
        self.y.snap_to_target();
        self.z.snap_to_target();
    }

    /// Advance the simulation.
    pub fn step(&mut self, config: &SpringConfig, dt: f64) {
        self.x.step(config, dt);
        self.y.step(config, dt);
        self.z.step(config, dt);
    }

    /// Check if all axes have settled.
    pub fn is_settled(&self, config: &SpringConfig) -> bool {
        self.x.is_settled(config) && self.y.is_settled(config) && self.z.is_settled(config)
    }

    /// Get current position as tuple.
    pub fn position(&self) -> (f64, f64, f64) {
        (self.x.position, self.y.position, self.z.position)
    }

    /// Get target position as tuple.
    pub fn target(&self) -> (f64, f64, f64) {
        (self.x.target, self.y.target, self.z.target)
    }

    /// Get distance from target.
    pub fn distance_to_target(&self) -> f64 {
        let dx = self.x.displacement();
        let dy = self.y.displacement();
        let dz = self.z.displacement();
        (dx * dx + dy * dy + dz * dz).sqrt()
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                      // tests
// ═══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_spring_config_defaults() {
        let config = SpringConfig::DEFAULT;
        assert!(config.stiffness > 0.0);
        assert!(config.damping > 0.0);
        assert!(config.mass > 0.0);
    }

    #[test]
    fn test_damping_ratio() {
        // Critically damped: ζ = 1
        let critical = SpringConfig::critically_damped(100.0, 1.0);
        assert!((critical.damping_ratio() - 1.0).abs() < 0.01);

        // Underdamped: ζ < 1
        let wobbly = SpringConfig::WOBBLY;
        assert!(wobbly.is_underdamped());

        // With high damping: overdamped
        let over = SpringConfig::new(100.0, 100.0, 1.0);
        assert!(over.is_overdamped());
    }

    #[test]
    fn test_spring_converges() {
        let config = SpringConfig::STIFF;
        let mut state = SpringState::new(0.0, 100.0);

        // Run simulation for 2 seconds at 60fps
        for _ in 0..120 {
            state.step(&config, 1.0 / 60.0);
        }

        assert!(state.is_settled(&config), "Spring should have settled");
        assert!(
            (state.position - 100.0).abs() < 0.1,
            "Position should be near target"
        );
    }

    #[test]
    fn test_underdamped_overshoots() {
        let config = SpringConfig::WOBBLY;
        let mut state = SpringState::new(0.0, 100.0);
        let mut max_position: f64 = 0.0;

        // Run simulation
        for frame in 0..120 {
            state.step(&config, 1.0 / 60.0);
            max_position = max_position.max(state.position);
            // frame available for debugging
            if frame == 119 && max_position <= 100.0 {
                log::trace!("Final frame {}, max_position {}", frame, max_position);
            }
        }

        // Underdamped spring should overshoot target
        assert!(
            max_position > 100.0,
            "Wobbly spring should overshoot, max was {}",
            max_position
        );
    }

    #[test]
    fn test_overdamped_no_overshoot() {
        let config = SpringConfig::new(100.0, 50.0, 1.0); // Overdamped
        let mut state = SpringState::new(0.0, 100.0);
        let mut max_position: f64 = 0.0;

        // Run simulation
        for frame in 0..300 {
            // Overdamped is slower
            state.step(&config, 1.0 / 60.0);
            max_position = max_position.max(state.position);
            // frame available for debugging
            if frame == 299 && max_position > 100.0 + config.rest_delta {
                log::trace!("Final frame {}, max_position {}", frame, max_position);
            }
        }

        // Overdamped spring should not overshoot
        assert!(
            max_position <= 100.0 + config.rest_delta,
            "Overdamped spring should not overshoot, max was {}",
            max_position
        );
    }

    #[test]
    fn test_spring_2d() {
        let config = SpringConfig::STIFF;
        let mut spring = Spring2D::new(0.0, 0.0, 100.0, 100.0);

        for _ in 0..120 {
            spring.step(&config, 1.0 / 60.0);
        }

        assert!(spring.is_settled(&config));
        let (x, y) = spring.position();
        assert!((x - 100.0).abs() < 0.1);
        assert!((y - 100.0).abs() < 0.1);
    }

    #[test]
    fn test_spring_3d() {
        let config = SpringConfig::STIFF;
        let mut spring = Spring3D::new(0.0, 0.0, 0.0, 50.0, 50.0, 50.0);

        for _ in 0..120 {
            spring.step(&config, 1.0 / 60.0);
        }

        assert!(spring.is_settled(&config));
        let (x, y, z) = spring.position();
        assert!((x - 50.0).abs() < 0.1);
        assert!((y - 50.0).abs() < 0.1);
        assert!((z - 50.0).abs() < 0.1);
    }

    #[test]
    fn test_set_target_mid_animation() {
        let config = SpringConfig::STIFF;
        let mut state = SpringState::new(0.0, 100.0);

        // Animate halfway
        for _ in 0..30 {
            state.step(&config, 1.0 / 60.0);
        }

        // Change target mid-animation
        state.set_target(50.0);

        // Continue animation
        for _ in 0..90 {
            state.step(&config, 1.0 / 60.0);
        }

        assert!(state.is_settled(&config));
        assert!(
            (state.position - 50.0).abs() < 0.1,
            "Should have settled to new target"
        );
    }

    #[test]
    fn test_initial_velocity() {
        let config = SpringConfig::GENTLE;
        let mut state = SpringState::with_velocity(0.0, 0.0, 500.0);

        // With initial velocity, should overshoot even with zero displacement
        let mut max_position: f64 = 0.0;
        for frame in 0..120 {
            state.step(&config, 1.0 / 60.0);
            max_position = max_position.max(state.position);
            // frame available for debugging
            if frame == 119 && max_position <= 10.0 {
                log::trace!("Final frame {}, max_position {}", frame, max_position);
            }
        }

        assert!(
            max_position > 10.0,
            "Initial velocity should cause movement"
        );
        assert!(state.is_settled(&config));
    }

    #[test]
    fn test_jump_to() {
        let config = SpringConfig::STIFF;
        let mut state = SpringState::new(0.0, 100.0);

        // Animate a bit
        for _ in 0..30 {
            state.step(&config, 1.0 / 60.0);
        }

        // Jump to new position
        state.jump_to(200.0);
        assert_eq!(state.position, 200.0);
        assert_eq!(state.velocity, 0.0);
    }

    #[test]
    fn test_snap_to_target() {
        let mut state = SpringState::new(0.0, 100.0);
        state.velocity = 50.0; // Some velocity

        state.snap_to_target();

        assert_eq!(state.position, 100.0);
        assert_eq!(state.velocity, 0.0);
    }

    #[test]
    fn test_config_bounds() {
        // Values should be clamped to valid ranges
        let config = SpringConfig::new(-100.0, -50.0, -1.0);
        assert!(config.stiffness >= 0.01);
        assert!(config.damping >= 0.0);
        assert!(config.mass >= 0.01);

        let config2 = SpringConfig::new(100000.0, 10000.0, 10000.0);
        assert!(config2.stiffness <= 10000.0);
        assert!(config2.damping <= 1000.0);
        assert!(config2.mass <= 1000.0);
    }
}
