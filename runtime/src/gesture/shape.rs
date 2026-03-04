//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                                 // hydrogen // gesture // shape
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! # Shape and Pattern Gesture Recognition
//!
//! - Zigzag: Back and forth pattern (crossing out)
//! - Throw: Sharp acceleration then release
//! - Shape Recognition: Detect drawn letters/shapes (L, Z, O, check, X)

use super::common::*;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                        // recognized shapes
// ═══════════════════════════════════════════════════════════════════════════════

/// Shapes that can be recognized from drawn paths.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RecognizedShape {
    // Letters
    LetterL,
    LetterZ,
    LetterS,
    LetterO,
    LetterC,
    LetterV,
    LetterX,
    LetterN,
    LetterM,
    LetterW,

    // Symbols
    Checkmark,
    Cross, // X mark
    Circle,
    Triangle,
    Square,
    Star,
    Heart,
    Arrow,

    // Gestures
    Zigzag,
    Spiral,
    Wave,
    Lightning, // Z-shape but faster
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                         // zigzag gesture
// ═══════════════════════════════════════════════════════════════════════════════

/// State for zigzag gesture (crossing out).
#[derive(Clone, Debug)]
pub struct ZigzagState {
    /// Points collected during gesture.
    pub points: Vec<TimestampedPoint>,
    /// Number of direction reversals detected.
    pub reversal_count: u32,
    /// Last movement direction.
    pub last_direction: Option<ZigzagDirection>,
    /// Whether actively tracking.
    pub active: bool,
}

impl Default for ZigzagState {
    fn default() -> Self {
        ZigzagState {
            points: Vec::new(),
            reversal_count: 0,
            last_direction: None,
            active: false,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ZigzagDirection {
    Left,
    Right,
}

/// Configuration for zigzag gesture.
#[derive(Clone, Debug)]
pub struct ZigzagConfig {
    /// Minimum movement to register direction (pixels).
    pub min_movement: f64,
    /// Required reversals to trigger zigzag.
    pub required_reversals: u32,
    /// Maximum time for gesture (ms).
    pub max_duration_ms: f64,
}

impl Default for ZigzagConfig {
    fn default() -> Self {
        ZigzagConfig {
            min_movement: 30.0,
            required_reversals: 3,
            max_duration_ms: 1500.0,
        }
    }
}

/// Output action for zigzag gesture.
#[derive(Clone, Debug)]
pub enum ZigzagAction {
    Zigzag {
        reversals: u32,
        haptic: HapticFeedback,
    },
}

/// Result of stepping zigzag state machine.
pub struct ZigzagStepResult {
    pub state: ZigzagState,
    pub actions: Vec<ZigzagAction>,
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // throw gesture
// ═══════════════════════════════════════════════════════════════════════════════

/// State for throw gesture (sharp acceleration then release).
#[derive(Clone, Debug)]
pub enum ThrowState {
    Idle,
    Tracking {
        samples: Vec<TimestampedPoint>,
        peak_velocity: f64,
    },
    Thrown,
}

impl Default for ThrowState {
    fn default() -> Self {
        ThrowState::Idle
    }
}

/// Configuration for throw gesture.
#[derive(Clone, Debug)]
pub struct ThrowConfig {
    /// Minimum velocity to consider a throw (pixels/second).
    pub min_velocity: f64,
    /// Velocity must exceed this to trigger (pixels/second).
    pub throw_threshold: f64,
}

impl Default for ThrowConfig {
    fn default() -> Self {
        ThrowConfig {
            min_velocity: 500.0,
            throw_threshold: 1500.0,
        }
    }
}

/// Output action for throw gesture.
#[derive(Clone, Debug)]
pub enum ThrowAction {
    Throw {
        velocity: Point,
        direction: SwipeDirection,
        haptic: HapticFeedback,
    },
}

/// Result of stepping throw state machine.
pub struct ThrowStepResult {
    pub state: ThrowState,
    pub actions: Vec<ThrowAction>,
}
