//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                            // hydrogen // gesture // two_finger
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! # Two-Finger Gesture Recognition
//!
//! Pure state machines for two-finger gestures following the libevring pattern:
//!
//! ```text
//! step :: State -> Event -> (State, [Action])
//! ```
//!
//! ## Gestures Implemented
//!
//! - **Pinch**: Two-finger scale gesture
//! - **Rotate**: Two-finger rotation gesture
//!
//! ## Integration
//!
//! - Haptics: Each action includes haptic feedback descriptor
//! - Elevation: Gestures are elevation-aware
//!
//! ─────────────────────────────────────────────────────────────────────────────

use super::common::{clamp, normalize_angle, GestureTarget, HapticFeedback, Point, TwoFingerData};
use super::touch::GestureInput;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // pinch gesture
// ═══════════════════════════════════════════════════════════════════════════════

/// Configuration for pinch gesture recognition.
#[derive(Clone, Debug)]
pub struct PinchConfig {
    /// Minimum scale (e.g., 0.1 = 10% of original).
    pub min_scale: f64,
    /// Maximum scale (e.g., 10.0 = 1000% of original).
    pub max_scale: f64,
    /// Target element (optional).
    pub target: Option<GestureTarget>,
}

impl Default for PinchConfig {
    fn default() -> Self {
        PinchConfig {
            min_scale: 0.1,
            max_scale: 10.0,
            target: None,
        }
    }
}

/// Pinch gesture state.
#[derive(Clone, Debug)]
pub enum PinchState {
    /// No active gesture.
    Idle,
    /// Actively pinching.
    Active {
        initial_distance: f64,
        initial_scale: f64,
        current_scale: f64,
        center: Point,
    },
}

impl Default for PinchState {
    fn default() -> Self {
        PinchState::Idle
    }
}

/// Data included with pinch actions.
#[derive(Clone, Debug)]
pub struct PinchData {
    /// Current scale factor.
    pub scale: f64,
    /// Initial scale when gesture started.
    pub initial_scale: f64,
    /// Center point between fingers.
    pub center: Point,
    /// Distance between fingers.
    pub distance: f64,
}

/// Actions emitted by the pinch state machine.
#[derive(Clone, Debug)]
pub enum PinchAction {
    /// Pinch gesture started.
    Start {
        data: PinchData,
        haptic: HapticFeedback,
    },
    /// Pinch gesture updated.
    Update {
        data: PinchData,
        haptic: Option<HapticFeedback>,
    },
    /// Pinch gesture ended.
    End {
        data: PinchData,
        haptic: HapticFeedback,
    },
}

/// Result of a pinch state machine step.
#[derive(Clone, Debug)]
pub struct PinchStepResult {
    /// New state.
    pub state: PinchState,
    /// Actions to emit.
    pub actions: Vec<PinchAction>,
}

/// Pure state machine step for pinch gesture.
pub fn pinch_step(
    state: PinchState,
    input: &GestureInput,
    config: &PinchConfig,
) -> PinchStepResult {
    match (&state, input) {
        // Idle -> Active on two-finger start
        (PinchState::Idle, GestureInput::TwoFingerUpdate { data, .. }) => {
            let pinch_data = PinchData {
                scale: 1.0,
                initial_scale: 1.0,
                center: data.center,
                distance: data.distance,
            };
            PinchStepResult {
                state: PinchState::Active {
                    initial_distance: data.distance,
                    initial_scale: 1.0,
                    current_scale: 1.0,
                    center: data.center,
                },
                actions: vec![PinchAction::Start {
                    data: pinch_data,
                    haptic: HapticFeedback::light_tap(),
                }],
            }
        }

        // Active state updates
        (
            PinchState::Active {
                initial_distance,
                initial_scale,
                ..
            },
            GestureInput::TwoFingerUpdate { data, .. },
        ) => {
            let raw_scale = initial_scale * (data.distance / initial_distance);
            let clamped_scale = clamp(raw_scale, config.min_scale, config.max_scale);

            let pinch_data = PinchData {
                scale: clamped_scale,
                initial_scale: *initial_scale,
                center: data.center,
                distance: data.distance,
            };

            PinchStepResult {
                state: PinchState::Active {
                    initial_distance: *initial_distance,
                    initial_scale: *initial_scale,
                    current_scale: clamped_scale,
                    center: data.center,
                },
                actions: vec![PinchAction::Update {
                    data: pinch_data,
                    haptic: None,
                }],
            }
        }

        // Active -> Idle on two-finger end
        (
            PinchState::Active {
                initial_scale,
                current_scale,
                center,
                initial_distance,
            },
            GestureInput::TwoFingerEnd,
        ) => {
            let pinch_data = PinchData {
                scale: *current_scale,
                initial_scale: *initial_scale,
                center: *center,
                distance: *initial_distance,
            };
            PinchStepResult {
                state: PinchState::Idle,
                actions: vec![PinchAction::End {
                    data: pinch_data,
                    haptic: HapticFeedback::light_tap(),
                }],
            }
        }

        // Default: no state change
        _ => PinchStepResult {
            state,
            actions: vec![],
        },
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // rotate gesture
// ═══════════════════════════════════════════════════════════════════════════════

/// Configuration for rotate gesture recognition.
#[derive(Clone, Debug)]
pub struct RotateConfig {
    /// Minimum angle change (degrees) before gesture activates.
    pub threshold: f64,
    /// Target element (optional).
    pub target: Option<GestureTarget>,
}

impl Default for RotateConfig {
    fn default() -> Self {
        RotateConfig {
            threshold: 5.0,
            target: None,
        }
    }
}

/// Rotate gesture state.
#[derive(Clone, Debug)]
pub enum RotateState {
    /// No active gesture.
    Idle,
    /// Waiting for threshold.
    Pending {
        initial_angle: f64,
        initial_rotation: f64,
        center: Point,
        last_angle: f64,
        last_time: f64,
    },
    /// Actively rotating.
    Active {
        initial_angle: f64,
        initial_rotation: f64,
        current_rotation: f64,
        center: Point,
        angular_velocity: f64,
        last_angle: f64,
        last_time: f64,
    },
}

impl Default for RotateState {
    fn default() -> Self {
        RotateState::Idle
    }
}

/// Data included with rotate actions.
#[derive(Clone, Debug)]
pub struct RotateData {
    /// Current rotation (degrees).
    pub rotation: f64,
    /// Initial rotation when gesture started.
    pub initial_rotation: f64,
    /// Center point between fingers.
    pub center: Point,
    /// Angular velocity (degrees/second).
    pub velocity: f64,
}

/// Actions emitted by the rotate state machine.
#[derive(Clone, Debug)]
pub enum RotateAction {
    /// Rotate gesture started.
    Start {
        data: RotateData,
        haptic: HapticFeedback,
    },
    /// Rotate gesture updated.
    Update {
        data: RotateData,
        haptic: Option<HapticFeedback>,
    },
    /// Rotate gesture ended.
    End {
        data: RotateData,
        haptic: HapticFeedback,
    },
}

/// Result of a rotate state machine step.
#[derive(Clone, Debug)]
pub struct RotateStepResult {
    /// New state.
    pub state: RotateState,
    /// Actions to emit.
    pub actions: Vec<RotateAction>,
}

/// Pure state machine step for rotate gesture.
pub fn rotate_step(
    state: RotateState,
    input: &GestureInput,
    config: &RotateConfig,
) -> RotateStepResult {
    match (&state, input) {
        // Idle -> Pending on two-finger start
        (RotateState::Idle, GestureInput::TwoFingerUpdate { data, time_ms }) => RotateStepResult {
            state: RotateState::Pending {
                initial_angle: data.angle_degrees,
                initial_rotation: 0.0,
                center: data.center,
                last_angle: data.angle_degrees,
                last_time: *time_ms,
            },
            actions: vec![],
        },

        // Pending -> check threshold
        (
            RotateState::Pending {
                initial_angle,
                initial_rotation,
                last_angle,
                last_time,
                ..
            },
            GestureInput::TwoFingerUpdate { data, time_ms },
        ) => {
            let mut delta_angle = data.angle_degrees - initial_angle;
            delta_angle = normalize_angle(delta_angle);

            if delta_angle.abs() >= config.threshold {
                // Threshold exceeded — activate
                let dt_seconds = (time_ms - last_time) / 1000.0;
                let angular_velocity = if dt_seconds > 0.0 {
                    normalize_angle(data.angle_degrees - last_angle) / dt_seconds
                } else {
                    0.0
                };

                let rotation_data = RotateData {
                    rotation: *initial_rotation + delta_angle,
                    initial_rotation: *initial_rotation,
                    center: data.center,
                    velocity: angular_velocity,
                };

                RotateStepResult {
                    state: RotateState::Active {
                        initial_angle: *initial_angle,
                        initial_rotation: *initial_rotation,
                        current_rotation: *initial_rotation + delta_angle,
                        center: data.center,
                        angular_velocity,
                        last_angle: data.angle_degrees,
                        last_time: *time_ms,
                    },
                    actions: vec![RotateAction::Start {
                        data: rotation_data,
                        haptic: HapticFeedback::light_tap(),
                    }],
                }
            } else {
                // Still pending
                RotateStepResult {
                    state: RotateState::Pending {
                        initial_angle: *initial_angle,
                        initial_rotation: *initial_rotation,
                        center: data.center,
                        last_angle: data.angle_degrees,
                        last_time: *time_ms,
                    },
                    actions: vec![],
                }
            }
        }

        // Active state updates
        (
            RotateState::Active {
                initial_angle,
                initial_rotation,
                last_angle,
                last_time,
                ..
            },
            GestureInput::TwoFingerUpdate { data, time_ms },
        ) => {
            let mut delta_angle = data.angle_degrees - initial_angle;
            delta_angle = normalize_angle(delta_angle);

            let dt_seconds = (time_ms - last_time) / 1000.0;
            let angular_velocity = if dt_seconds > 0.0 {
                normalize_angle(data.angle_degrees - last_angle) / dt_seconds
            } else {
                0.0
            };

            let rotation_data = RotateData {
                rotation: *initial_rotation + delta_angle,
                initial_rotation: *initial_rotation,
                center: data.center,
                velocity: angular_velocity,
            };

            RotateStepResult {
                state: RotateState::Active {
                    initial_angle: *initial_angle,
                    initial_rotation: *initial_rotation,
                    current_rotation: *initial_rotation + delta_angle,
                    center: data.center,
                    angular_velocity,
                    last_angle: data.angle_degrees,
                    last_time: *time_ms,
                },
                actions: vec![RotateAction::Update {
                    data: rotation_data,
                    haptic: None,
                }],
            }
        }

        // Pending -> Idle on two-finger end
        (RotateState::Pending { .. }, GestureInput::TwoFingerEnd) => RotateStepResult {
            state: RotateState::Idle,
            actions: vec![],
        },

        // Active -> Idle on two-finger end
        (
            RotateState::Active {
                initial_rotation,
                current_rotation,
                center,
                angular_velocity,
                ..
            },
            GestureInput::TwoFingerEnd,
        ) => {
            let rotation_data = RotateData {
                rotation: *current_rotation,
                initial_rotation: *initial_rotation,
                center: *center,
                velocity: *angular_velocity,
            };
            RotateStepResult {
                state: RotateState::Idle,
                actions: vec![RotateAction::End {
                    data: rotation_data,
                    haptic: HapticFeedback::light_tap(),
                }],
            }
        }

        // Default: no state change
        _ => RotateStepResult {
            state,
            actions: vec![],
        },
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                         // two-finger utilities
// ═══════════════════════════════════════════════════════════════════════════════

/// Combined metrics from two-finger gesture data.
///
/// Provides unified view of pinch, rotate, and pan information
/// from a single two-finger interaction.
#[derive(Clone, Debug)]
pub struct TwoFingerMetrics {
    /// Scale factor relative to reference distance.
    pub scale: f64,
    /// Rotation in degrees relative to reference angle.
    pub rotation: f64,
    /// Center translation from reference center.
    pub translation: Point,
    /// Current center point.
    pub center: Point,
    /// Current finger distance.
    pub distance: f64,
}

impl TwoFingerMetrics {
    /// Compute metrics from two-finger data relative to a reference.
    ///
    /// This provides a unified view of all two-finger gesture components.
    pub fn from_data(current: &TwoFingerData, reference: &TwoFingerData) -> Self {
        let scale = if reference.distance > 0.0 {
            current.distance / reference.distance
        } else {
            1.0
        };

        let rotation = normalize_angle(current.angle_degrees - reference.angle_degrees);

        let translation = Point {
            x: current.center.x - reference.center.x,
            y: current.center.y - reference.center.y,
        };

        TwoFingerMetrics {
            scale,
            rotation,
            translation,
            center: current.center,
            distance: current.distance,
        }
    }

    /// Check if scale has changed significantly.
    pub fn has_significant_scale(&self, threshold: f64) -> bool {
        (self.scale - 1.0).abs() >= threshold
    }

    /// Check if rotation has changed significantly.
    pub fn has_significant_rotation(&self, threshold_degrees: f64) -> bool {
        self.rotation.abs() >= threshold_degrees
    }

    /// Check if translation has changed significantly.
    pub fn has_significant_translation(&self, threshold_pixels: f64) -> bool {
        let distance = (self.translation.x * self.translation.x
            + self.translation.y * self.translation.y)
            .sqrt();
        distance >= threshold_pixels
    }
}
