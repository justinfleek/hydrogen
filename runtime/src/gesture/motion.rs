//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                                 // hydrogen // gesture // motion
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! # Device Motion Gesture Recognition
//!
//! Pure state machines for device sensor gestures following the libevring pattern:
//!
//! ```text
//! step :: State -> Event -> (State, [Action])
//! ```
//!
//! ## Gestures Implemented
//!
//! - **Shake**: Device shaken (rapid acceleration reversals)
//! - **Tilt**: Device tilted beyond threshold (sustained orientation)
//! - **BarrelRoll**: 360° rotation around forward axis
//! - **Flip**: Device flipped over (180° rotation)
//!
//! ## Sensor Input
//!
//! Uses accelerometer and gyroscope data from device sensors.
//! On web: DeviceMotionEvent and DeviceOrientationEvent
//! The runtime translates these to MotionInput events.
//!
//! ─────────────────────────────────────────────────────────────────────────────

use super::common::{clamp, HapticFeedback, Point3D, Quaternion};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // motion input
// ═══════════════════════════════════════════════════════════════════════════════

/// Input events from device motion sensors.
///
/// On web, these come from DeviceMotionEvent (acceleration) and
/// DeviceOrientationEvent (rotation). The runtime translates raw
/// browser events into these normalized inputs.
#[derive(Clone, Debug)]
pub enum MotionInput {
    /// Acceleration update (from accelerometer).
    /// Values in m/s², with gravity removed if available.
    Acceleration {
        /// Linear acceleration (gravity removed).
        acceleration: Point3D,
        /// Acceleration including gravity.
        acceleration_with_gravity: Point3D,
        /// Timestamp in milliseconds.
        time_ms: f64,
    },
    /// Absolute orientation as quaternion (from sensor fusion).
    /// Available on devices with RelativeOrientationSensor / AbsoluteOrientationSensor.
    /// More accurate than Euler angles for continuous tracking.
    AbsoluteOrientation {
        /// Device orientation as quaternion.
        orientation: Quaternion,
        /// Timestamp in milliseconds.
        time_ms: f64,
    },
    /// Rotation rate update (from gyroscope).
    /// Values in degrees/second.
    RotationRate {
        /// Rotation rate around X axis (degrees/second).
        alpha: f64,
        /// Rotation rate around Y axis (degrees/second).
        beta: f64,
        /// Rotation rate around Z axis (degrees/second).
        gamma: f64,
        /// Timestamp in milliseconds.
        time_ms: f64,
    },
    /// Device orientation update.
    /// Euler angles relative to Earth coordinate frame.
    Orientation {
        /// Rotation around Z axis (0-360, compass direction).
        alpha: f64,
        /// Rotation around X axis (-180 to 180, front-back tilt).
        beta: f64,
        /// Rotation around Y axis (-90 to 90, left-right tilt).
        gamma: f64,
        /// Timestamp in milliseconds.
        time_ms: f64,
    },
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // shake gesture
// ═══════════════════════════════════════════════════════════════════════════════

/// Configuration for shake gesture recognition.
#[derive(Clone, Debug)]
pub struct ShakeConfig {
    /// Minimum acceleration magnitude to register a shake (m/s²).
    pub acceleration_threshold: f64,
    /// Required direction reversals to trigger shake.
    pub required_reversals: u32,
    /// Maximum time window for shake gesture (ms).
    pub time_window_ms: f64,
    /// Minimum time between shake detections (ms).
    pub cooldown_ms: f64,
}

impl Default for ShakeConfig {
    fn default() -> Self {
        ShakeConfig {
            acceleration_threshold: 15.0, // ~1.5g
            required_reversals: 3,
            time_window_ms: 500.0,
            cooldown_ms: 500.0,
        }
    }
}

/// Direction of acceleration for shake detection.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ShakeDirection {
    Positive,
    Negative,
    Neutral,
}

/// Shake gesture state.
#[derive(Clone, Debug)]
pub struct ShakeState {
    /// Number of direction reversals detected.
    pub reversal_count: u32,
    /// Last detected direction.
    pub last_direction: ShakeDirection,
    /// Time of first reversal in current sequence (ms).
    pub sequence_start_ms: f64,
    /// Time of last shake detection (for cooldown).
    pub last_shake_ms: f64,
}

impl Default for ShakeState {
    fn default() -> Self {
        ShakeState {
            reversal_count: 0,
            last_direction: ShakeDirection::Neutral,
            sequence_start_ms: 0.0,
            last_shake_ms: 0.0,
        }
    }
}

/// Data included with shake actions.
#[derive(Clone, Debug)]
pub struct ShakeData {
    /// Number of reversals detected.
    pub reversals: u32,
    /// Peak acceleration magnitude during shake.
    pub peak_acceleration: f64,
}

/// Actions emitted by the shake state machine.
#[derive(Clone, Debug)]
pub enum ShakeAction {
    /// Shake detected.
    Detected {
        data: ShakeData,
        haptic: HapticFeedback,
    },
}

/// Result of a shake state machine step.
#[derive(Clone, Debug)]
pub struct ShakeStepResult {
    /// New state.
    pub state: ShakeState,
    /// Actions to emit.
    pub actions: Vec<ShakeAction>,
}

/// Pure state machine step for shake gesture.
pub fn shake_step(state: ShakeState, input: &MotionInput, config: &ShakeConfig) -> ShakeStepResult {
    match input {
        MotionInput::Acceleration {
            acceleration,
            time_ms,
            ..
        } => {
            // Check cooldown
            if *time_ms - state.last_shake_ms < config.cooldown_ms {
                return ShakeStepResult {
                    state,
                    actions: vec![],
                };
            }

            // Use X-axis as primary shake axis (left-right motion)
            let accel_x = acceleration.x;
            let magnitude = acceleration.magnitude();

            // Determine current direction
            let current_direction = if magnitude < config.acceleration_threshold {
                ShakeDirection::Neutral
            } else if accel_x > 0.0 {
                ShakeDirection::Positive
            } else {
                ShakeDirection::Negative
            };

            // Check for reversal
            let is_reversal = matches!(
                (state.last_direction, current_direction),
                (ShakeDirection::Positive, ShakeDirection::Negative)
                    | (ShakeDirection::Negative, ShakeDirection::Positive)
            );

            if is_reversal {
                let new_count = state.reversal_count + 1;
                let sequence_start = if state.reversal_count == 0 {
                    *time_ms
                } else {
                    state.sequence_start_ms
                };

                // Check if within time window
                if *time_ms - sequence_start > config.time_window_ms {
                    // Window expired, start new sequence
                    return ShakeStepResult {
                        state: ShakeState {
                            reversal_count: 1,
                            last_direction: current_direction,
                            sequence_start_ms: *time_ms,
                            last_shake_ms: state.last_shake_ms,
                        },
                        actions: vec![],
                    };
                }

                // Check if shake detected
                if new_count >= config.required_reversals {
                    return ShakeStepResult {
                        state: ShakeState {
                            reversal_count: 0,
                            last_direction: ShakeDirection::Neutral,
                            sequence_start_ms: 0.0,
                            last_shake_ms: *time_ms,
                        },
                        actions: vec![ShakeAction::Detected {
                            data: ShakeData {
                                reversals: new_count,
                                peak_acceleration: magnitude,
                            },
                            haptic: HapticFeedback::success(),
                        }],
                    };
                }

                // Continue building sequence
                ShakeStepResult {
                    state: ShakeState {
                        reversal_count: new_count,
                        last_direction: current_direction,
                        sequence_start_ms: sequence_start,
                        last_shake_ms: state.last_shake_ms,
                    },
                    actions: vec![],
                }
            } else if current_direction != ShakeDirection::Neutral {
                // Update direction without counting reversal
                ShakeStepResult {
                    state: ShakeState {
                        last_direction: current_direction,
                        ..state
                    },
                    actions: vec![],
                }
            } else {
                // No change
                ShakeStepResult {
                    state,
                    actions: vec![],
                }
            }
        }
        // Ignore non-acceleration inputs for shake
        _ => ShakeStepResult {
            state,
            actions: vec![],
        },
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // tilt gesture
// ═══════════════════════════════════════════════════════════════════════════════

/// Tilt direction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TiltDirection {
    /// Forward tilt (top of device moving away from user).
    Forward,
    /// Backward tilt (top of device moving toward user).
    Backward,
    /// Left tilt.
    Left,
    /// Right tilt.
    Right,
}

/// Configuration for tilt gesture recognition.
#[derive(Clone, Debug)]
pub struct TiltConfig {
    /// Angle threshold to trigger tilt (degrees).
    pub angle_threshold: f64,
    /// Time device must be held at angle (ms).
    pub hold_duration_ms: f64,
    /// Angle at which tilt ends (degrees, hysteresis).
    pub release_threshold: f64,
}

impl Default for TiltConfig {
    fn default() -> Self {
        TiltConfig {
            angle_threshold: 30.0,
            hold_duration_ms: 200.0,
            release_threshold: 15.0,
        }
    }
}

/// Tilt gesture state.
#[derive(Clone, Debug)]
pub enum TiltState {
    /// No tilt detected.
    Idle,
    /// Tilted beyond threshold, waiting for hold duration.
    Pending {
        direction: TiltDirection,
        angle: f64,
        start_time_ms: f64,
    },
    /// Actively tilted.
    Tilted {
        direction: TiltDirection,
        angle: f64,
    },
}

impl Default for TiltState {
    fn default() -> Self {
        TiltState::Idle
    }
}

/// Data included with tilt actions.
#[derive(Clone, Debug)]
pub struct TiltData {
    /// Tilt direction.
    pub direction: TiltDirection,
    /// Tilt angle in degrees.
    pub angle: f64,
}

/// Actions emitted by the tilt state machine.
#[derive(Clone, Debug)]
pub enum TiltAction {
    /// Tilt started.
    Start {
        data: TiltData,
        haptic: HapticFeedback,
    },
    /// Tilt angle updated.
    Update { data: TiltData },
    /// Tilt ended.
    End {
        data: TiltData,
        haptic: HapticFeedback,
    },
}

/// Result of a tilt state machine step.
#[derive(Clone, Debug)]
pub struct TiltStepResult {
    /// New state.
    pub state: TiltState,
    /// Actions to emit.
    pub actions: Vec<TiltAction>,
}

/// Detect tilt direction from orientation angles.
/// Returns the direction and angle (clamped to sensible bounds).
fn detect_tilt_direction(beta: f64, gamma: f64, threshold: f64) -> Option<(TiltDirection, f64)> {
    // Beta: front-back tilt (-180 to 180)
    // Gamma: left-right tilt (-90 to 90)
    // Clamp angles to valid bounds to handle sensor noise

    let clamped_beta = clamp(beta, -180.0, 180.0);
    let clamped_gamma = clamp(gamma, -90.0, 90.0);

    if clamped_beta.abs() > clamped_gamma.abs() {
        if clamped_beta > threshold {
            Some((TiltDirection::Backward, clamp(clamped_beta, 0.0, 90.0)))
        } else if clamped_beta < -threshold {
            Some((TiltDirection::Forward, clamp(clamped_beta.abs(), 0.0, 90.0)))
        } else {
            None
        }
    } else if clamped_gamma > threshold {
        Some((TiltDirection::Right, clamp(clamped_gamma, 0.0, 90.0)))
    } else if clamped_gamma < -threshold {
        Some((TiltDirection::Left, clamp(clamped_gamma.abs(), 0.0, 90.0)))
    } else {
        None
    }
}

/// Pure state machine step for tilt gesture.
pub fn tilt_step(state: TiltState, input: &MotionInput, config: &TiltConfig) -> TiltStepResult {
    match input {
        MotionInput::Orientation {
            beta,
            gamma,
            time_ms,
            ..
        } => {
            match &state {
                TiltState::Idle => {
                    // Check if tilted beyond threshold
                    if let Some((direction, angle)) =
                        detect_tilt_direction(*beta, *gamma, config.angle_threshold)
                    {
                        TiltStepResult {
                            state: TiltState::Pending {
                                direction,
                                angle,
                                start_time_ms: *time_ms,
                            },
                            actions: vec![],
                        }
                    } else {
                        TiltStepResult {
                            state,
                            actions: vec![],
                        }
                    }
                }
                TiltState::Pending {
                    direction,
                    start_time_ms,
                    ..
                } => {
                    // Check if still tilted in same direction
                    if let Some((new_direction, angle)) =
                        detect_tilt_direction(*beta, *gamma, config.release_threshold)
                    {
                        if new_direction == *direction {
                            // Check if hold duration met
                            if *time_ms - start_time_ms >= config.hold_duration_ms {
                                TiltStepResult {
                                    state: TiltState::Tilted {
                                        direction: *direction,
                                        angle,
                                    },
                                    actions: vec![TiltAction::Start {
                                        data: TiltData {
                                            direction: *direction,
                                            angle,
                                        },
                                        haptic: HapticFeedback::light_tap(),
                                    }],
                                }
                            } else {
                                // Still waiting
                                TiltStepResult {
                                    state: TiltState::Pending {
                                        direction: *direction,
                                        angle,
                                        start_time_ms: *start_time_ms,
                                    },
                                    actions: vec![],
                                }
                            }
                        } else {
                            // Direction changed, restart
                            TiltStepResult {
                                state: TiltState::Pending {
                                    direction: new_direction,
                                    angle,
                                    start_time_ms: *time_ms,
                                },
                                actions: vec![],
                            }
                        }
                    } else {
                        // No longer tilted
                        TiltStepResult {
                            state: TiltState::Idle,
                            actions: vec![],
                        }
                    }
                }
                TiltState::Tilted {
                    direction,
                    angle: prev_angle,
                } => {
                    // Check if still tilted
                    if let Some((new_direction, angle)) =
                        detect_tilt_direction(*beta, *gamma, config.release_threshold)
                    {
                        if new_direction == *direction {
                            TiltStepResult {
                                state: TiltState::Tilted {
                                    direction: *direction,
                                    angle,
                                },
                                actions: vec![TiltAction::Update {
                                    data: TiltData {
                                        direction: *direction,
                                        angle,
                                    },
                                }],
                            }
                        } else {
                            // Direction changed, end current tilt
                            TiltStepResult {
                                state: TiltState::Pending {
                                    direction: new_direction,
                                    angle,
                                    start_time_ms: *time_ms,
                                },
                                actions: vec![TiltAction::End {
                                    data: TiltData {
                                        direction: *direction,
                                        angle: *prev_angle,
                                    },
                                    haptic: HapticFeedback::light_tap(),
                                }],
                            }
                        }
                    } else {
                        // No longer tilted
                        TiltStepResult {
                            state: TiltState::Idle,
                            actions: vec![TiltAction::End {
                                data: TiltData {
                                    direction: *direction,
                                    angle: *prev_angle,
                                },
                                haptic: HapticFeedback::light_tap(),
                            }],
                        }
                    }
                }
            }
        }
        // Ignore non-orientation inputs for tilt
        _ => TiltStepResult {
            state,
            actions: vec![],
        },
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                           // barrel roll gesture
// ═══════════════════════════════════════════════════════════════════════════════

/// Barrel roll direction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BarrelRollDirection {
    /// Clockwise rotation (right shoulder down first).
    Clockwise,
    /// Counter-clockwise rotation (left shoulder down first).
    CounterClockwise,
}

/// Configuration for barrel roll gesture recognition.
#[derive(Clone, Debug)]
pub struct BarrelRollConfig {
    /// Minimum rotation rate to start tracking (degrees/second).
    pub min_rotation_rate: f64,
    /// Required rotation to complete barrel roll (degrees).
    pub required_rotation: f64,
    /// Maximum time to complete rotation (ms).
    pub max_duration_ms: f64,
}

impl Default for BarrelRollConfig {
    fn default() -> Self {
        BarrelRollConfig {
            min_rotation_rate: 90.0,  // degrees/second
            required_rotation: 330.0, // ~full rotation with tolerance
            max_duration_ms: 2000.0,
        }
    }
}

/// Barrel roll gesture state.
#[derive(Clone, Debug)]
pub enum BarrelRollState {
    /// No rotation tracked.
    Idle,
    /// Tracking rotation.
    Tracking {
        direction: BarrelRollDirection,
        accumulated_rotation: f64,
        start_time_ms: f64,
        last_time_ms: f64,
    },
}

impl Default for BarrelRollState {
    fn default() -> Self {
        BarrelRollState::Idle
    }
}

/// Data included with barrel roll actions.
#[derive(Clone, Debug)]
pub struct BarrelRollData {
    /// Rotation direction.
    pub direction: BarrelRollDirection,
    /// Total rotation completed (degrees).
    pub rotation: f64,
    /// Duration of roll (ms).
    pub duration_ms: f64,
}

/// Actions emitted by the barrel roll state machine.
#[derive(Clone, Debug)]
pub enum BarrelRollAction {
    /// Barrel roll started (tracking initiated).
    Start { direction: BarrelRollDirection },
    /// Barrel roll progress update.
    Progress {
        rotation: f64,
        direction: BarrelRollDirection,
    },
    /// Barrel roll completed.
    Completed {
        data: BarrelRollData,
        haptic: HapticFeedback,
    },
    /// Barrel roll cancelled (timeout or reversed direction).
    Cancelled,
}

/// Result of a barrel roll state machine step.
#[derive(Clone, Debug)]
pub struct BarrelRollStepResult {
    /// New state.
    pub state: BarrelRollState,
    /// Actions to emit.
    pub actions: Vec<BarrelRollAction>,
}

/// Pure state machine step for barrel roll gesture.
pub fn barrel_roll_step(
    state: BarrelRollState,
    input: &MotionInput,
    config: &BarrelRollConfig,
) -> BarrelRollStepResult {
    match input {
        MotionInput::RotationRate {
            gamma, // Y-axis rotation = roll
            time_ms,
            ..
        } => {
            match &state {
                BarrelRollState::Idle => {
                    // Check if rotation rate exceeds threshold
                    if gamma.abs() >= config.min_rotation_rate {
                        let direction = if *gamma > 0.0 {
                            BarrelRollDirection::Clockwise
                        } else {
                            BarrelRollDirection::CounterClockwise
                        };
                        BarrelRollStepResult {
                            state: BarrelRollState::Tracking {
                                direction,
                                accumulated_rotation: 0.0,
                                start_time_ms: *time_ms,
                                last_time_ms: *time_ms,
                            },
                            actions: vec![BarrelRollAction::Start { direction }],
                        }
                    } else {
                        BarrelRollStepResult {
                            state,
                            actions: vec![],
                        }
                    }
                }
                BarrelRollState::Tracking {
                    direction,
                    accumulated_rotation,
                    start_time_ms,
                    last_time_ms,
                } => {
                    let elapsed = *time_ms - *start_time_ms;

                    // Check timeout
                    if elapsed > config.max_duration_ms {
                        return BarrelRollStepResult {
                            state: BarrelRollState::Idle,
                            actions: vec![BarrelRollAction::Cancelled],
                        };
                    }

                    // Check if direction reversed
                    let current_direction = if *gamma > 0.0 {
                        BarrelRollDirection::Clockwise
                    } else {
                        BarrelRollDirection::CounterClockwise
                    };

                    if gamma.abs() >= config.min_rotation_rate / 2.0
                        && current_direction != *direction
                    {
                        // Direction reversed significantly, cancel
                        return BarrelRollStepResult {
                            state: BarrelRollState::Idle,
                            actions: vec![BarrelRollAction::Cancelled],
                        };
                    }

                    // Accumulate rotation (only in correct direction)
                    let dt_seconds = (*time_ms - *last_time_ms) / 1000.0;
                    let delta_rotation = match direction {
                        BarrelRollDirection::Clockwise => (*gamma).max(0.0) * dt_seconds,
                        BarrelRollDirection::CounterClockwise => (-*gamma).max(0.0) * dt_seconds,
                    };
                    let new_rotation = *accumulated_rotation + delta_rotation;

                    // Check if barrel roll completed
                    if new_rotation >= config.required_rotation {
                        BarrelRollStepResult {
                            state: BarrelRollState::Idle,
                            actions: vec![BarrelRollAction::Completed {
                                data: BarrelRollData {
                                    direction: *direction,
                                    rotation: new_rotation,
                                    duration_ms: elapsed,
                                },
                                haptic: HapticFeedback::success(),
                            }],
                        }
                    } else {
                        BarrelRollStepResult {
                            state: BarrelRollState::Tracking {
                                direction: *direction,
                                accumulated_rotation: new_rotation,
                                start_time_ms: *start_time_ms,
                                last_time_ms: *time_ms,
                            },
                            actions: vec![BarrelRollAction::Progress {
                                rotation: new_rotation,
                                direction: *direction,
                            }],
                        }
                    }
                }
            }
        }
        // Ignore non-rotation inputs for barrel roll
        _ => BarrelRollStepResult {
            state,
            actions: vec![],
        },
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // flip gesture
// ═══════════════════════════════════════════════════════════════════════════════

/// Device face state (which side is up).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DeviceFace {
    /// Screen facing up.
    FaceUp,
    /// Screen facing down.
    FaceDown,
}

/// Configuration for flip gesture recognition.
#[derive(Clone, Debug)]
pub struct FlipConfig {
    /// Angle threshold for face detection (degrees from vertical).
    /// Device is "face up" when beta is within this threshold of 0.
    /// Device is "face down" when beta is within this threshold of 180 (or -180).
    pub angle_threshold: f64,
    /// Minimum time in flipped state before detecting (ms).
    pub hold_duration_ms: f64,
}

impl Default for FlipConfig {
    fn default() -> Self {
        FlipConfig {
            angle_threshold: 45.0,
            hold_duration_ms: 300.0,
        }
    }
}

/// Flip gesture state.
#[derive(Clone, Debug)]
pub enum FlipState {
    /// Device face up, stable.
    FaceUp,
    /// Device face down, stable.
    FaceDown,
    /// Transitioning, tracking duration.
    Transitioning {
        to_face: DeviceFace,
        start_time_ms: f64,
    },
}

impl Default for FlipState {
    fn default() -> Self {
        FlipState::FaceUp
    }
}

/// Data included with flip actions.
#[derive(Clone, Debug)]
pub struct FlipData {
    /// Previous face state.
    pub from: DeviceFace,
    /// New face state.
    pub to: DeviceFace,
}

/// Actions emitted by the flip state machine.
#[derive(Clone, Debug)]
pub enum FlipAction {
    /// Device flipped from face up to face down.
    FlippedDown {
        data: FlipData,
        haptic: HapticFeedback,
    },
    /// Device flipped from face down to face up.
    FlippedUp {
        data: FlipData,
        haptic: HapticFeedback,
    },
}

/// Result of a flip state machine step.
#[derive(Clone, Debug)]
pub struct FlipStepResult {
    /// New state.
    pub state: FlipState,
    /// Actions to emit.
    pub actions: Vec<FlipAction>,
}

/// Detect device face from orientation.
fn detect_device_face(beta: f64, threshold: f64) -> Option<DeviceFace> {
    // Beta: rotation around X axis
    // 0 = flat, face up
    // 180 or -180 = flat, face down
    // Values in between = tilted

    let abs_beta = beta.abs();
    if abs_beta < threshold {
        Some(DeviceFace::FaceUp)
    } else if abs_beta > (180.0 - threshold) {
        Some(DeviceFace::FaceDown)
    } else {
        None // Tilted, indeterminate
    }
}

/// Pure state machine step for flip gesture.
pub fn flip_step(state: FlipState, input: &MotionInput, config: &FlipConfig) -> FlipStepResult {
    match input {
        MotionInput::Orientation { beta, time_ms, .. } => {
            let current_face = detect_device_face(*beta, config.angle_threshold);

            match (&state, current_face) {
                // Stable face up, detect transition to face down
                (FlipState::FaceUp, Some(DeviceFace::FaceDown)) => FlipStepResult {
                    state: FlipState::Transitioning {
                        to_face: DeviceFace::FaceDown,
                        start_time_ms: *time_ms,
                    },
                    actions: vec![],
                },
                // Stable face up, still face up
                (FlipState::FaceUp, Some(DeviceFace::FaceUp)) => FlipStepResult {
                    state,
                    actions: vec![],
                },
                // Stable face down, detect transition to face up
                (FlipState::FaceDown, Some(DeviceFace::FaceUp)) => FlipStepResult {
                    state: FlipState::Transitioning {
                        to_face: DeviceFace::FaceUp,
                        start_time_ms: *time_ms,
                    },
                    actions: vec![],
                },
                // Stable face down, still face down
                (FlipState::FaceDown, Some(DeviceFace::FaceDown)) => FlipStepResult {
                    state,
                    actions: vec![],
                },
                // Transitioning to face down
                (
                    FlipState::Transitioning {
                        to_face: DeviceFace::FaceDown,
                        start_time_ms,
                    },
                    Some(DeviceFace::FaceDown),
                ) => {
                    if *time_ms - *start_time_ms >= config.hold_duration_ms {
                        FlipStepResult {
                            state: FlipState::FaceDown,
                            actions: vec![FlipAction::FlippedDown {
                                data: FlipData {
                                    from: DeviceFace::FaceUp,
                                    to: DeviceFace::FaceDown,
                                },
                                haptic: HapticFeedback::tap(),
                            }],
                        }
                    } else {
                        FlipStepResult {
                            state,
                            actions: vec![],
                        }
                    }
                }
                // Transitioning to face up
                (
                    FlipState::Transitioning {
                        to_face: DeviceFace::FaceUp,
                        start_time_ms,
                    },
                    Some(DeviceFace::FaceUp),
                ) => {
                    if *time_ms - *start_time_ms >= config.hold_duration_ms {
                        FlipStepResult {
                            state: FlipState::FaceUp,
                            actions: vec![FlipAction::FlippedUp {
                                data: FlipData {
                                    from: DeviceFace::FaceDown,
                                    to: DeviceFace::FaceUp,
                                },
                                haptic: HapticFeedback::tap(),
                            }],
                        }
                    } else {
                        FlipStepResult {
                            state,
                            actions: vec![],
                        }
                    }
                }
                // Transitioning cancelled (returned to original state)
                (
                    FlipState::Transitioning {
                        to_face: DeviceFace::FaceDown,
                        ..
                    },
                    Some(DeviceFace::FaceUp),
                ) => FlipStepResult {
                    state: FlipState::FaceUp,
                    actions: vec![],
                },
                (
                    FlipState::Transitioning {
                        to_face: DeviceFace::FaceUp,
                        ..
                    },
                    Some(DeviceFace::FaceDown),
                ) => FlipStepResult {
                    state: FlipState::FaceDown,
                    actions: vec![],
                },
                // Indeterminate orientation (tilted)
                (_, None) => FlipStepResult {
                    state,
                    actions: vec![],
                },
            }
        }
        // Ignore non-orientation inputs for flip
        _ => FlipStepResult {
            state,
            actions: vec![],
        },
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // tests
// ═══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_shake_detection() {
        let config = ShakeConfig::default();
        // Initialize with last_shake_ms in the past to avoid cooldown on first input
        let mut state = ShakeState {
            last_shake_ms: -1000.0,
            ..Default::default()
        };

        // Simulate shake sequence: right, left, right, left (3 reversals)
        // Times start at 1000ms to avoid cooldown issues
        let inputs = [
            (20.0, 1000.0),  // Right
            (-20.0, 1100.0), // Left (reversal 1)
            (20.0, 1200.0),  // Right (reversal 2)
            (-20.0, 1300.0), // Left (reversal 3)
        ];

        for (accel_x, time) in inputs {
            let input = MotionInput::Acceleration {
                acceleration: Point3D::new(accel_x, 0.0, 0.0),
                acceleration_with_gravity: Point3D::new(accel_x, 0.0, 9.8),
                time_ms: time,
            };
            let result = shake_step(state, &input, &config);
            state = result.state;
            if !result.actions.is_empty() {
                assert!(matches!(result.actions[0], ShakeAction::Detected { .. }));
                return;
            }
        }
        panic!("Shake should have been detected");
    }

    #[test]
    fn test_tilt_direction_detection() {
        // Forward tilt
        assert!(matches!(
            detect_tilt_direction(-45.0, 0.0, 30.0),
            Some((TiltDirection::Forward, _))
        ));
        // Backward tilt
        assert!(matches!(
            detect_tilt_direction(45.0, 0.0, 30.0),
            Some((TiltDirection::Backward, _))
        ));
        // Left tilt
        assert!(matches!(
            detect_tilt_direction(0.0, -45.0, 30.0),
            Some((TiltDirection::Left, _))
        ));
        // Right tilt
        assert!(matches!(
            detect_tilt_direction(0.0, 45.0, 30.0),
            Some((TiltDirection::Right, _))
        ));
        // No tilt
        assert!(detect_tilt_direction(10.0, 10.0, 30.0).is_none());
    }

    #[test]
    fn test_flip_detection() {
        let config = FlipConfig::default();
        let state = FlipState::FaceUp;

        // Simulate flip to face down
        let input = MotionInput::Orientation {
            alpha: 0.0,
            beta: 170.0, // Near face down
            gamma: 0.0,
            time_ms: 0.0,
        };
        let result = flip_step(state, &input, &config);
        assert!(matches!(
            result.state,
            FlipState::Transitioning {
                to_face: DeviceFace::FaceDown,
                ..
            }
        ));

        // After hold duration
        let input2 = MotionInput::Orientation {
            alpha: 0.0,
            beta: 175.0,
            gamma: 0.0,
            time_ms: 500.0, // > hold_duration_ms
        };
        let result2 = flip_step(result.state, &input2, &config);
        assert!(matches!(result2.state, FlipState::FaceDown));
        assert!(!result2.actions.is_empty());
        assert!(matches!(result2.actions[0], FlipAction::FlippedDown { .. }));
    }

    #[test]
    fn test_device_face_detection() {
        // Face up
        assert_eq!(detect_device_face(0.0, 45.0), Some(DeviceFace::FaceUp));
        assert_eq!(detect_device_face(30.0, 45.0), Some(DeviceFace::FaceUp));
        // Face down
        assert_eq!(detect_device_face(170.0, 45.0), Some(DeviceFace::FaceDown));
        assert_eq!(detect_device_face(-170.0, 45.0), Some(DeviceFace::FaceDown));
        // Indeterminate (tilted)
        assert_eq!(detect_device_face(90.0, 45.0), None);
        assert_eq!(detect_device_face(-90.0, 45.0), None);
    }
}
