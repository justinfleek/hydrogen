//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                                  // hydrogen // gesture // touch
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! # Touch Gesture Recognition
//!
//! Pure state machines for touch gestures following the libevring pattern:
//!
//! ```text
//! step :: State -> Event -> (State, [Action])
//! ```
//!
//! ## Gestures Implemented
//!
//! - **Pan**: Single-finger drag with velocity tracking
//! - **Pinch**: Two-finger scale gesture
//! - **Rotate**: Two-finger rotation gesture
//! - **Swipe**: Directional flick (up/down/left/right)
//! - **LongPress**: Timed hold gesture
//! - **DoubleTap**: Two taps within time/distance threshold
//!
//! ## Integration
//!
//! - Haptics: Each action includes haptic feedback descriptor
//! - Elevation: Gestures are elevation-aware (higher = heavier inertia)
//! - Proofs: Bounded types verified in proofs/Gesture/Bounds.lean
//!
//! ─────────────────────────────────────────────────────────────────────────────

use super::common::{
    clamp, compute_velocity, detect_swipe_direction, normalize_angle, Axis, Elevation,
    GestureTarget, Handle, HapticFeedback, HapticPattern, Point, SwipeDirection, TimestampedPoint,
    TwoFingerData,
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // gesture input
// ═══════════════════════════════════════════════════════════════════════════════

/// Input events from the pointer/touch system.
/// This is what the runtime sends to gesture state machines.
#[derive(Clone, Debug)]
pub enum GestureInput {
    /// Single pointer down
    PointerDown {
        position: Point,
        time_ms: f64,
        pointer_id: i32,
    },
    /// Pointer moved
    PointerMove {
        position: Point,
        time_ms: f64,
        pointer_id: i32,
    },
    /// Pointer released
    PointerUp {
        position: Point,
        time_ms: f64,
        pointer_id: i32,
    },
    /// Pointer cancelled (e.g., touch interrupted)
    PointerCancel { pointer_id: i32 },
    /// Two-finger gesture data (for pinch/rotate)
    TwoFingerUpdate { data: TwoFingerData, time_ms: f64 },
    /// Two fingers lifted
    TwoFingerEnd,
    /// Timer fired (for long press)
    TimerFired { timer_id: u32 },
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // pan gesture
// ═══════════════════════════════════════════════════════════════════════════════

/// Configuration for pan gesture recognition.
#[derive(Clone, Debug)]
pub struct PanConfig {
    /// Minimum distance (pixels) before pan activates.
    pub threshold: f64,
    /// Lock to single axis after threshold.
    pub lock_axis: bool,
    /// Maximum velocity samples to track.
    pub max_velocity_samples: usize,
    /// Target element (optional).
    pub target: Option<GestureTarget>,
}

impl Default for PanConfig {
    fn default() -> Self {
        PanConfig {
            threshold: 10.0,
            lock_axis: false,
            max_velocity_samples: 10,
            target: None,
        }
    }
}

/// Pan gesture state.
#[derive(Clone, Debug)]
pub enum PanState {
    /// No active gesture.
    Idle,
    /// Pointer down, waiting for threshold.
    Pending {
        pointer_id: i32,
        start: Point,
        current: Point,
        samples: Vec<TimestampedPoint>,
    },
    /// Actively panning.
    Active {
        pointer_id: i32,
        start: Point,
        current: Point,
        samples: Vec<TimestampedPoint>,
        locked_axis: Option<Axis>,
        offset: Point,
    },
}

impl Default for PanState {
    fn default() -> Self {
        PanState::Idle
    }
}

/// Data included with pan actions.
#[derive(Clone, Debug)]
pub struct PanData {
    /// Starting position.
    pub start: Point,
    /// Current position.
    pub current: Point,
    /// Delta from start.
    pub delta: Point,
    /// Accumulated offset (for multiple pan sessions).
    pub offset: Point,
    /// Current velocity (pixels/second).
    pub velocity: Point,
    /// Locked axis (if any).
    pub locked_axis: Option<Axis>,
}

/// Actions emitted by the pan state machine.
#[derive(Clone, Debug)]
pub enum PanAction {
    /// Pan gesture started.
    Start {
        data: PanData,
        haptic: HapticFeedback,
    },
    /// Pan gesture moved.
    Move {
        data: PanData,
        haptic: Option<HapticFeedback>,
    },
    /// Pan gesture ended.
    End {
        data: PanData,
        haptic: HapticFeedback,
    },
    /// Pan gesture cancelled.
    Cancel,
}

/// Result of a pan state machine step.
#[derive(Clone, Debug)]
pub struct PanStepResult {
    /// New state.
    pub state: PanState,
    /// Actions to emit.
    pub actions: Vec<PanAction>,
}

/// Pure state machine step for pan gesture.
///
/// ```text
/// step :: PanState -> GestureInput -> PanConfig -> PanStepResult
/// ```
pub fn pan_step(state: PanState, input: &GestureInput, config: &PanConfig) -> PanStepResult {
    match (&state, input) {
        // ─────────────────────────────────────────────────────────────────────
        // Idle state transitions
        // ─────────────────────────────────────────────────────────────────────
        (
            PanState::Idle,
            GestureInput::PointerDown {
                position,
                time_ms,
                pointer_id,
            },
        ) => PanStepResult {
            state: PanState::Pending {
                pointer_id: *pointer_id,
                start: *position,
                current: *position,
                samples: vec![TimestampedPoint {
                    point: *position,
                    time_ms: *time_ms,
                }],
            },
            actions: vec![],
        },

        // ─────────────────────────────────────────────────────────────────────
        // Pending state transitions
        // ─────────────────────────────────────────────────────────────────────
        (
            PanState::Pending {
                pointer_id: pid,
                start,
                samples,
                ..
            },
            GestureInput::PointerMove {
                position,
                time_ms,
                pointer_id,
            },
        ) if pid == pointer_id => {
            let distance = start.distance_to(position);
            let mut new_samples = samples.clone();
            new_samples.push(TimestampedPoint {
                point: *position,
                time_ms: *time_ms,
            });
            if new_samples.len() > config.max_velocity_samples {
                new_samples.remove(0);
            }

            if distance >= config.threshold {
                // Threshold exceeded — activate pan
                let locked_axis = if config.lock_axis {
                    let dx = (position.x - start.x).abs();
                    let dy = (position.y - start.y).abs();
                    Some(if dx > dy { Axis::X } else { Axis::Y })
                } else {
                    None
                };

                let velocity = compute_velocity(&new_samples);
                let data = PanData {
                    start: *start,
                    current: *position,
                    delta: position.sub(start),
                    offset: Point::default(),
                    velocity,
                    locked_axis,
                };

                PanStepResult {
                    state: PanState::Active {
                        pointer_id: *pointer_id,
                        start: *start,
                        current: *position,
                        samples: new_samples,
                        locked_axis,
                        offset: Point::default(),
                    },
                    actions: vec![PanAction::Start {
                        data,
                        haptic: HapticFeedback::light_tap(),
                    }],
                }
            } else {
                // Still pending
                PanStepResult {
                    state: PanState::Pending {
                        pointer_id: *pointer_id,
                        start: *start,
                        current: *position,
                        samples: new_samples,
                    },
                    actions: vec![],
                }
            }
        }

        (
            PanState::Pending {
                pointer_id: pid, ..
            },
            GestureInput::PointerUp { pointer_id, .. },
        ) if pid == pointer_id => {
            // Released before threshold — return to idle
            PanStepResult {
                state: PanState::Idle,
                actions: vec![],
            }
        }

        (
            PanState::Pending {
                pointer_id: pid, ..
            },
            GestureInput::PointerCancel { pointer_id },
        ) if pid == pointer_id => PanStepResult {
            state: PanState::Idle,
            actions: vec![PanAction::Cancel],
        },

        // ─────────────────────────────────────────────────────────────────────
        // Active state transitions
        // ─────────────────────────────────────────────────────────────────────
        (
            PanState::Active {
                pointer_id: pid,
                start,
                samples,
                locked_axis,
                offset,
                ..
            },
            GestureInput::PointerMove {
                position,
                time_ms,
                pointer_id,
            },
        ) if pid == pointer_id => {
            let mut new_samples = samples.clone();
            new_samples.push(TimestampedPoint {
                point: *position,
                time_ms: *time_ms,
            });
            if new_samples.len() > config.max_velocity_samples {
                new_samples.remove(0);
            }

            let velocity = compute_velocity(&new_samples);
            let data = PanData {
                start: *start,
                current: *position,
                delta: position.sub(start),
                offset: *offset,
                velocity,
                locked_axis: *locked_axis,
            };

            PanStepResult {
                state: PanState::Active {
                    pointer_id: *pointer_id,
                    start: *start,
                    current: *position,
                    samples: new_samples,
                    locked_axis: *locked_axis,
                    offset: *offset,
                },
                actions: vec![PanAction::Move { data, haptic: None }],
            }
        }

        (
            PanState::Active {
                pointer_id: pid,
                start,
                current,
                samples,
                locked_axis,
                offset,
            },
            GestureInput::PointerUp { pointer_id, .. },
        ) if pid == pointer_id => {
            let velocity = compute_velocity(samples);
            let new_offset = offset.add(&current.sub(start));
            let data = PanData {
                start: *start,
                current: *current,
                delta: current.sub(start),
                offset: new_offset,
                velocity,
                locked_axis: *locked_axis,
            };

            PanStepResult {
                state: PanState::Idle,
                actions: vec![PanAction::End {
                    data,
                    haptic: HapticFeedback::light_tap(),
                }],
            }
        }

        (
            PanState::Active {
                pointer_id: pid, ..
            },
            GestureInput::PointerCancel { pointer_id },
        ) if pid == pointer_id => PanStepResult {
            state: PanState::Idle,
            actions: vec![PanAction::Cancel],
        },

        // ─────────────────────────────────────────────────────────────────────
        // Default: no state change
        // ─────────────────────────────────────────────────────────────────────
        _ => PanStepResult {
            state,
            actions: vec![],
        },
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // swipe gesture
// ═══════════════════════════════════════════════════════════════════════════════

/// Configuration for swipe gesture recognition.
#[derive(Clone, Debug)]
pub struct SwipeConfig {
    /// Minimum distance (pixels) for a swipe.
    pub min_distance: f64,
    /// Maximum time (ms) for a swipe.
    pub max_duration_ms: f64,
    /// Minimum velocity (pixels/second) required.
    pub min_velocity: f64,
    /// Maximum angle deviation from cardinal direction (degrees).
    pub max_angle_deviation: f64,
    /// Target element (optional, for elevation-aware feedback).
    pub target: Option<GestureTarget>,
}

impl Default for SwipeConfig {
    fn default() -> Self {
        SwipeConfig {
            min_distance: 50.0,
            max_duration_ms: 300.0,
            min_velocity: 200.0,
            max_angle_deviation: 30.0,
            target: None,
        }
    }
}

/// Swipe gesture state.
#[derive(Clone, Debug)]
pub enum SwipeState {
    /// No active gesture.
    Idle,
    /// Tracking potential swipe.
    Tracking {
        pointer_id: i32,
        start: Point,
        start_time_ms: f64,
        samples: Vec<TimestampedPoint>,
    },
}

impl Default for SwipeState {
    fn default() -> Self {
        SwipeState::Idle
    }
}

/// Data included with swipe actions.
#[derive(Clone, Debug)]
pub struct SwipeData {
    /// Detected swipe direction.
    pub direction: SwipeDirection,
    /// Starting position.
    pub start: Point,
    /// End position.
    pub end: Point,
    /// Total distance traveled.
    pub distance: f64,
    /// Swipe velocity (pixels/second).
    pub velocity: f64,
    /// Duration in milliseconds.
    pub duration_ms: f64,
    /// Target handle (if any).
    pub target_handle: Handle,
    /// Target elevation (affects haptic intensity).
    pub elevation: Elevation,
}

/// Actions emitted by the swipe state machine.
#[derive(Clone, Debug)]
pub enum SwipeAction {
    /// Swipe gesture detected.
    Detected {
        data: SwipeData,
        haptic: HapticFeedback,
    },
    /// Swipe cancelled (didn't meet criteria).
    Cancel,
}

/// Result of a swipe state machine step.
#[derive(Clone, Debug)]
pub struct SwipeStepResult {
    /// New state.
    pub state: SwipeState,
    /// Actions to emit.
    pub actions: Vec<SwipeAction>,
}

/// Helper: get Handle from GestureTarget or return INVALID.
fn get_swipe_target_handle(target: &Option<GestureTarget>) -> Handle {
    target.as_ref().map_or(Handle::INVALID, |t| t.handle)
}

/// Helper: get Elevation from GestureTarget or return base.
fn get_swipe_target_elevation(target: &Option<GestureTarget>) -> Elevation {
    target.as_ref().map_or(Elevation::base(), |t| t.elevation)
}

/// Compute haptic feedback for swipe based on velocity and elevation.
/// Higher elevation = heavier feel, higher velocity = stronger impact.
fn swipe_haptic(velocity: f64, elevation: &Elevation) -> HapticFeedback {
    // Normalize velocity to 0-1 range (assuming max velocity ~2000 px/s)
    let normalized_velocity = clamp(velocity / 2000.0, 0.0, 1.0);
    // Scale by elevation inertia (heavier elements have more impact)
    let force = normalized_velocity * elevation.inertia_factor;
    HapticFeedback {
        intensity: clamp(0.3 + force * 0.5, 0.0, 1.0),
        duration_ms: 15,
        pattern: HapticPattern::Impact { force },
    }
}

/// Check if angle (in degrees) is within deviation of a cardinal direction.
fn is_valid_swipe_angle(dx: f64, dy: f64, max_deviation: f64) -> bool {
    let angle_rad = dy.atan2(dx);
    let angle_deg = angle_rad.to_degrees();
    let normalized = normalize_angle(angle_deg);

    // Cardinal directions: 0 (right), 90 (down), -90 (up), 180/-180 (left)
    let cardinal_angles = [0.0, 90.0, -90.0, 180.0, -180.0];

    cardinal_angles.iter().any(|&cardinal| {
        let diff = normalize_angle(normalized - cardinal).abs();
        diff <= max_deviation
    })
}

/// Pure state machine step for swipe gesture.
///
/// ```text
/// step :: SwipeState -> GestureInput -> SwipeConfig -> SwipeStepResult
/// ```
pub fn swipe_step(
    state: SwipeState,
    input: &GestureInput,
    config: &SwipeConfig,
) -> SwipeStepResult {
    match (&state, input) {
        // ─────────────────────────────────────────────────────────────────────
        // Idle -> Tracking on pointer down
        // ─────────────────────────────────────────────────────────────────────
        (
            SwipeState::Idle,
            GestureInput::PointerDown {
                position,
                time_ms,
                pointer_id,
            },
        ) => SwipeStepResult {
            state: SwipeState::Tracking {
                pointer_id: *pointer_id,
                start: *position,
                start_time_ms: *time_ms,
                samples: vec![TimestampedPoint {
                    point: *position,
                    time_ms: *time_ms,
                }],
            },
            actions: vec![],
        },

        // ─────────────────────────────────────────────────────────────────────
        // Tracking -> update samples on move
        // ─────────────────────────────────────────────────────────────────────
        (
            SwipeState::Tracking {
                pointer_id: pid,
                start,
                start_time_ms,
                samples,
            },
            GestureInput::PointerMove {
                position,
                time_ms,
                pointer_id,
            },
        ) if pid == pointer_id => {
            let mut new_samples = samples.clone();
            new_samples.push(TimestampedPoint {
                point: *position,
                time_ms: *time_ms,
            });
            // Keep last 10 samples for velocity calculation
            if new_samples.len() > 10 {
                new_samples.remove(0);
            }

            // Check if exceeded max duration (cancel early)
            let elapsed = time_ms - start_time_ms;
            if elapsed > config.max_duration_ms {
                return SwipeStepResult {
                    state: SwipeState::Idle,
                    actions: vec![SwipeAction::Cancel],
                };
            }

            SwipeStepResult {
                state: SwipeState::Tracking {
                    pointer_id: *pointer_id,
                    start: *start,
                    start_time_ms: *start_time_ms,
                    samples: new_samples,
                },
                actions: vec![],
            }
        }

        // ─────────────────────────────────────────────────────────────────────
        // Tracking -> evaluate on pointer up
        // ─────────────────────────────────────────────────────────────────────
        (
            SwipeState::Tracking {
                pointer_id: pid,
                start,
                start_time_ms,
                samples,
            },
            GestureInput::PointerUp {
                position,
                time_ms,
                pointer_id,
            },
        ) if pid == pointer_id => {
            let dx = position.x - start.x;
            let dy = position.y - start.y;
            let distance = start.distance_to(position);
            let duration_ms = time_ms - start_time_ms;
            let velocity = compute_velocity(samples);
            let speed = (velocity.x * velocity.x + velocity.y * velocity.y).sqrt();

            // Validate swipe criteria
            let is_far_enough = distance >= config.min_distance;
            let is_fast_enough = speed >= config.min_velocity;
            let is_quick_enough = duration_ms <= config.max_duration_ms;
            let is_directional = is_valid_swipe_angle(dx, dy, config.max_angle_deviation);

            if is_far_enough && is_fast_enough && is_quick_enough && is_directional {
                let direction = detect_swipe_direction(dx, dy);
                let target_handle = get_swipe_target_handle(&config.target);
                let elevation = get_swipe_target_elevation(&config.target);

                let data = SwipeData {
                    direction,
                    start: *start,
                    end: *position,
                    distance,
                    velocity: speed,
                    duration_ms,
                    target_handle,
                    elevation,
                };

                SwipeStepResult {
                    state: SwipeState::Idle,
                    actions: vec![SwipeAction::Detected {
                        data: data.clone(),
                        haptic: swipe_haptic(speed, &data.elevation),
                    }],
                }
            } else {
                // Didn't meet swipe criteria
                SwipeStepResult {
                    state: SwipeState::Idle,
                    actions: vec![SwipeAction::Cancel],
                }
            }
        }

        // ─────────────────────────────────────────────────────────────────────
        // Tracking -> cancel on pointer cancel
        // ─────────────────────────────────────────────────────────────────────
        (
            SwipeState::Tracking {
                pointer_id: pid, ..
            },
            GestureInput::PointerCancel { pointer_id },
        ) if pid == pointer_id => SwipeStepResult {
            state: SwipeState::Idle,
            actions: vec![SwipeAction::Cancel],
        },

        // ─────────────────────────────────────────────────────────────────────
        // Default: no state change
        // ─────────────────────────────────────────────────────────────────────
        _ => SwipeStepResult {
            state,
            actions: vec![],
        },
    }
}
