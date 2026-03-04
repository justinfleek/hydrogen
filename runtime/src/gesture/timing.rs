//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                                // hydrogen // gesture // timing
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! # Timing-Based Gesture Recognition
//!
//! Pure state machines for timing-based gestures following the libevring pattern:
//!
//! ```text
//! step :: State -> Event -> (State, [Action])
//! ```
//!
//! ## Gestures Implemented
//!
//! - **Swipe**: Directional flick (up/down/left/right)
//! - **LongPress**: Timed hold gesture
//! - **DoubleTap**: Two taps within time/distance threshold
//!
//! ## Integration
//!
//! - Haptics: Each action includes haptic feedback descriptor
//!
//! ─────────────────────────────────────────────────────────────────────────────

use super::common::{detect_swipe_direction, GestureTarget, HapticFeedback, Point, SwipeDirection};
use super::touch::GestureInput;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // swipe gesture
// ═══════════════════════════════════════════════════════════════════════════════

/// Configuration for swipe gesture recognition.
#[derive(Clone, Debug)]
pub struct SwipeConfig {
    /// Minimum distance (pixels) for swipe.
    pub distance_threshold: f64,
    /// Minimum velocity (pixels/second) for swipe.
    pub velocity_threshold: f64,
    /// Maximum duration (ms) for swipe.
    pub max_duration: f64,
    /// Target element (optional).
    pub target: Option<GestureTarget>,
}

impl Default for SwipeConfig {
    fn default() -> Self {
        SwipeConfig {
            distance_threshold: 50.0,
            velocity_threshold: 300.0,
            max_duration: 500.0,
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
        start_time: f64,
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
    /// Detected direction.
    pub direction: SwipeDirection,
    /// Swipe velocity (pixels/second).
    pub velocity: f64,
    /// Distance traveled.
    pub distance: f64,
    /// Start position.
    pub start: Point,
    /// End position.
    pub end: Point,
}

/// Actions emitted by the swipe state machine.
#[derive(Clone, Debug)]
pub enum SwipeAction {
    /// Swipe detected.
    Detected {
        data: SwipeData,
        haptic: HapticFeedback,
    },
}

/// Result of a swipe state machine step.
#[derive(Clone, Debug)]
pub struct SwipeStepResult {
    /// New state.
    pub state: SwipeState,
    /// Actions to emit.
    pub actions: Vec<SwipeAction>,
}

/// Pure state machine step for swipe gesture.
pub fn swipe_step(
    state: SwipeState,
    input: &GestureInput,
    config: &SwipeConfig,
) -> SwipeStepResult {
    match (&state, input) {
        // Idle -> Tracking on pointer down
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
                start_time: *time_ms,
            },
            actions: vec![],
        },

        // Tracking -> check on pointer up
        (
            SwipeState::Tracking {
                pointer_id: pid,
                start,
                start_time,
            },
            GestureInput::PointerUp {
                position,
                time_ms,
                pointer_id,
            },
        ) if pid == pointer_id => {
            let dx = position.x - start.x;
            let dy = position.y - start.y;
            let distance = (dx * dx + dy * dy).sqrt();
            let duration = time_ms - start_time;

            // Check swipe conditions
            if duration <= config.max_duration && distance >= config.distance_threshold {
                let velocity = distance / (duration / 1000.0);
                if velocity >= config.velocity_threshold {
                    let direction = detect_swipe_direction(dx, dy);
                    let swipe_data = SwipeData {
                        direction,
                        velocity,
                        distance,
                        start: *start,
                        end: *position,
                    };
                    return SwipeStepResult {
                        state: SwipeState::Idle,
                        actions: vec![SwipeAction::Detected {
                            data: swipe_data,
                            haptic: HapticFeedback::tap(),
                        }],
                    };
                }
            }

            // Not a valid swipe
            SwipeStepResult {
                state: SwipeState::Idle,
                actions: vec![],
            }
        }

        // Tracking cancelled
        (
            SwipeState::Tracking {
                pointer_id: pid, ..
            },
            GestureInput::PointerCancel { pointer_id },
        ) if pid == pointer_id => SwipeStepResult {
            state: SwipeState::Idle,
            actions: vec![],
        },

        // Default: no state change
        _ => SwipeStepResult {
            state,
            actions: vec![],
        },
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                             // long press gesture
// ═══════════════════════════════════════════════════════════════════════════════

/// Configuration for long press gesture recognition.
#[derive(Clone, Debug)]
pub struct LongPressConfig {
    /// Duration (ms) to trigger long press.
    pub duration: f64,
    /// Maximum movement (pixels) allowed during press.
    pub max_distance: f64,
    /// Target element (optional).
    pub target: Option<GestureTarget>,
}

impl Default for LongPressConfig {
    fn default() -> Self {
        LongPressConfig {
            duration: 500.0,
            max_distance: 10.0,
            target: None,
        }
    }
}

/// Long press gesture state.
#[derive(Clone, Debug)]
pub enum LongPressState {
    /// No active gesture.
    Idle,
    /// Waiting for duration.
    Waiting {
        pointer_id: i32,
        start: Point,
        start_time: f64,
        timer_id: u32,
    },
    /// Long press triggered, still holding.
    Triggered { pointer_id: i32, position: Point },
}

impl Default for LongPressState {
    fn default() -> Self {
        LongPressState::Idle
    }
}

/// Data included with long press actions.
#[derive(Clone, Debug)]
pub struct LongPressData {
    /// Position of the long press.
    pub position: Point,
}

/// Actions emitted by the long press state machine.
#[derive(Clone, Debug)]
pub enum LongPressAction {
    /// Long press started (pointer down).
    Start { data: LongPressData },
    /// Request to start a timer (runtime must handle).
    RequestTimer { duration_ms: f64, timer_id: u32 },
    /// Long press triggered (duration elapsed).
    Triggered {
        data: LongPressData,
        haptic: HapticFeedback,
    },
    /// Long press ended (pointer up after trigger).
    End { data: LongPressData },
    /// Long press cancelled (moved too far or released early).
    Cancel,
}

/// Result of a long press state machine step.
#[derive(Clone, Debug)]
pub struct LongPressStepResult {
    /// New state.
    pub state: LongPressState,
    /// Actions to emit.
    pub actions: Vec<LongPressAction>,
}

/// Counter for generating timer IDs.
static TIMER_COUNTER: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);

fn next_timer_id() -> u32 {
    TIMER_COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
}

/// Pure state machine step for long press gesture.
pub fn long_press_step(
    state: LongPressState,
    input: &GestureInput,
    config: &LongPressConfig,
) -> LongPressStepResult {
    match (&state, input) {
        // Idle -> Waiting on pointer down
        (
            LongPressState::Idle,
            GestureInput::PointerDown {
                position,
                time_ms,
                pointer_id,
            },
        ) => {
            let timer_id = next_timer_id();
            LongPressStepResult {
                state: LongPressState::Waiting {
                    pointer_id: *pointer_id,
                    start: *position,
                    start_time: *time_ms,
                    timer_id,
                },
                actions: vec![
                    LongPressAction::Start {
                        data: LongPressData {
                            position: *position,
                        },
                    },
                    LongPressAction::RequestTimer {
                        duration_ms: config.duration,
                        timer_id,
                    },
                ],
            }
        }

        // Waiting -> check movement
        (
            LongPressState::Waiting {
                pointer_id: pid,
                start,
                start_time,
                timer_id,
            },
            GestureInput::PointerMove {
                position,
                pointer_id,
                ..
            },
        ) if pid == pointer_id => {
            let distance = start.distance_to(position);
            if distance > config.max_distance {
                // Moved too far — cancel
                LongPressStepResult {
                    state: LongPressState::Idle,
                    actions: vec![LongPressAction::Cancel],
                }
            } else {
                // Still waiting
                LongPressStepResult {
                    state: LongPressState::Waiting {
                        pointer_id: *pointer_id,
                        start: *start,
                        start_time: *start_time,
                        timer_id: *timer_id,
                    },
                    actions: vec![],
                }
            }
        }

        // Waiting -> Triggered on timer
        (
            LongPressState::Waiting {
                pointer_id,
                start,
                timer_id: expected_id,
                ..
            },
            GestureInput::TimerFired { timer_id },
        ) if timer_id == expected_id => LongPressStepResult {
            state: LongPressState::Triggered {
                pointer_id: *pointer_id,
                position: *start,
            },
            actions: vec![LongPressAction::Triggered {
                data: LongPressData { position: *start },
                haptic: HapticFeedback::heavy_tap(),
            }],
        },

        // Waiting -> cancelled on pointer up (released too early)
        (
            LongPressState::Waiting {
                pointer_id: pid, ..
            },
            GestureInput::PointerUp { pointer_id, .. },
        ) if pid == pointer_id => LongPressStepResult {
            state: LongPressState::Idle,
            actions: vec![LongPressAction::Cancel],
        },

        // Waiting -> cancelled on pointer cancel
        (
            LongPressState::Waiting {
                pointer_id: pid, ..
            },
            GestureInput::PointerCancel { pointer_id },
        ) if pid == pointer_id => LongPressStepResult {
            state: LongPressState::Idle,
            actions: vec![LongPressAction::Cancel],
        },

        // Triggered -> End on pointer up
        (
            LongPressState::Triggered {
                pointer_id: pid,
                position,
            },
            GestureInput::PointerUp { pointer_id, .. },
        ) if pid == pointer_id => LongPressStepResult {
            state: LongPressState::Idle,
            actions: vec![LongPressAction::End {
                data: LongPressData {
                    position: *position,
                },
            }],
        },

        // Default: no state change
        _ => LongPressStepResult {
            state,
            actions: vec![],
        },
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // multi-tap gesture
// ═══════════════════════════════════════════════════════════════════════════════

/// Configuration for multi-tap gesture recognition.
#[derive(Clone, Debug)]
pub struct MultiTapConfig {
    /// Maximum time (ms) between taps.
    pub max_delay: f64,
    /// Maximum distance (pixels) between tap positions.
    pub max_distance: f64,
    /// Number of taps to detect (2 = double tap, 3 = triple tap, etc).
    pub required_taps: u32,
    /// Target element (optional).
    pub target: Option<GestureTarget>,
}

impl Default for MultiTapConfig {
    fn default() -> Self {
        MultiTapConfig {
            max_delay: 300.0,
            max_distance: 30.0,
            required_taps: 2,
            target: None,
        }
    }
}

impl MultiTapConfig {
    /// Create a double-tap configuration.
    pub fn double_tap() -> Self {
        MultiTapConfig {
            required_taps: 2,
            ..Default::default()
        }
    }

    /// Create a triple-tap configuration.
    pub fn triple_tap() -> Self {
        MultiTapConfig {
            required_taps: 3,
            ..Default::default()
        }
    }
}

/// Multi-tap gesture state.
#[derive(Clone, Debug)]
pub enum MultiTapState {
    /// No active gesture.
    Idle,
    /// Waiting for next tap.
    Waiting {
        tap_count: u32,
        last_position: Point,
        last_time: f64,
        timer_id: u32,
    },
}

impl Default for MultiTapState {
    fn default() -> Self {
        MultiTapState::Idle
    }
}

/// Data included with multi-tap actions.
#[derive(Clone, Debug)]
pub struct MultiTapData {
    /// Number of taps detected.
    pub tap_count: u32,
    /// Position of the final tap.
    pub position: Point,
}

/// Actions emitted by the multi-tap state machine.
#[derive(Clone, Debug)]
pub enum MultiTapAction {
    /// Single tap detected (may become part of multi-tap).
    TapDetected { position: Point },
    /// Request timeout timer.
    RequestTimer { duration_ms: f64, timer_id: u32 },
    /// Multi-tap completed (required taps reached).
    Completed {
        data: MultiTapData,
        haptic: HapticFeedback,
    },
    /// Sequence failed (timeout or moved too far).
    Failed,
}

/// Result of a multi-tap state machine step.
#[derive(Clone, Debug)]
pub struct MultiTapStepResult {
    /// New state.
    pub state: MultiTapState,
    /// Actions to emit.
    pub actions: Vec<MultiTapAction>,
}

/// Pure state machine step for multi-tap gesture.
pub fn multi_tap_step(
    state: MultiTapState,
    input: &GestureInput,
    config: &MultiTapConfig,
) -> MultiTapStepResult {
    match (&state, input) {
        // Idle -> first tap on pointer up
        (
            MultiTapState::Idle,
            GestureInput::PointerUp {
                position, time_ms, ..
            },
        ) => {
            if config.required_taps == 1 {
                // Single tap mode — complete immediately
                MultiTapStepResult {
                    state: MultiTapState::Idle,
                    actions: vec![MultiTapAction::Completed {
                        data: MultiTapData {
                            tap_count: 1,
                            position: *position,
                        },
                        haptic: HapticFeedback::tap(),
                    }],
                }
            } else {
                // Need more taps — start waiting
                let timer_id = next_timer_id();
                MultiTapStepResult {
                    state: MultiTapState::Waiting {
                        tap_count: 1,
                        last_position: *position,
                        last_time: *time_ms,
                        timer_id,
                    },
                    actions: vec![
                        MultiTapAction::TapDetected {
                            position: *position,
                        },
                        MultiTapAction::RequestTimer {
                            duration_ms: config.max_delay,
                            timer_id,
                        },
                    ],
                }
            }
        }

        // Waiting -> check subsequent tap
        (
            MultiTapState::Waiting {
                tap_count,
                last_position,
                last_time,
                ..
            },
            GestureInput::PointerUp {
                position, time_ms, ..
            },
        ) => {
            let distance = last_position.distance_to(position);
            let elapsed = time_ms - last_time;

            if elapsed <= config.max_delay && distance <= config.max_distance {
                let new_count = tap_count + 1;

                if new_count >= config.required_taps {
                    // Required taps reached — complete
                    MultiTapStepResult {
                        state: MultiTapState::Idle,
                        actions: vec![MultiTapAction::Completed {
                            data: MultiTapData {
                                tap_count: new_count,
                                position: *position,
                            },
                            haptic: HapticFeedback::tap(),
                        }],
                    }
                } else {
                    // Need more taps — keep waiting
                    let timer_id = next_timer_id();
                    MultiTapStepResult {
                        state: MultiTapState::Waiting {
                            tap_count: new_count,
                            last_position: *position,
                            last_time: *time_ms,
                            timer_id,
                        },
                        actions: vec![
                            MultiTapAction::TapDetected {
                                position: *position,
                            },
                            MultiTapAction::RequestTimer {
                                duration_ms: config.max_delay,
                                timer_id,
                            },
                        ],
                    }
                }
            } else {
                // Too slow or too far — this is a new first tap
                let timer_id = next_timer_id();
                MultiTapStepResult {
                    state: MultiTapState::Waiting {
                        tap_count: 1,
                        last_position: *position,
                        last_time: *time_ms,
                        timer_id,
                    },
                    actions: vec![
                        MultiTapAction::Failed,
                        MultiTapAction::TapDetected {
                            position: *position,
                        },
                        MultiTapAction::RequestTimer {
                            duration_ms: config.max_delay,
                            timer_id,
                        },
                    ],
                }
            }
        }

        // Waiting -> timeout (timer fired)
        (
            MultiTapState::Waiting {
                timer_id: expected_id,
                ..
            },
            GestureInput::TimerFired { timer_id },
        ) if timer_id == expected_id => MultiTapStepResult {
            state: MultiTapState::Idle,
            actions: vec![MultiTapAction::Failed],
        },

        // Default: no state change
        _ => MultiTapStepResult {
            state,
            actions: vec![],
        },
    }
}
