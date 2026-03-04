//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                               // hydrogen // gesture // sequence
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! # Sequence Gesture Recognition
//!
//! Pure state machines for pattern-based gestures following the libevring pattern:
//!
//! ```text
//! step :: State -> Event -> (State, [Action])
//! ```
//!
//! ## Gestures Implemented
//!
//! - **Konami**: Classic direction sequence (up, up, down, down, left, right, left, right)
//! - **Spiral**: Circular drawing motion (inward or outward)
//! - **MultiFingerSwipe**: Coordinated swipe with multiple fingers
//! - **RhythmTap**: Taps matching a specific tempo/pattern
//!
//! ## Pattern Recognition
//!
//! These gestures track sequences of simpler gestures (swipes, taps) and
//! detect when they match predefined or custom patterns.
//!
//! ─────────────────────────────────────────────────────────────────────────────

use super::common::{
    clamp, detect_swipe_direction, normalize_angle, HapticFeedback, Point, SwipeDirection,
    TimestampedPoint,
};
use super::touch::GestureInput;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // konami gesture
// ═══════════════════════════════════════════════════════════════════════════════

/// A direction in the Konami sequence.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KonamiDirection {
    Up,
    Down,
    Left,
    Right,
}

impl From<SwipeDirection> for KonamiDirection {
    fn from(swipe: SwipeDirection) -> Self {
        match swipe {
            SwipeDirection::Up => KonamiDirection::Up,
            SwipeDirection::Down => KonamiDirection::Down,
            SwipeDirection::Left => KonamiDirection::Left,
            SwipeDirection::Right => KonamiDirection::Right,
        }
    }
}

/// The classic Konami code sequence.
pub const KONAMI_SEQUENCE: [KonamiDirection; 8] = [
    KonamiDirection::Up,
    KonamiDirection::Up,
    KonamiDirection::Down,
    KonamiDirection::Down,
    KonamiDirection::Left,
    KonamiDirection::Right,
    KonamiDirection::Left,
    KonamiDirection::Right,
];

/// Configuration for Konami gesture recognition.
#[derive(Clone, Debug)]
pub struct KonamiConfig {
    /// The sequence to match.
    pub sequence: Vec<KonamiDirection>,
    /// Maximum time between inputs (ms).
    pub max_delay_ms: f64,
    /// Minimum swipe distance to register (pixels).
    pub min_swipe_distance: f64,
    /// Minimum swipe velocity (pixels/second).
    pub min_velocity: f64,
}

impl Default for KonamiConfig {
    fn default() -> Self {
        KonamiConfig {
            sequence: KONAMI_SEQUENCE.to_vec(),
            max_delay_ms: 2000.0,
            min_swipe_distance: 50.0,
            min_velocity: 200.0,
        }
    }
}

/// Konami gesture state.
#[derive(Clone, Debug)]
pub struct KonamiState {
    /// Current position in the sequence.
    pub sequence_index: usize,
    /// Time of last valid input (ms).
    pub last_input_ms: f64,
    /// Start position for tracking current swipe.
    pub swipe_start: Option<Point>,
    /// Start time for current swipe.
    pub swipe_start_ms: f64,
}

impl Default for KonamiState {
    fn default() -> Self {
        KonamiState {
            sequence_index: 0,
            last_input_ms: 0.0,
            swipe_start: None,
            swipe_start_ms: 0.0,
        }
    }
}

/// Actions emitted by the Konami state machine.
#[derive(Clone, Debug)]
pub enum KonamiAction {
    /// Progress in the sequence.
    Progress { index: usize, total: usize },
    /// Sequence completed.
    Completed { haptic: HapticFeedback },
    /// Sequence failed (wrong direction or timeout).
    Failed,
}

/// Result of a Konami state machine step.
#[derive(Clone, Debug)]
pub struct KonamiStepResult {
    /// New state.
    pub state: KonamiState,
    /// Actions to emit.
    pub actions: Vec<KonamiAction>,
}

/// Pure state machine step for Konami gesture.
pub fn konami_step(
    state: KonamiState,
    input: &GestureInput,
    config: &KonamiConfig,
) -> KonamiStepResult {
    match input {
        GestureInput::PointerDown {
            position, time_ms, ..
        } => {
            // Check timeout
            if state.sequence_index > 0 && *time_ms - state.last_input_ms > config.max_delay_ms {
                // Timeout, restart
                return KonamiStepResult {
                    state: KonamiState {
                        sequence_index: 0,
                        last_input_ms: 0.0,
                        swipe_start: Some(*position),
                        swipe_start_ms: *time_ms,
                    },
                    actions: vec![KonamiAction::Failed],
                };
            }

            KonamiStepResult {
                state: KonamiState {
                    swipe_start: Some(*position),
                    swipe_start_ms: *time_ms,
                    ..state
                },
                actions: vec![],
            }
        }

        GestureInput::PointerUp {
            position, time_ms, ..
        } => {
            let swipe_start = match state.swipe_start {
                Some(start) => start,
                None => {
                    return KonamiStepResult {
                        state,
                        actions: vec![],
                    }
                }
            };

            let dx = position.x - swipe_start.x;
            let dy = position.y - swipe_start.y;
            let distance = (dx * dx + dy * dy).sqrt();
            let duration_sec = (*time_ms - state.swipe_start_ms) / 1000.0;
            let velocity = if duration_sec > 0.0 {
                distance / duration_sec
            } else {
                0.0
            };

            // Check if this is a valid swipe
            if distance < config.min_swipe_distance || velocity < config.min_velocity {
                return KonamiStepResult {
                    state: KonamiState {
                        swipe_start: None,
                        ..state
                    },
                    actions: vec![],
                };
            }

            let swipe_direction = detect_swipe_direction(dx, dy);
            let konami_direction: KonamiDirection = swipe_direction.into();

            // Check if direction matches expected
            if state.sequence_index < config.sequence.len()
                && konami_direction == config.sequence[state.sequence_index]
            {
                let new_index = state.sequence_index + 1;

                if new_index >= config.sequence.len() {
                    // Sequence complete!
                    KonamiStepResult {
                        state: KonamiState::default(),
                        actions: vec![KonamiAction::Completed {
                            haptic: HapticFeedback::success(),
                        }],
                    }
                } else {
                    // Progress
                    KonamiStepResult {
                        state: KonamiState {
                            sequence_index: new_index,
                            last_input_ms: *time_ms,
                            swipe_start: None,
                            swipe_start_ms: 0.0,
                        },
                        actions: vec![KonamiAction::Progress {
                            index: new_index,
                            total: config.sequence.len(),
                        }],
                    }
                }
            } else {
                // Wrong direction, check if it matches start of sequence
                if konami_direction == config.sequence[0] {
                    KonamiStepResult {
                        state: KonamiState {
                            sequence_index: 1,
                            last_input_ms: *time_ms,
                            swipe_start: None,
                            swipe_start_ms: 0.0,
                        },
                        actions: vec![
                            KonamiAction::Failed,
                            KonamiAction::Progress {
                                index: 1,
                                total: config.sequence.len(),
                            },
                        ],
                    }
                } else {
                    KonamiStepResult {
                        state: KonamiState::default(),
                        actions: vec![KonamiAction::Failed],
                    }
                }
            }
        }

        _ => KonamiStepResult {
            state,
            actions: vec![],
        },
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // spiral gesture
// ═══════════════════════════════════════════════════════════════════════════════

/// Spiral direction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SpiralDirection {
    /// Spiraling inward (decreasing radius).
    Inward,
    /// Spiraling outward (increasing radius).
    Outward,
}

/// Spiral rotation direction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SpiralRotation {
    Clockwise,
    CounterClockwise,
}

/// Configuration for spiral gesture recognition.
#[derive(Clone, Debug)]
pub struct SpiralConfig {
    /// Minimum points to sample for spiral detection.
    pub min_samples: usize,
    /// Required rotations to detect spiral (1.0 = full circle).
    pub min_rotations: f64,
    /// Minimum radius change to confirm spiral direction (pixels).
    pub min_radius_change: f64,
}

impl Default for SpiralConfig {
    fn default() -> Self {
        SpiralConfig {
            min_samples: 20,
            min_rotations: 1.0,
            min_radius_change: 30.0,
        }
    }
}

/// Spiral gesture state.
#[derive(Clone, Debug)]
pub struct SpiralState {
    /// Center point of spiral (approximated).
    pub center: Option<Point>,
    /// Sampled points during gesture.
    pub samples: Vec<TimestampedPoint>,
    /// Accumulated angle change (radians).
    pub accumulated_angle: f64,
    /// Initial radius.
    pub initial_radius: f64,
    /// Current radius.
    pub current_radius: f64,
    /// Detected rotation direction.
    pub rotation: Option<SpiralRotation>,
    /// Whether actively tracking.
    pub active: bool,
}

impl Default for SpiralState {
    fn default() -> Self {
        SpiralState {
            center: None,
            samples: Vec::new(),
            accumulated_angle: 0.0,
            initial_radius: 0.0,
            current_radius: 0.0,
            rotation: None,
            active: false,
        }
    }
}

/// Data included with spiral actions.
#[derive(Clone, Debug)]
pub struct SpiralData {
    /// Spiral direction (inward/outward).
    pub direction: SpiralDirection,
    /// Rotation direction (clockwise/counter-clockwise).
    pub rotation: SpiralRotation,
    /// Total rotations completed.
    pub rotations: f64,
    /// Center point.
    pub center: Point,
}

/// Actions emitted by the spiral state machine.
#[derive(Clone, Debug)]
pub enum SpiralAction {
    /// Spiral detected.
    Detected {
        data: SpiralData,
        haptic: HapticFeedback,
    },
}

/// Result of a spiral state machine step.
#[derive(Clone, Debug)]
pub struct SpiralStepResult {
    /// New state.
    pub state: SpiralState,
    /// Actions to emit.
    pub actions: Vec<SpiralAction>,
}

/// Compute the approximate center from a set of points.
fn compute_center(samples: &[TimestampedPoint]) -> Point {
    if samples.is_empty() {
        return Point::default();
    }
    let sum_x: f64 = samples.iter().map(|s| s.point.x).sum();
    let sum_y: f64 = samples.iter().map(|s| s.point.y).sum();
    let n = samples.len() as f64;
    Point::new(sum_x / n, sum_y / n)
}

/// Pure state machine step for spiral gesture.
pub fn spiral_step(
    state: SpiralState,
    input: &GestureInput,
    config: &SpiralConfig,
) -> SpiralStepResult {
    match input {
        GestureInput::PointerDown {
            position, time_ms, ..
        } => SpiralStepResult {
            state: SpiralState {
                center: None,
                samples: vec![TimestampedPoint {
                    point: *position,
                    time_ms: *time_ms,
                }],
                accumulated_angle: 0.0,
                initial_radius: 0.0,
                current_radius: 0.0,
                rotation: None,
                active: true,
            },
            actions: vec![],
        },

        GestureInput::PointerMove {
            position, time_ms, ..
        } => {
            if !state.active {
                return SpiralStepResult {
                    state,
                    actions: vec![],
                };
            }

            let mut new_samples = state.samples.clone();
            new_samples.push(TimestampedPoint {
                point: *position,
                time_ms: *time_ms,
            });

            // Keep samples bounded
            if new_samples.len() > 100 {
                new_samples.remove(0);
            }

            // Need enough samples to detect spiral
            if new_samples.len() < config.min_samples {
                return SpiralStepResult {
                    state: SpiralState {
                        samples: new_samples,
                        ..state
                    },
                    actions: vec![],
                };
            }

            // Compute center from samples
            let center = compute_center(&new_samples);

            // Compute angle changes
            let mut accumulated_angle = 0.0;
            let mut last_angle: Option<f64> = None;

            for sample in &new_samples {
                let dx = sample.point.x - center.x;
                let dy = sample.point.y - center.y;
                let angle = dy.atan2(dx);

                if let Some(prev) = last_angle {
                    let mut delta = angle - prev;
                    // Normalize to [-PI, PI]
                    delta = normalize_angle(delta.to_degrees()).to_radians();
                    accumulated_angle += delta;
                }
                last_angle = Some(angle);
            }

            // Determine rotation direction
            let rotation = if accumulated_angle > 0.0 {
                SpiralRotation::CounterClockwise
            } else {
                SpiralRotation::Clockwise
            };

            // Compute initial and current radius
            let first_sample = &new_samples[0];
            let initial_radius = first_sample.point.distance_to(&center);
            let current_radius = position.distance_to(&center);

            SpiralStepResult {
                state: SpiralState {
                    center: Some(center),
                    samples: new_samples,
                    accumulated_angle,
                    initial_radius,
                    current_radius,
                    rotation: Some(rotation),
                    active: true,
                },
                actions: vec![],
            }
        }

        GestureInput::PointerUp { .. } => {
            if !state.active {
                return SpiralStepResult {
                    state: SpiralState::default(),
                    actions: vec![],
                };
            }

            let rotations = state.accumulated_angle.abs() / (2.0 * std::f64::consts::PI);
            let radius_change = state.current_radius - state.initial_radius;

            // Check if spiral detected
            if rotations >= config.min_rotations && radius_change.abs() >= config.min_radius_change
            {
                let direction = if radius_change < 0.0 {
                    SpiralDirection::Inward
                } else {
                    SpiralDirection::Outward
                };

                let rotation = state.rotation.unwrap_or(SpiralRotation::Clockwise);
                let center = state.center.unwrap_or_default();

                SpiralStepResult {
                    state: SpiralState::default(),
                    actions: vec![SpiralAction::Detected {
                        data: SpiralData {
                            direction,
                            rotation,
                            rotations,
                            center,
                        },
                        haptic: HapticFeedback::success(),
                    }],
                }
            } else {
                SpiralStepResult {
                    state: SpiralState::default(),
                    actions: vec![],
                }
            }
        }

        GestureInput::PointerCancel { .. } => SpiralStepResult {
            state: SpiralState::default(),
            actions: vec![],
        },

        _ => SpiralStepResult {
            state,
            actions: vec![],
        },
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                       // multi-finger swipe gesture
// ═══════════════════════════════════════════════════════════════════════════════

/// Configuration for multi-finger swipe gesture.
#[derive(Clone, Debug)]
pub struct MultiFingerSwipeConfig {
    /// Required number of fingers.
    pub finger_count: u32,
    /// Minimum distance for swipe (pixels).
    pub min_distance: f64,
    /// Minimum velocity (pixels/second).
    pub min_velocity: f64,
    /// Maximum time between finger touches to be considered simultaneous (ms).
    pub simultaneity_window_ms: f64,
    /// Maximum angle deviation between fingers (degrees).
    pub max_angle_deviation: f64,
}

impl Default for MultiFingerSwipeConfig {
    fn default() -> Self {
        MultiFingerSwipeConfig {
            finger_count: 3,
            min_distance: 80.0,
            min_velocity: 300.0,
            simultaneity_window_ms: 100.0,
            max_angle_deviation: 30.0,
        }
    }
}

/// Tracking data for a single finger in multi-finger swipe.
#[derive(Clone, Debug)]
pub struct FingerTrack {
    pub pointer_id: i32,
    pub start: Point,
    pub start_time_ms: f64,
    pub current: Point,
    pub current_time_ms: f64,
}

/// Multi-finger swipe gesture state.
#[derive(Clone, Debug)]
pub struct MultiFingerSwipeState {
    /// Active finger tracks.
    pub fingers: Vec<FingerTrack>,
}

impl Default for MultiFingerSwipeState {
    fn default() -> Self {
        MultiFingerSwipeState {
            fingers: Vec::new(),
        }
    }
}

/// Data included with multi-finger swipe actions.
#[derive(Clone, Debug)]
pub struct MultiFingerSwipeData {
    /// Swipe direction.
    pub direction: SwipeDirection,
    /// Number of fingers.
    pub finger_count: u32,
    /// Average velocity (pixels/second).
    pub velocity: f64,
}

/// Actions emitted by the multi-finger swipe state machine.
#[derive(Clone, Debug)]
pub enum MultiFingerSwipeAction {
    /// Multi-finger swipe detected.
    Detected {
        data: MultiFingerSwipeData,
        haptic: HapticFeedback,
    },
}

/// Result of a multi-finger swipe state machine step.
#[derive(Clone, Debug)]
pub struct MultiFingerSwipeStepResult {
    /// New state.
    pub state: MultiFingerSwipeState,
    /// Actions to emit.
    pub actions: Vec<MultiFingerSwipeAction>,
}

/// Pure state machine step for multi-finger swipe gesture.
pub fn multi_finger_swipe_step(
    state: MultiFingerSwipeState,
    input: &GestureInput,
    config: &MultiFingerSwipeConfig,
) -> MultiFingerSwipeStepResult {
    match input {
        GestureInput::PointerDown {
            position,
            time_ms,
            pointer_id,
        } => {
            let mut new_fingers = state.fingers.clone();

            // Remove stale fingers (outside simultaneity window)
            if let Some(first) = new_fingers.first() {
                if *time_ms - first.start_time_ms > config.simultaneity_window_ms {
                    new_fingers.clear();
                }
            }

            new_fingers.push(FingerTrack {
                pointer_id: *pointer_id,
                start: *position,
                start_time_ms: *time_ms,
                current: *position,
                current_time_ms: *time_ms,
            });

            MultiFingerSwipeStepResult {
                state: MultiFingerSwipeState {
                    fingers: new_fingers,
                },
                actions: vec![],
            }
        }

        GestureInput::PointerMove {
            position,
            time_ms,
            pointer_id,
        } => {
            let mut new_fingers = state.fingers.clone();

            if let Some(finger) = new_fingers.iter_mut().find(|f| f.pointer_id == *pointer_id) {
                finger.current = *position;
                finger.current_time_ms = *time_ms;
            }

            MultiFingerSwipeStepResult {
                state: MultiFingerSwipeState {
                    fingers: new_fingers,
                },
                actions: vec![],
            }
        }

        GestureInput::PointerUp { pointer_id, .. } => {
            // Check if we have enough fingers
            if state.fingers.len() < config.finger_count as usize {
                // Remove this finger and continue
                let new_fingers: Vec<_> = state
                    .fingers
                    .iter()
                    .filter(|f| f.pointer_id != *pointer_id)
                    .cloned()
                    .collect();

                return MultiFingerSwipeStepResult {
                    state: MultiFingerSwipeState {
                        fingers: new_fingers,
                    },
                    actions: vec![],
                };
            }

            // Check if all fingers swiped in same direction
            let mut total_dx = 0.0;
            let mut total_dy = 0.0;
            let mut total_velocity = 0.0;
            let mut angles: Vec<f64> = Vec::new();

            for finger in &state.fingers {
                let dx = finger.current.x - finger.start.x;
                let dy = finger.current.y - finger.start.y;
                let distance = (dx * dx + dy * dy).sqrt();
                let duration_sec = (finger.current_time_ms - finger.start_time_ms) / 1000.0;

                if distance < config.min_distance {
                    // Not a valid swipe
                    return MultiFingerSwipeStepResult {
                        state: MultiFingerSwipeState::default(),
                        actions: vec![],
                    };
                }

                let velocity = if duration_sec > 0.0 {
                    distance / duration_sec
                } else {
                    0.0
                };

                if velocity < config.min_velocity {
                    return MultiFingerSwipeStepResult {
                        state: MultiFingerSwipeState::default(),
                        actions: vec![],
                    };
                }

                total_dx += dx;
                total_dy += dy;
                total_velocity += velocity;
                angles.push(dy.atan2(dx).to_degrees());
            }

            // Check angle consistency
            if angles.len() >= 2 {
                let avg_angle: f64 = angles.iter().sum::<f64>() / angles.len() as f64;
                for angle in &angles {
                    let deviation = normalize_angle(*angle - avg_angle).abs();
                    if deviation > config.max_angle_deviation {
                        return MultiFingerSwipeStepResult {
                            state: MultiFingerSwipeState::default(),
                            actions: vec![],
                        };
                    }
                }
            }

            let avg_velocity = total_velocity / state.fingers.len() as f64;
            let direction = detect_swipe_direction(total_dx, total_dy);

            MultiFingerSwipeStepResult {
                state: MultiFingerSwipeState::default(),
                actions: vec![MultiFingerSwipeAction::Detected {
                    data: MultiFingerSwipeData {
                        direction,
                        finger_count: state.fingers.len() as u32,
                        velocity: avg_velocity,
                    },
                    haptic: HapticFeedback::tap(),
                }],
            }
        }

        GestureInput::PointerCancel { pointer_id } => {
            let new_fingers: Vec<_> = state
                .fingers
                .iter()
                .filter(|f| f.pointer_id != *pointer_id)
                .cloned()
                .collect();

            MultiFingerSwipeStepResult {
                state: MultiFingerSwipeState {
                    fingers: new_fingers,
                },
                actions: vec![],
            }
        }

        _ => MultiFingerSwipeStepResult {
            state,
            actions: vec![],
        },
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // rhythm tap gesture
// ═══════════════════════════════════════════════════════════════════════════════

/// Configuration for rhythm tap gesture.
#[derive(Clone, Debug)]
pub struct RhythmTapConfig {
    /// Target BPM (beats per minute).
    pub target_bpm: f64,
    /// Tolerance for timing (percentage, 0.0-1.0).
    pub timing_tolerance: f64,
    /// Required consecutive on-beat taps to trigger.
    pub required_beats: u32,
    /// Maximum time to wait for next tap (ms).
    pub timeout_ms: f64,
}

impl Default for RhythmTapConfig {
    fn default() -> Self {
        RhythmTapConfig {
            target_bpm: 120.0,     // 2 beats per second
            timing_tolerance: 0.2, // 20% timing tolerance
            required_beats: 4,
            timeout_ms: 2000.0,
        }
    }
}

impl RhythmTapConfig {
    /// Get the beat interval in milliseconds.
    pub fn beat_interval_ms(&self) -> f64 {
        60000.0 / self.target_bpm
    }
}

/// Rhythm tap gesture state.
#[derive(Clone, Debug)]
pub struct RhythmTapState {
    /// Times of recent taps (ms).
    pub tap_times: Vec<f64>,
    /// Consecutive on-beat taps.
    pub on_beat_count: u32,
    /// Whether we're actively tracking rhythm.
    pub active: bool,
}

impl Default for RhythmTapState {
    fn default() -> Self {
        RhythmTapState {
            tap_times: Vec::new(),
            on_beat_count: 0,
            active: false,
        }
    }
}

/// Data included with rhythm tap actions.
#[derive(Clone, Debug)]
pub struct RhythmTapData {
    /// Detected BPM.
    pub detected_bpm: f64,
    /// Number of beats matched.
    pub beats_matched: u32,
    /// Timing accuracy (0.0-1.0).
    pub accuracy: f64,
}

/// Actions emitted by the rhythm tap state machine.
#[derive(Clone, Debug)]
pub enum RhythmTapAction {
    /// Beat detected (on tempo).
    BeatDetected { beat_number: u32, accuracy: f64 },
    /// Rhythm pattern completed.
    Completed {
        data: RhythmTapData,
        haptic: HapticFeedback,
    },
    /// Off-beat tap (rhythm broken).
    OffBeat,
    /// Timeout (too long between taps).
    Timeout,
}

/// Result of a rhythm tap state machine step.
#[derive(Clone, Debug)]
pub struct RhythmTapStepResult {
    /// New state.
    pub state: RhythmTapState,
    /// Actions to emit.
    pub actions: Vec<RhythmTapAction>,
}

/// Pure state machine step for rhythm tap gesture.
pub fn rhythm_tap_step(
    state: RhythmTapState,
    input: &GestureInput,
    config: &RhythmTapConfig,
) -> RhythmTapStepResult {
    match input {
        GestureInput::PointerDown { time_ms, .. } => {
            // Check timeout
            if let Some(last_tap) = state.tap_times.last() {
                if *time_ms - last_tap > config.timeout_ms {
                    // Timeout, restart
                    return RhythmTapStepResult {
                        state: RhythmTapState {
                            tap_times: vec![*time_ms],
                            on_beat_count: 1,
                            active: true,
                        },
                        actions: vec![RhythmTapAction::Timeout],
                    };
                }
            }

            // First tap
            if state.tap_times.is_empty() {
                return RhythmTapStepResult {
                    state: RhythmTapState {
                        tap_times: vec![*time_ms],
                        on_beat_count: 1,
                        active: true,
                    },
                    actions: vec![RhythmTapAction::BeatDetected {
                        beat_number: 1,
                        accuracy: 1.0,
                    }],
                };
            }

            let last_tap = state.tap_times.last().unwrap();
            let interval = *time_ms - last_tap;
            let expected_interval = config.beat_interval_ms();

            // Calculate timing error
            let error = (interval - expected_interval).abs() / expected_interval;
            let accuracy = clamp(1.0 - error, 0.0, 1.0);

            let mut new_tap_times = state.tap_times.clone();
            new_tap_times.push(*time_ms);

            // Keep last 10 taps
            if new_tap_times.len() > 10 {
                new_tap_times.remove(0);
            }

            if error <= config.timing_tolerance {
                // On beat!
                let new_count = state.on_beat_count + 1;

                if new_count >= config.required_beats {
                    // Calculate detected BPM from tap intervals
                    let avg_interval: f64 =
                        new_tap_times.windows(2).map(|w| w[1] - w[0]).sum::<f64>()
                            / (new_tap_times.len() - 1) as f64;
                    let detected_bpm = 60000.0 / avg_interval;

                    RhythmTapStepResult {
                        state: RhythmTapState::default(),
                        actions: vec![RhythmTapAction::Completed {
                            data: RhythmTapData {
                                detected_bpm,
                                beats_matched: new_count,
                                accuracy,
                            },
                            haptic: HapticFeedback::success(),
                        }],
                    }
                } else {
                    RhythmTapStepResult {
                        state: RhythmTapState {
                            tap_times: new_tap_times,
                            on_beat_count: new_count,
                            active: true,
                        },
                        actions: vec![RhythmTapAction::BeatDetected {
                            beat_number: new_count,
                            accuracy,
                        }],
                    }
                }
            } else {
                // Off beat, restart
                RhythmTapStepResult {
                    state: RhythmTapState {
                        tap_times: vec![*time_ms],
                        on_beat_count: 1,
                        active: true,
                    },
                    actions: vec![RhythmTapAction::OffBeat],
                }
            }
        }

        _ => RhythmTapStepResult {
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
    fn test_konami_sequence() {
        let config = KonamiConfig::default();
        let mut state = KonamiState::default();

        // Simulate the Konami code: up, up, down, down, left, right, left, right
        let directions = [
            (0.0, -100.0), // Up
            (0.0, -100.0), // Up
            (0.0, 100.0),  // Down
            (0.0, 100.0),  // Down
            (-100.0, 0.0), // Left
            (100.0, 0.0),  // Right
            (-100.0, 0.0), // Left
            (100.0, 0.0),  // Right
        ];

        for (i, (dx, dy)) in directions.iter().enumerate() {
            let time = (i as f64) * 200.0 + 1000.0;

            // Pointer down
            let down = GestureInput::PointerDown {
                position: Point::new(200.0, 200.0),
                time_ms: time,
                pointer_id: 0,
            };
            let result = konami_step(state, &down, &config);
            state = result.state;

            // Pointer up with swipe
            let up = GestureInput::PointerUp {
                position: Point::new(200.0 + dx, 200.0 + dy),
                time_ms: time + 100.0,
                pointer_id: 0,
            };
            let result = konami_step(state, &up, &config);
            state = result.state;

            if result
                .actions
                .iter()
                .any(|a| matches!(a, KonamiAction::Completed { .. }))
            {
                assert_eq!(i, 7, "Konami should complete on last input");
                return;
            }
        }
        panic!("Konami should have been detected");
    }

    #[test]
    fn test_rhythm_tap_detection() {
        let config = RhythmTapConfig {
            target_bpm: 120.0, // 500ms per beat
            timing_tolerance: 0.2,
            required_beats: 4,
            timeout_ms: 2000.0,
        };
        let mut state = RhythmTapState::default();

        // Tap at 120 BPM (500ms intervals)
        let times = [0.0, 500.0, 1000.0, 1500.0];

        for time in times {
            let input = GestureInput::PointerDown {
                position: Point::new(100.0, 100.0),
                time_ms: time,
                pointer_id: 0,
            };
            let result = rhythm_tap_step(state, &input, &config);
            state = result.state;

            if result
                .actions
                .iter()
                .any(|a| matches!(a, RhythmTapAction::Completed { .. }))
            {
                return;
            }
        }
        panic!("Rhythm should have been detected");
    }
}
