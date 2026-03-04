//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                                    // hydrogen // gesture // vr
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! # VR/XR Gesture Recognition
//!
//! Hand tracking, head tracking, and eye tracking for immersive environments.
//!
//! ## Hand Gestures
//! - Pinch (thumb + index) - select
//! - Grab/Fist - grab objects
//! - Point - ray casting
//! - Open Palm - UI surfaces, stop
//! - Thumbs Up/Down - approval/rejection
//!
//! ## Two-Handed Gestures  
//! - Stretch/Compress - scale objects
//! - Twist - rotate objects
//! - Clap - trigger action
//! - Frame - screenshot
//!
//! ## Head/Eye Tracking
//! - Nod/Shake - yes/no
//! - Gaze Dwell - select by looking
//! - Wink - quick action

use super::common::*;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // finger pose
// ═══════════════════════════════════════════════════════════════════════════════

/// Individual finger identifier.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Finger {
    Thumb,
    Index,
    Middle,
    Ring,
    Pinky,
}

/// Pose of a single finger (curl amount and direction).
#[derive(Clone, Copy, Debug, Default)]
pub struct FingerPose {
    /// Curl amount (0.0 = extended, 1.0 = fully curled).
    pub curl: f64,
    /// Spread from neighboring finger (-1.0 to 1.0).
    pub spread: f64,
    /// Tip position in hand-local space.
    pub tip_position: Point3D,
}

/// Full hand pose with all fingers.
#[derive(Clone, Debug, Default)]
pub struct HandPose {
    /// Hand position in world space.
    pub position: Point3D,
    /// Hand rotation.
    pub rotation: Quaternion,
    /// Individual finger poses [thumb, index, middle, ring, pinky].
    pub fingers: [FingerPose; 5],
    /// Confidence of tracking (0.0 - 1.0).
    pub confidence: f64,
}

impl HandPose {
    /// Check if hand is in pinch pose (thumb + index close together).
    pub fn is_pinching(&self, threshold: f64) -> bool {
        let thumb_tip = self.fingers[0].tip_position;
        let index_tip = self.fingers[1].tip_position;
        thumb_tip.distance_to(&index_tip) < threshold
    }

    /// Check if hand is in fist/grab pose (all fingers curled).
    pub fn is_grabbing(&self, curl_threshold: f64) -> bool {
        self.fingers.iter().all(|f| f.curl > curl_threshold)
    }

    /// Check if hand is pointing (index extended, others curled).
    pub fn is_pointing(&self, extend_thresh: f64, curl_thresh: f64) -> bool {
        self.fingers[1].curl < extend_thresh  // Index extended
            && self.fingers[2].curl > curl_thresh  // Middle curled
            && self.fingers[3].curl > curl_thresh  // Ring curled
            && self.fingers[4].curl > curl_thresh // Pinky curled
    }

    /// Check if palm is open (all fingers extended).
    pub fn is_palm_open(&self, threshold: f64) -> bool {
        self.fingers.iter().all(|f| f.curl < threshold)
    }

    /// Check for thumbs up gesture.
    pub fn is_thumbs_up(&self, thumb_extend: f64, others_curl: f64) -> bool {
        self.fingers[0].curl < thumb_extend  // Thumb extended
            && self.fingers[1].curl > others_curl
            && self.fingers[2].curl > others_curl
            && self.fingers[3].curl > others_curl
            && self.fingers[4].curl > others_curl
    }
}

/// Which hand.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Hand {
    Left,
    Right,
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                         // hand gesture input
// ═══════════════════════════════════════════════════════════════════════════════

/// Input event from hand tracking.
#[derive(Clone, Debug)]
pub enum HandInput {
    /// Hand tracking update.
    PoseUpdate {
        hand: Hand,
        pose: HandPose,
        time_ms: f64,
    },
    /// Hand tracking lost.
    TrackingLost { hand: Hand },
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                       // pinch gesture (VR)
// ═══════════════════════════════════════════════════════════════════════════════

/// State for VR pinch gesture.
#[derive(Clone, Debug)]
pub enum VrPinchState {
    Idle,
    Pinching {
        hand: Hand,
        start_position: Point3D,
        current_position: Point3D,
    },
}

impl Default for VrPinchState {
    fn default() -> Self {
        VrPinchState::Idle
    }
}

/// Configuration for VR pinch gesture.
#[derive(Clone, Debug)]
pub struct VrPinchConfig {
    /// Distance threshold for pinch detection (meters).
    pub pinch_threshold: f64,
    /// Distance threshold for release detection (meters).
    pub release_threshold: f64,
}

impl Default for VrPinchConfig {
    fn default() -> Self {
        VrPinchConfig {
            pinch_threshold: 0.02,   // 2cm
            release_threshold: 0.04, // 4cm
        }
    }
}

/// Output action for VR pinch gesture.
#[derive(Clone, Debug)]
pub enum VrPinchAction {
    PinchStart {
        hand: Hand,
        position: Point3D,
        haptic: HapticFeedback,
    },
    PinchMove {
        hand: Hand,
        position: Point3D,
        delta: Point3D,
    },
    PinchEnd {
        hand: Hand,
        position: Point3D,
        haptic: HapticFeedback,
    },
}

/// Result of stepping VR pinch state machine.
pub struct VrPinchStepResult {
    pub state: VrPinchState,
    pub actions: Vec<VrPinchAction>,
}

/// Step the VR pinch gesture state machine.
pub fn vr_pinch_step(
    state: VrPinchState,
    input: &HandInput,
    config: &VrPinchConfig,
) -> VrPinchStepResult {
    match (&state, input) {
        // Idle + pose update with pinch → start pinching
        (VrPinchState::Idle, HandInput::PoseUpdate { hand, pose, .. }) => {
            if pose.is_pinching(config.pinch_threshold) {
                VrPinchStepResult {
                    state: VrPinchState::Pinching {
                        hand: *hand,
                        start_position: pose.position,
                        current_position: pose.position,
                    },
                    actions: vec![VrPinchAction::PinchStart {
                        hand: *hand,
                        position: pose.position,
                        haptic: HapticFeedback::tap(),
                    }],
                }
            } else {
                VrPinchStepResult {
                    state,
                    actions: vec![],
                }
            }
        }

        // Pinching + pose update → update or end
        (
            VrPinchState::Pinching {
                hand: pinch_hand,
                start_position,
                current_position,
            },
            HandInput::PoseUpdate { hand, pose, .. },
        ) if hand == pinch_hand => {
            if pose.is_pinching(config.release_threshold) {
                // Still pinching - update position
                let delta = Point3D {
                    x: pose.position.x - current_position.x,
                    y: pose.position.y - current_position.y,
                    z: pose.position.z - current_position.z,
                };
                VrPinchStepResult {
                    state: VrPinchState::Pinching {
                        hand: *hand,
                        start_position: *start_position,
                        current_position: pose.position,
                    },
                    actions: vec![VrPinchAction::PinchMove {
                        hand: *hand,
                        position: pose.position,
                        delta,
                    }],
                }
            } else {
                // Released
                VrPinchStepResult {
                    state: VrPinchState::Idle,
                    actions: vec![VrPinchAction::PinchEnd {
                        hand: *hand,
                        position: pose.position,
                        haptic: HapticFeedback::light_tap(),
                    }],
                }
            }
        }

        // Tracking lost while pinching → end
        (
            VrPinchState::Pinching {
                hand: pinch_hand,
                current_position,
                ..
            },
            HandInput::TrackingLost { hand },
        ) if hand == pinch_hand => VrPinchStepResult {
            state: VrPinchState::Idle,
            actions: vec![VrPinchAction::PinchEnd {
                hand: *hand,
                position: *current_position,
                haptic: HapticFeedback::error(),
            }],
        },

        _ => VrPinchStepResult {
            state,
            actions: vec![],
        },
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                        // grab gesture (VR)
// ═══════════════════════════════════════════════════════════════════════════════

/// State for VR grab gesture.
#[derive(Clone, Debug)]
pub enum VrGrabState {
    Idle,
    Grabbing {
        hand: Hand,
        start_position: Point3D,
        start_rotation: Quaternion,
    },
}

impl Default for VrGrabState {
    fn default() -> Self {
        VrGrabState::Idle
    }
}

/// Output action for VR grab gesture.
#[derive(Clone, Debug)]
pub enum VrGrabAction {
    GrabStart {
        hand: Hand,
        position: Point3D,
        haptic: HapticFeedback,
    },
    GrabMove {
        hand: Hand,
        position: Point3D,
        rotation: Quaternion,
    },
    GrabEnd {
        hand: Hand,
        velocity: Point3D,
        haptic: HapticFeedback,
    },
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                         // head tracking
// ═══════════════════════════════════════════════════════════════════════════════

/// Head pose for tracking.
#[derive(Clone, Copy, Debug, Default)]
pub struct HeadPose {
    pub position: Point3D,
    pub rotation: Quaternion,
    /// Forward direction vector.
    pub forward: Point3D,
}

/// Input event from head tracking.
#[derive(Clone, Debug)]
pub enum HeadInput {
    PoseUpdate { pose: HeadPose, time_ms: f64 },
}

/// State for nod/shake gesture.
#[derive(Clone, Debug)]
pub struct NodShakeState {
    /// Recent pitch changes for nod detection.
    pub pitch_history: Vec<f64>,
    /// Recent yaw changes for shake detection.
    pub yaw_history: Vec<f64>,
    pub last_time_ms: f64,
}

impl Default for NodShakeState {
    fn default() -> Self {
        NodShakeState {
            pitch_history: Vec::new(),
            yaw_history: Vec::new(),
            last_time_ms: 0.0,
        }
    }
}

/// Output action for nod/shake gesture.
#[derive(Clone, Debug)]
pub enum NodShakeAction {
    Nod,   // Yes
    Shake, // No
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // eye tracking
// ═══════════════════════════════════════════════════════════════════════════════

/// Eye gaze data.
#[derive(Clone, Copy, Debug, Default)]
pub struct GazeData {
    /// Gaze ray origin (eye position).
    pub origin: Point3D,
    /// Gaze ray direction.
    pub direction: Point3D,
    /// Pupil dilation (0.0 - 1.0).
    pub pupil_dilation: f64,
    /// Which eye(s) are being tracked.
    pub eyes_tracked: EyesTracked,
}

/// Which eyes are being tracked.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum EyesTracked {
    #[default]
    Both,
    LeftOnly,
    RightOnly,
    None,
}

/// Input event from eye tracking.
#[derive(Clone, Debug)]
pub enum EyeInput {
    GazeUpdate { gaze: GazeData, time_ms: f64 },
    Blink { eye: Eye, time_ms: f64 },
}

/// Which eye.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Eye {
    Left,
    Right,
    Both,
}

/// State for gaze dwell gesture.
#[derive(Clone, Debug)]
pub struct GazeDwellState {
    /// Current target being looked at.
    pub target: Option<Handle>,
    /// Time started looking at target (ms).
    pub dwell_start_ms: f64,
    /// Accumulated dwell time (ms).
    pub dwell_time_ms: f64,
}

impl Default for GazeDwellState {
    fn default() -> Self {
        GazeDwellState {
            target: None,
            dwell_start_ms: 0.0,
            dwell_time_ms: 0.0,
        }
    }
}

/// Configuration for gaze dwell.
#[derive(Clone, Debug)]
pub struct GazeDwellConfig {
    /// Time to dwell before activation (ms).
    pub dwell_duration_ms: f64,
    /// Angle threshold for "still looking at same thing" (degrees).
    pub stability_threshold_degrees: f64,
}

impl Default for GazeDwellConfig {
    fn default() -> Self {
        GazeDwellConfig {
            dwell_duration_ms: 800.0,
            stability_threshold_degrees: 2.0,
        }
    }
}

/// Output action for gaze dwell.
#[derive(Clone, Debug)]
pub enum GazeDwellAction {
    DwellProgress {
        target: Handle,
        progress: f64,
    },
    DwellActivate {
        target: Handle,
        haptic: HapticFeedback,
    },
    DwellCancel,
}

/// State for wink gesture.
#[derive(Clone, Debug)]
pub struct WinkState {
    pub last_blink_eye: Option<Eye>,
    pub last_blink_time_ms: f64,
}

impl Default for WinkState {
    fn default() -> Self {
        WinkState {
            last_blink_eye: None,
            last_blink_time_ms: 0.0,
        }
    }
}

/// Output action for wink gesture.
#[derive(Clone, Debug)]
pub enum WinkAction {
    WinkLeft,
    WinkRight,
}
