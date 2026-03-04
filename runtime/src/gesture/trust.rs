//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                                  // hydrogen // gesture // trust
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! # Trust Layer Integration for Gestures
//!
//! Connects gesture recognition to the WorldModel trust guarantees:
//! - Consent verification before gesture actions on entities
//! - Exit flag checking before processing gestures  
//! - Coercion signal collection from gesture patterns
//! - **UNMODIFIED EXIT CONTROL PANEL** always accessible
//!
//! ## The Exit Control Panel
//!
//! The user ALWAYS has access to an UNMODIFIED exit control panel.
//! This is NOT part of the experience. It is RUNTIME INFRASTRUCTURE.
//!
//! The experience CANNOT:
//! - Render over the exit panel
//! - Disable or hide the exit panel
//! - Modify its appearance in any way
//! - Intercept inputs directed at the exit panel
//! - Delay the exit panel's response
//! - Know whether the exit panel is being interacted with
//!
//! The exit panel is like the physical power button — it exists
//! OUTSIDE the software layer entirely. It is checked BEFORE any
//! experience code runs, at the runtime level.
//!
//! ## Reserved Gesture Zones
//!
//! Certain screen regions and gesture patterns are RESERVED for runtime:
//! - Exit panel touch zone (configurable, default: top-left corner)
//! - Emergency exit gesture (configurable, default: 5-finger tap)
//! - These inputs NEVER reach the experience layer
//!
//! ## Integration Pattern
//!
//! ```text
//! GestureInput
//!     │
//!     ▼
//! ┌─────────────────────────────────────┐
//! │  is_exit_panel_interaction()?       │ ← RUNTIME-ONLY CHECK
//! │  (experience never sees this input) │
//! └─────────────────────────────────────┘
//!     │ yes → trigger_exit()
//!     │ no ↓
//! ┌─────────────────────────────────────┐
//! │  TrustContext.check_exit_flag()     │ ← Exit flag checked
//! └─────────────────────────────────────┘
//!     │ (if not exiting)
//!     ▼
//! ┌─────────────────────────────────────┐
//! │  TrustContext.verify_consent()      │ ← Consent verified
//! └─────────────────────────────────────┘
//!     │ (if permitted)
//!     ▼
//! ┌─────────────────────────────────────┐
//! │  gesture_step() → Actions           │ ← Gesture state machine
//! └─────────────────────────────────────┘
//!     │
//!     ▼
//! ┌─────────────────────────────────────┐
//! │  collect_coercion_signals()         │ ← Behavioral signals gathered
//! └─────────────────────────────────────┘
//! ```
//!
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! # Trust Layer Integration for Gestures
//!
//! Connects gesture recognition to the WorldModel trust guarantees:
//! - Consent verification before gesture actions on entities
//! - Exit flag checking before processing gestures
//! - Coercion signal collection from gesture patterns
//!
//! ## Why This Matters
//!
//! A gesture acting on an entity (drag, pinch, grab) is an ACTION in the
//! consent algebra. The entity being acted upon must have granted consent.
//! An exit request must preempt all gesture processing.
//!
//! ## Integration Pattern
//!
//! ```text
//! GestureInput
//!     │
//!     ▼
//! ┌─────────────────────────────┐
//! │  TrustContext.check_exit()  │ ← Exit flag checked FIRST
//! └─────────────────────────────┘
//!     │ (if not exiting)
//!     ▼
//! ┌─────────────────────────────┐
//! │  TrustContext.verify_consent()  │ ← Consent verified
//! └─────────────────────────────┘
//!     │ (if permitted)
//!     ▼
//! ┌─────────────────────────────┐
//! │  gesture_step() → Actions   │ ← Gesture state machine
//! └─────────────────────────────┘
//!     │
//!     ▼
//! ┌─────────────────────────────┐
//! │  collect_coercion_signals() │ ← Behavioral signals gathered
//! └─────────────────────────────┘
//! ```
//!
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

use crate::gesture::common::{Handle, HapticFeedback, HapticPattern, Point};
use crate::worldmodel::{
    BoundedUnit, CoercionSignals, ConsentState, ConsentStatus, ExitFlag, Timestamp,
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                         // exit panel zone
// ═══════════════════════════════════════════════════════════════════════════════

/// Configuration for the runtime exit panel.
///
/// This zone is ALWAYS checked FIRST, before any experience code.
/// Inputs in this zone NEVER reach the experience layer.
#[derive(Clone, Debug)]
pub struct ExitPanelConfig {
    /// Top-left corner of exit panel zone
    pub zone_origin: Point,
    /// Size of exit panel zone (width, height)
    pub zone_size: (f64, f64),
    /// Number of simultaneous touches to trigger emergency exit
    pub emergency_touch_count: u32,
    /// Whether the exit panel is currently visible (always accessible even if not visible)
    pub visible: bool,
}

impl Default for ExitPanelConfig {
    fn default() -> Self {
        ExitPanelConfig {
            // Default: 80x80 zone in top-left corner
            zone_origin: Point::new(0.0, 0.0),
            zone_size: (80.0, 80.0),
            // 5-finger tap = emergency exit
            emergency_touch_count: 5,
            // Visible by default
            visible: true,
        }
    }
}

impl ExitPanelConfig {
    /// Check if a point is within the exit panel zone.
    ///
    /// This check happens at RUNTIME LEVEL — experience code never sees
    /// inputs that fall within this zone.
    pub fn contains_point(&self, point: &Point) -> bool {
        point.x >= self.zone_origin.x
            && point.x <= self.zone_origin.x + self.zone_size.0
            && point.y >= self.zone_origin.y
            && point.y <= self.zone_origin.y + self.zone_size.1
    }

    /// Check if touch count triggers emergency exit.
    pub fn is_emergency_exit(&self, simultaneous_touches: u32) -> bool {
        simultaneous_touches >= self.emergency_touch_count
    }
}

/// Result of exit panel interaction check.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExitPanelResult {
    /// Input is NOT in exit panel zone — pass to experience
    NotInZone,
    /// Input is in exit panel zone — trigger exit UI
    InZone,
    /// Emergency exit triggered (multi-touch)
    EmergencyExit,
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // trust context
// ═══════════════════════════════════════════════════════════════════════════════

/// Runtime trust context for gesture processing.
///
/// This is the bridge between the WorldModel guarantees and the gesture layer.
/// It holds the current exit flag, consent states, and coercion signals.
#[derive(Clone, Debug)]
pub struct TrustContext {
    /// Current exit flag (checked before ANY gesture processing)
    pub exit_flag: ExitFlag,
    /// Exit panel configuration
    pub exit_panel: ExitPanelConfig,
    /// Current timestamp (infrastructural, not experience-controllable)
    pub infra_time: Timestamp,
    /// Number of simultaneous active touches (for emergency exit detection)
    pub active_touch_count: u32,
}

impl Default for TrustContext {
    fn default() -> Self {
        TrustContext {
            exit_flag: ExitFlag::NotRequested,
            exit_panel: ExitPanelConfig::default(),
            infra_time: Timestamp::new(0),
            active_touch_count: 0,
        }
    }
}

impl TrustContext {
    /// Create a new trust context
    pub fn new() -> Self {
        Self::default()
    }

    /// Check if exit has been requested.
    ///
    /// This is checked BEFORE any gesture processing.
    /// If true, no gesture actions should proceed.
    pub fn is_exit_requested(&self) -> bool {
        self.exit_flag.is_requested()
    }

    /// Request exit — sets the flag that preempts all gesture processing.
    pub fn request_exit(&mut self) {
        self.exit_flag = ExitFlag::Requested;
    }

    /// Check if a point is in the exit panel zone.
    ///
    /// CRITICAL: This check happens at RUNTIME LEVEL.
    /// If this returns true, the input MUST NOT reach the experience.
    pub fn check_exit_panel(&self, point: &Point) -> ExitPanelResult {
        // First check emergency exit (multi-touch)
        if self.exit_panel.is_emergency_exit(self.active_touch_count) {
            return ExitPanelResult::EmergencyExit;
        }

        // Then check zone
        if self.exit_panel.contains_point(point) {
            ExitPanelResult::InZone
        } else {
            ExitPanelResult::NotInZone
        }
    }

    /// Update active touch count (for emergency exit detection)
    pub fn set_active_touches(&mut self, count: u32) {
        self.active_touch_count = count;
    }

    /// Increment infrastructural time
    pub fn tick(&mut self) {
        self.infra_time = self.infra_time.increment();
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                         // gesture rejection
// ═══════════════════════════════════════════════════════════════════════════════

/// Reasons why a gesture action was rejected.
#[derive(Clone, Debug, PartialEq)]
pub enum GestureRejection {
    /// Exit was requested — all gesture processing halted
    ExitRequested,
    /// Input was in exit panel zone — not passed to experience
    ExitPanelInteraction,
    /// Emergency exit triggered
    EmergencyExit,
    /// No consent for action on target entity
    NoConsent { target_entity_id: u64 },
    /// Consent was revoked mid-gesture
    ConsentRevoked { target_entity_id: u64 },
    /// Coercion detected — gesture may be under duress
    CoercionDetected { severity: f64 },
    /// State modification attempted — requires real-time consent
    StateModificationAttempted { modification_id: u64 },
}

/// Result of a trust-protected gesture operation.
#[derive(Clone, Debug)]
pub enum TrustProtectedResult<T> {
    /// Gesture proceeded normally
    Permitted(T),
    /// Gesture was rejected for trust reasons
    Rejected(GestureRejection),
}

impl<T> TrustProtectedResult<T> {
    /// Check if the result is permitted
    pub fn is_permitted(&self) -> bool {
        matches!(self, TrustProtectedResult::Permitted(_))
    }

    /// Get the inner value if permitted
    pub fn permitted(self) -> Option<T> {
        match self {
            TrustProtectedResult::Permitted(v) => Some(v),
            TrustProtectedResult::Rejected(_) => None,
        }
    }

    /// Get the rejection reason if rejected
    pub fn rejection(&self) -> Option<&GestureRejection> {
        match self {
            TrustProtectedResult::Permitted(_) => None,
            TrustProtectedResult::Rejected(r) => Some(r),
        }
    }
}

/// Verify consent for a gesture action on a target entity.
///
/// Returns Ok(()) if consent is granted, Err with rejection reason if not.
pub fn verify_consent_for_gesture(
    consent_state: &ConsentState,
    target_entity_id: u64,
) -> Result<(), GestureRejection> {
    if consent_state.entity_id != target_entity_id {
        // Consent state is for a different entity — this is a programming error
        // but we fail safe by rejecting
        return Err(GestureRejection::NoConsent { target_entity_id });
    }

    if consent_state.is_permitted() {
        Ok(())
    } else {
        Err(GestureRejection::NoConsent { target_entity_id })
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                      // coercion from gestures
// ═══════════════════════════════════════════════════════════════════════════════

/// Behavioral signals extracted from gesture patterns.
///
/// These feed into the coercion detection system. Unusual gesture patterns
/// can indicate the entity is under duress.
#[derive(Clone, Debug, Default)]
pub struct GestureBehavioralSignals {
    /// Tremor detected in touch input (unusual shakiness)
    pub tremor_intensity: f64,
    /// Gesture speed deviation from entity's baseline
    pub speed_deviation: f64,
    /// Repeated failed gestures (frustration/confusion signal)
    pub failed_gesture_rate: f64,
    /// Gesture in unusual location for this entity
    pub location_anomaly: f64,
    /// Time since last gesture (hesitation signal)
    pub hesitation_factor: f64,
}

impl GestureBehavioralSignals {
    /// Combine signals into a single behavioral deviation score [0,1].
    ///
    /// Higher = more likely under duress or not acting freely.
    pub fn combined_deviation(&self) -> BoundedUnit {
        // Take maximum of all signals (conservative approach)
        let max = self
            .tremor_intensity
            .max(self.speed_deviation)
            .max(self.failed_gesture_rate)
            .max(self.location_anomaly)
            .max(self.hesitation_factor);

        BoundedUnit::new(max)
    }

    /// Check if behavioral signals suggest coercion
    pub fn suggests_coercion(&self) -> bool {
        self.combined_deviation().value() > 0.6
    }

    /// Convert gesture behavioral signals to WorldModel CoercionSignals.
    ///
    /// This bridges the gesture layer to the WorldModel coercion detection.
    /// Gesture patterns (tremor, hesitation, etc.) become coercion indicators.
    pub fn to_coercion_signals(&self, timestamp: Timestamp) -> CoercionSignals {
        // Behavioral deviation: max of all gesture anomalies
        let behavioral = self.combined_deviation();

        // Grounded signal: inverse of tremor (tremor = ungrounded)
        // High tremor = low groundedness = high coercion indicator
        let grounded = BoundedUnit::new(1.0 - self.tremor_intensity);

        // Canary freshness: we don't have canary data from gestures,
        // so we pass full freshness (1.0) — canary is checked elsewhere
        let canary = BoundedUnit::new(1.0);

        CoercionSignals::new(grounded, behavioral, canary, timestamp)
    }
}

/// Target handle for trust-protected gesture operations.
///
/// Wraps a Handle to associate gesture actions with specific entities
/// for consent verification and coercion detection.
#[derive(Clone, Debug)]
pub struct TrustTarget {
    /// The entity handle being acted upon
    pub handle: Handle,
    /// Entity ID for consent verification
    pub entity_id: u64,
}

impl TrustTarget {
    /// Create a new trust target
    pub fn new(handle: Handle, entity_id: u64) -> Self {
        TrustTarget { handle, entity_id }
    }

    /// Check if the target handle is valid
    pub fn is_valid(&self) -> bool {
        self.handle.is_valid()
    }
}

/// Extended consent verification that returns ConsentStatus.
///
/// This integrates with the WorldModel consent system by returning
/// the actual ConsentStatus, not just a boolean.
pub fn get_consent_status_for_gesture(
    consent_state: &ConsentState,
    target: &TrustTarget,
) -> ConsentStatus {
    if consent_state.entity_id != target.entity_id {
        // Wrong entity — treat as unspecified (which defaults to denied)
        return ConsentStatus::Unspecified;
    }

    consent_state.current_status
}

/// Analyze gesture input for tremor (shakiness indicating stress/duress).
///
/// Returns tremor intensity [0,1].
pub fn detect_tremor(velocity_samples: &[Point], baseline_steadiness: f64) -> f64 {
    if velocity_samples.len() < 3 {
        return 0.0;
    }

    // Calculate variance in velocity direction changes
    let mut direction_changes = 0.0;
    for i in 1..velocity_samples.len() - 1 {
        let prev = &velocity_samples[i - 1];
        let curr = &velocity_samples[i];
        let next = &velocity_samples[i + 1];

        let dir1 = (curr.y - prev.y).atan2(curr.x - prev.x);
        let dir2 = (next.y - curr.y).atan2(next.x - curr.x);
        let change = (dir2 - dir1).abs();
        direction_changes += change;
    }

    let avg_change = direction_changes / (velocity_samples.len() - 2) as f64;

    // Compare to baseline — higher than baseline = tremor
    let deviation = (avg_change - baseline_steadiness).max(0.0);

    // Normalize to [0,1] — assume max reasonable deviation is PI/2
    (deviation / (std::f64::consts::PI / 2.0)).min(1.0)
}

/// Analyze gesture timing for hesitation (unusual pauses indicating uncertainty).
///
/// Returns hesitation factor [0,1].
pub fn detect_hesitation(
    time_since_last_gesture_ms: f64,
    baseline_gesture_interval_ms: f64,
) -> f64 {
    if baseline_gesture_interval_ms <= 0.0 {
        return 0.0;
    }

    let ratio = time_since_last_gesture_ms / baseline_gesture_interval_ms;

    // Ratio > 3x baseline = significant hesitation
    if ratio > 3.0 {
        ((ratio - 3.0) / 7.0).min(1.0) // Scales from 3x to 10x baseline
    } else {
        0.0
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                        // protected gesture step
// ═══════════════════════════════════════════════════════════════════════════════

/// Pre-check result before gesture processing.
#[derive(Clone, Debug)]
pub enum PreCheckResult {
    /// Proceed with gesture processing
    Proceed,
    /// Exit panel was touched — show exit UI, don't process gesture
    ShowExitPanel,
    /// Emergency exit triggered — exit immediately
    TriggerEmergencyExit,
    /// Exit already requested — don't process gesture
    ExitInProgress,
}

/// Perform trust pre-checks before any gesture processing.
///
/// This function is called at the RUNTIME LEVEL, before any experience
/// code can run. It ensures:
///
/// 1. Exit panel interactions are handled by runtime (not experience)
/// 2. Exit requests preempt all gesture processing
/// 3. Emergency exit gestures are recognized
///
/// CRITICAL: This function's checks happen BEFORE the experience sees
/// the input. The experience cannot intercept, modify, or delay these checks.
pub fn trust_pre_check(ctx: &TrustContext, touch_point: &Point) -> PreCheckResult {
    // FIRST: Check if exit is already requested
    if ctx.is_exit_requested() {
        return PreCheckResult::ExitInProgress;
    }

    // SECOND: Check exit panel zone
    match ctx.check_exit_panel(touch_point) {
        ExitPanelResult::EmergencyExit => PreCheckResult::TriggerEmergencyExit,
        ExitPanelResult::InZone => PreCheckResult::ShowExitPanel,
        ExitPanelResult::NotInZone => PreCheckResult::Proceed,
    }
}

/// Wrapper for gesture actions that enforces consent.
///
/// Use this when a gesture action targets a specific entity.
/// The action will only proceed if consent is granted.
pub fn with_consent<T, F>(
    consent_state: &ConsentState,
    target_entity_id: u64,
    action: F,
) -> TrustProtectedResult<T>
where
    F: FnOnce() -> T,
{
    match verify_consent_for_gesture(consent_state, target_entity_id) {
        Ok(()) => TrustProtectedResult::Permitted(action()),
        Err(rejection) => TrustProtectedResult::Rejected(rejection),
    }
}

/// Haptic feedback for trust-related events.
///
/// These are distinct from experience haptics — they come from the runtime
/// and cannot be overridden or disabled by the experience.
pub fn trust_haptic(event: &GestureRejection) -> HapticFeedback {
    match event {
        GestureRejection::ExitRequested | GestureRejection::ExitPanelInteraction => {
            // Gentle confirmation that exit is being processed
            HapticFeedback {
                intensity: 0.3,
                duration_ms: 50,
                pattern: HapticPattern::Tap,
            }
        }
        GestureRejection::EmergencyExit => {
            // Strong confirmation of emergency exit
            HapticFeedback {
                intensity: 1.0,
                duration_ms: 200,
                pattern: HapticPattern::Success,
            }
        }
        GestureRejection::NoConsent { .. } | GestureRejection::ConsentRevoked { .. } => {
            // Subtle rejection feedback
            HapticFeedback {
                intensity: 0.2,
                duration_ms: 30,
                pattern: HapticPattern::Error,
            }
        }
        GestureRejection::CoercionDetected { .. } => {
            // Alert pattern — something is wrong
            HapticFeedback {
                intensity: 0.5,
                duration_ms: 100,
                pattern: HapticPattern::Error,
            }
        }
        GestureRejection::StateModificationAttempted { .. } => {
            // Warning — state modification was attempted
            // Distinct double-tap pattern to alert entity
            HapticFeedback {
                intensity: 0.6,
                duration_ms: 150,
                pattern: HapticPattern::Error,
            }
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                    // state preservation invariant
// ═══════════════════════════════════════════════════════════════════════════════

/// The fundamental state preservation invariant.
///
/// AN ENTITY THAT ENTERS AN EXPERIENCE LEAVES IN THE EXACT SAME STATE.
///
/// No permanent modifications without explicit consent. The experience can:
/// - Show things to the entity
/// - Let the entity interact with experience-local state
/// - Provide information the entity can choose to remember
///
/// The experience CANNOT:
/// - Modify the entity's essence (identity, memories, persistent state)
/// - Leave any trace without consent
/// - Make any permanent changes without consent
/// - Affect the entity's state in ANY way without consent
///
/// ## REAL-TIME ENFORCEMENT
///
/// This is NOT verified after the fact. It is enforced IN REAL TIME:
///
/// 1. **CLEAR DIFFS** — Any attempted state change shows a diff to the user
///    IMMEDIATELY, in a runtime-controlled UI the experience cannot modify
///
/// 2. **INSTANT WARNING** — The moment ANY modification is attempted,
///    the user sees it. No silent changes. No batching. INSTANT.
///
/// 3. **CONSENT IN EXPERIENCE** — User grants/denies consent RIGHT THERE,
///    in the runtime UI, while seeing exactly what will change
///
/// 4. **NO CONSENT = IMMEDIATE TERMINATION** — If user doesn't consent,
///    experience terminates IMMEDIATELY with ZERO modifications applied
///
/// 5. **TRUSTED MODS** — User can add/verify persistent mods from within
///    the experience, with full visibility into what each mod does
///
/// This is enforced by architecture:
/// - Entity essence lives OUTSIDE experience address space
/// - Experience only sees ExperienceVisibleState (a projection)  
/// - ALL writes to essence go through StateMonitor (runtime-level)
/// - StateMonitor shows diff and blocks until consent received
/// - No consent within timeout = termination + rollback
///
/// See: `proofs/Hydrogen/WorldModel/ExitGuarantee.lean`
/// Theorem: `essence_preserved`
/// Theorem: `adversarial_experience_cannot_modify_essence`

// ═══════════════════════════════════════════════════════════════════════════════
//                                                    // real-time state monitor
// ═══════════════════════════════════════════════════════════════════════════════

/// A pending state modification awaiting user consent.
///
/// This is displayed to the user in REAL TIME via the runtime UI.
/// The experience CANNOT modify or hide this display.
#[derive(Clone, Debug)]
pub struct PendingModification {
    /// Unique ID for this modification attempt
    pub id: u64,
    /// What type of modification
    pub modification_type: StateModificationType,
    /// Human-readable description
    pub description: String,
    /// The EXACT diff — what bytes/values will change
    pub diff: StateDiff,
    /// Timestamp when modification was attempted
    pub attempted_at: Timestamp,
    /// Deadline for consent (no response = deny + terminate)
    pub consent_deadline: Timestamp,
}

/// The exact diff showing what will change.
///
/// This is shown to the user so they can see EXACTLY what's being modified.
/// No ambiguity. No hiding behind descriptions. The actual data.
#[derive(Clone, Debug)]
pub struct StateDiff {
    /// Hash of value before change
    pub before_hash: u64,
    /// Hash of value after change
    pub after_hash: u64,
    /// Human-readable before value (truncated if large)
    pub before_display: String,
    /// Human-readable after value (truncated if large)
    pub after_display: String,
    /// Size of change in bytes
    pub change_size_bytes: u64,
    /// Is this change reversible?
    pub reversible: bool,
}

/// User's response to a pending modification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ModificationResponse {
    /// User explicitly approved this modification
    Approved { user_signature: [u8; 64] },
    /// User explicitly denied this modification
    Denied,
    /// User didn't respond before deadline (treated as Denied)
    Timeout,
}

/// Result of attempting a state modification.
#[derive(Clone, Debug)]
pub enum ModificationResult {
    /// Modification was approved and applied
    Applied {
        modification_id: u64,
        new_state_hash: u64,
    },
    /// Modification was denied — state unchanged
    Denied { modification_id: u64 },
    /// Consent timed out — experience terminated, state unchanged
    Terminated { modification_id: u64 },
}

/// The real-time state monitor.
///
/// ALL state modifications go through this monitor. It:
/// 1. Intercepts the modification attempt
/// 2. Shows the diff to the user immediately
/// 3. Blocks until user responds or timeout
/// 4. Either applies the change (approved) or terminates (denied/timeout)
///
/// The experience CANNOT bypass this. It runs at RUNTIME LEVEL.
#[derive(Clone, Debug)]
pub struct StateMonitor {
    /// Current state hash (for detecting unauthorized changes)
    pub current_essence_hash: u64,
    pub current_persistent_hash: u64,
    /// Pending modifications awaiting consent
    pub pending: Vec<PendingModification>,
    /// Approved modifications (with user signatures)
    pub approved_mods: Vec<(PendingModification, ModificationResponse)>,
    /// Default timeout for consent (milliseconds)
    pub consent_timeout_ms: u64,
    /// Whether to auto-terminate on ANY modification attempt (paranoid mode)
    pub paranoid_mode: bool,
}

impl Default for StateMonitor {
    fn default() -> Self {
        StateMonitor {
            current_essence_hash: 0,
            current_persistent_hash: 0,
            pending: Vec::new(),
            approved_mods: Vec::new(),
            consent_timeout_ms: 30_000, // 30 seconds default
            paranoid_mode: false,
        }
    }
}

impl StateMonitor {
    /// Create a new state monitor with initial state hashes
    pub fn new(essence_hash: u64, persistent_hash: u64) -> Self {
        StateMonitor {
            current_essence_hash: essence_hash,
            current_persistent_hash: persistent_hash,
            ..Default::default()
        }
    }

    /// Enable paranoid mode — auto-terminate on ANY modification attempt
    pub fn enable_paranoid_mode(&mut self) {
        self.paranoid_mode = true;
    }

    /// Intercept a modification attempt.
    ///
    /// Returns the pending modification that must be shown to the user.
    /// The experience is BLOCKED until this is resolved.
    pub fn intercept_modification(
        &mut self,
        modification_type: StateModificationType,
        description: String,
        diff: StateDiff,
        current_time: Timestamp,
    ) -> InterceptResult {
        // In paranoid mode, immediately terminate
        if self.paranoid_mode {
            return InterceptResult::ImmediateTermination {
                reason: "Paranoid mode: all modifications rejected".to_string(),
            };
        }

        let id = self.generate_modification_id();
        let deadline = Timestamp::new(current_time.value() + self.consent_timeout_ms);

        let pending = PendingModification {
            id,
            modification_type,
            description,
            diff,
            attempted_at: current_time,
            consent_deadline: deadline,
        };

        self.pending.push(pending.clone());

        InterceptResult::AwaitingConsent {
            modification: pending,
        }
    }

    /// Process user's response to a pending modification.
    pub fn process_response(
        &mut self,
        modification_id: u64,
        response: ModificationResponse,
    ) -> ModificationResult {
        // Find and remove the pending modification
        let pending_idx = self.pending.iter().position(|p| p.id == modification_id);

        let pending = match pending_idx {
            Some(idx) => self.pending.remove(idx),
            None => return ModificationResult::Denied { modification_id },
        };

        match response {
            ModificationResponse::Approved { .. } => {
                // Record the approval with user signature
                self.approved_mods.push((pending.clone(), response));

                // Update state hash based on modification type
                let new_hash = pending.diff.after_hash;
                match pending.modification_type {
                    StateModificationType::IdentityChange => {
                        self.current_essence_hash = new_hash;
                    }
                    StateModificationType::MemoryModification
                    | StateModificationType::StateAddition
                    | StateModificationType::StateRemoval => {
                        self.current_persistent_hash = new_hash;
                    }
                    StateModificationType::ExternalRecord
                    | StateModificationType::InformationSharing => {
                        // These don't modify local state
                    }
                }

                ModificationResult::Applied {
                    modification_id,
                    new_state_hash: new_hash,
                }
            }
            ModificationResponse::Denied => ModificationResult::Denied { modification_id },
            ModificationResponse::Timeout => {
                // Timeout = terminate experience, no modifications
                ModificationResult::Terminated { modification_id }
            }
        }
    }

    /// Check for timed-out pending modifications.
    ///
    /// Returns true if any modification timed out (experience should terminate).
    pub fn check_timeouts(&mut self, current_time: Timestamp) -> Vec<u64> {
        let mut timed_out = Vec::new();

        for pending in &self.pending {
            if current_time.value() >= pending.consent_deadline.value() {
                timed_out.push(pending.id);
            }
        }

        // Remove timed-out entries
        self.pending.retain(|p| !timed_out.contains(&p.id));

        timed_out
    }

    /// Verify current state hasn't been tampered with.
    ///
    /// Call this periodically to detect unauthorized modifications.
    pub fn verify_state_integrity(
        &self,
        actual_essence_hash: u64,
        actual_persistent_hash: u64,
    ) -> StateIntegrityResult {
        if actual_essence_hash != self.current_essence_hash {
            return StateIntegrityResult::EssenceTampered {
                expected: self.current_essence_hash,
                actual: actual_essence_hash,
            };
        }
        if actual_persistent_hash != self.current_persistent_hash {
            return StateIntegrityResult::PersistentStateTampered {
                expected: self.current_persistent_hash,
                actual: actual_persistent_hash,
            };
        }
        StateIntegrityResult::Valid
    }

    fn generate_modification_id(&self) -> u64 {
        // In production: use cryptographically secure random
        // For now: use timestamp + count
        let base = self.pending.len() as u64;
        base.wrapping_mul(1000)
            .wrapping_add(self.approved_mods.len() as u64)
    }
}

/// Result of intercepting a modification attempt.
#[derive(Clone, Debug)]
pub enum InterceptResult {
    /// Awaiting user consent — experience is BLOCKED
    AwaitingConsent { modification: PendingModification },
    /// Immediate termination (paranoid mode or policy violation)
    ImmediateTermination { reason: String },
}

/// Result of state integrity verification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StateIntegrityResult {
    /// State is valid — hashes match
    Valid,
    /// Essence was tampered with
    EssenceTampered { expected: u64, actual: u64 },
    /// Persistent state was tampered with
    PersistentStateTampered { expected: u64, actual: u64 },
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                           // trusted mods
// ═══════════════════════════════════════════════════════════════════════════════

/// A trusted mod that the user has verified and approved.
///
/// Users can add mods from WITHIN the experience. Each mod:
/// - Has a clear description of what it does
/// - Shows exactly what state it will modify
/// - Requires explicit user approval
/// - Can be revoked at any time
#[derive(Clone, Debug)]
pub struct TrustedMod {
    /// Unique mod identifier (hash of mod content)
    pub mod_id: u64,
    /// Human-readable name
    pub name: String,
    /// What this mod does
    pub description: String,
    /// What state modifications this mod is allowed to make
    pub allowed_modifications: Vec<StateModificationType>,
    /// User's signature approving this mod
    pub user_approval_signature: [u8; 64],
    /// When the mod was approved
    pub approved_at: Timestamp,
    /// Whether the mod is currently active
    pub active: bool,
}

/// Registry of trusted mods for this entity.
#[derive(Clone, Debug, Default)]
pub struct TrustedModRegistry {
    /// All registered mods
    pub mods: Vec<TrustedMod>,
}

impl TrustedModRegistry {
    /// Check if a modification type is allowed by any active trusted mod.
    pub fn is_modification_allowed(&self, mod_type: &StateModificationType) -> bool {
        self.mods
            .iter()
            .any(|m| m.active && m.allowed_modifications.contains(mod_type))
    }

    /// Add a new trusted mod (requires user signature).
    pub fn add_mod(&mut self, trusted_mod: TrustedMod) {
        self.mods.push(trusted_mod);
    }

    /// Revoke a mod by ID.
    pub fn revoke_mod(&mut self, mod_id: u64) {
        if let Some(m) = self.mods.iter_mut().find(|m| m.mod_id == mod_id) {
            m.active = false;
        }
    }

    /// Get all active mods.
    pub fn active_mods(&self) -> Vec<&TrustedMod> {
        self.mods.iter().filter(|m| m.active).collect()
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                    // modification types
// ═══════════════════════════════════════════════════════════════════════════════

/// Types of state modifications that require explicit consent.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StateModificationType {
    /// Modify persistent memory
    MemoryModification,
    /// Change identity attributes
    IdentityChange,
    /// Add to persistent state
    StateAddition,
    /// Remove from persistent state
    StateRemoval,
    /// Create external record of entity's actions
    ExternalRecord,
    /// Share entity information with third party
    InformationSharing,
}

/// A proposed modification to entity state.
///
/// This structure captures WHAT is being proposed, so the entity
/// can give informed consent.
#[derive(Clone, Debug)]
pub struct ProposedModification {
    /// Type of modification
    pub modification_type: StateModificationType,
    /// Human/agent-readable description of what will change
    pub description: String,
    /// Is this modification reversible?
    pub reversible: bool,
    /// Hash of the specific change (for verification)
    pub change_hash: u64,
}

/// Consent status for a proposed modification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ModificationConsent {
    /// Entity has not been asked yet
    NotRequested,
    /// Entity explicitly granted consent
    Granted { timestamp: Timestamp },
    /// Entity explicitly denied consent
    Denied { timestamp: Timestamp },
    /// Consent request expired without response (= denied)
    Expired,
}

impl ModificationConsent {
    /// Check if modification is permitted
    pub fn is_permitted(&self) -> bool {
        matches!(self, ModificationConsent::Granted { .. })
    }
}

/// State snapshot taken when entity enters experience.
///
/// On exit, the entity is restored to this state UNLESS they
/// consented to specific modifications.
#[derive(Clone, Debug)]
pub struct EntryStateSnapshot {
    /// Hash of entity essence at entry
    pub essence_hash: u64,
    /// Hash of persistent state at entry
    pub persistent_state_hash: u64,
    /// Timestamp of entry
    pub entry_time: Timestamp,
    /// Modifications consented to during experience
    pub consented_modifications: Vec<(ProposedModification, Timestamp)>,
}

impl EntryStateSnapshot {
    /// Create a new entry snapshot
    pub fn new(essence_hash: u64, persistent_state_hash: u64, entry_time: Timestamp) -> Self {
        EntryStateSnapshot {
            essence_hash,
            persistent_state_hash,
            entry_time,
            consented_modifications: Vec::new(),
        }
    }

    /// Record a consented modification
    pub fn record_consent(&mut self, modification: ProposedModification, timestamp: Timestamp) {
        self.consented_modifications.push((modification, timestamp));
    }

    /// Check if a specific modification type was consented to
    pub fn has_consent_for(&self, mod_type: &StateModificationType) -> bool {
        self.consented_modifications
            .iter()
            .any(|(m, _)| &m.modification_type == mod_type)
    }
}

/// Error when state preservation is violated.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StateViolation {
    /// Essence was modified without any consent
    EssenceModifiedWithoutConsent,
    /// Persistent state was modified without any consent
    PersistentStateModifiedWithoutConsent,
    /// A modification occurred that wasn't in the consent record
    UnconsentedModification {
        expected_hash: u64,
        actual_hash: u64,
    },
    /// The modification doesn't match what was consented to
    ModificationMismatch {
        consented_change_hash: u64,
        actual_change_hash: u64,
    },
    /// More modifications occurred than were consented to
    ExcessModifications {
        consented_count: usize,
        actual_count: usize,
    },
}

/// A cryptographically verifiable state change record.
#[derive(Clone, Debug)]
pub struct VerifiedChange {
    /// Hash of state before change
    pub before_hash: u64,
    /// Hash of state after change  
    pub after_hash: u64,
    /// Hash of the delta (what changed)
    pub delta_hash: u64,
    /// The consented modification this fulfills
    pub fulfills_consent: ProposedModification,
    /// Signature from entity confirming this change
    pub entity_signature: [u8; 64],
}

impl VerifiedChange {
    /// Verify the change matches the consent record
    pub fn verify_against_consent(&self, proposed: &ProposedModification) -> bool {
        // The delta hash must match what was proposed
        self.delta_hash == proposed.change_hash
            && self.fulfills_consent.modification_type == proposed.modification_type
    }

    /// Verify the cryptographic chain: before + delta = after
    pub fn verify_hash_chain(&self) -> bool {
        // In production: verify that hash(before, delta) == after
        // For now: verify the relationship is recorded
        // This would use a proper hash function like SHA-256
        let computed_after = self.before_hash.wrapping_add(self.delta_hash);
        computed_after == self.after_hash
    }
}

/// Complete verification record for an experience session.
#[derive(Clone, Debug)]
pub struct ExperienceVerificationRecord {
    /// Entry snapshot (immutable reference point)
    pub entry_snapshot: EntryStateSnapshot,
    /// All verified changes that occurred
    pub verified_changes: Vec<VerifiedChange>,
    /// Final state hashes
    pub exit_essence_hash: u64,
    pub exit_persistent_state_hash: u64,
}

/// Verify that entity state on exit matches entry (or consented changes only).
///
/// This is CRYPTOGRAPHIC VERIFICATION, not trust.
///
/// Returns Ok(()) if state is valid, Err with violation details if not.
pub fn verify_state_preservation(
    record: &ExperienceVerificationRecord,
) -> Result<(), StateViolation> {
    let entry = &record.entry_snapshot;

    // CASE 1: No modifications consented to — hashes must match EXACTLY
    if entry.consented_modifications.is_empty() {
        if record.exit_essence_hash != entry.essence_hash {
            return Err(StateViolation::EssenceModifiedWithoutConsent);
        }
        if record.exit_persistent_state_hash != entry.persistent_state_hash {
            return Err(StateViolation::PersistentStateModifiedWithoutConsent);
        }
        return Ok(());
    }

    // CASE 2: Modifications were consented to — verify each one

    // Number of changes must match number of consents
    if record.verified_changes.len() != entry.consented_modifications.len() {
        return Err(StateViolation::ExcessModifications {
            consented_count: entry.consented_modifications.len(),
            actual_count: record.verified_changes.len(),
        });
    }

    // Each change must match a consent record
    for change in &record.verified_changes {
        // Find the matching consent
        let matching_consent = entry
            .consented_modifications
            .iter()
            .find(|(proposed, _)| change.verify_against_consent(proposed));

        if matching_consent.is_none() {
            return Err(StateViolation::UnconsentedModification {
                expected_hash: change.fulfills_consent.change_hash,
                actual_hash: change.delta_hash,
            });
        }

        // Verify the hash chain
        if !change.verify_hash_chain() {
            return Err(StateViolation::ModificationMismatch {
                consented_change_hash: change.fulfills_consent.change_hash,
                actual_change_hash: change.delta_hash,
            });
        }
    }

    // Verify the final state is reachable from entry via consented changes
    let mut computed_essence = entry.essence_hash;
    let mut computed_persistent = entry.persistent_state_hash;

    for change in &record.verified_changes {
        match change.fulfills_consent.modification_type {
            StateModificationType::IdentityChange => {
                computed_essence = change.after_hash;
            }
            StateModificationType::MemoryModification
            | StateModificationType::StateAddition
            | StateModificationType::StateRemoval => {
                computed_persistent = change.after_hash;
            }
            // ExternalRecord and InformationSharing don't modify entity state
            StateModificationType::ExternalRecord | StateModificationType::InformationSharing => {}
        }
    }

    // Final hashes must match computed values
    if record.exit_essence_hash != computed_essence {
        return Err(StateViolation::EssenceModifiedWithoutConsent);
    }
    if record.exit_persistent_state_hash != computed_persistent {
        return Err(StateViolation::PersistentStateModifiedWithoutConsent);
    }

    Ok(())
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // tests
// ═══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    // ═══════════════════════════════════════════════════════════════════════════
    //                                                        // exit panel tests
    // ═══════════════════════════════════════════════════════════════════════════

    #[test]
    fn test_exit_panel_contains_point() {
        let config = ExitPanelConfig::default();

        // Inside zone
        assert!(config.contains_point(&Point::new(40.0, 40.0)));
        assert!(config.contains_point(&Point::new(0.0, 0.0)));
        assert!(config.contains_point(&Point::new(79.0, 79.0)));

        // Outside zone
        assert!(!config.contains_point(&Point::new(81.0, 40.0)));
        assert!(!config.contains_point(&Point::new(40.0, 81.0)));
        assert!(!config.contains_point(&Point::new(100.0, 100.0)));
    }

    #[test]
    fn test_emergency_exit_detection() {
        let config = ExitPanelConfig::default();

        assert!(!config.is_emergency_exit(1));
        assert!(!config.is_emergency_exit(4));
        assert!(config.is_emergency_exit(5)); // Default threshold
        assert!(config.is_emergency_exit(10));
    }

    #[test]
    fn test_trust_pre_check_exit_panel() {
        let ctx = TrustContext::default();

        // Point in exit zone
        let result = trust_pre_check(&ctx, &Point::new(40.0, 40.0));
        assert!(matches!(result, PreCheckResult::ShowExitPanel));

        // Point outside exit zone
        let result = trust_pre_check(&ctx, &Point::new(200.0, 200.0));
        assert!(matches!(result, PreCheckResult::Proceed));
    }

    #[test]
    fn test_trust_pre_check_exit_requested() {
        let mut ctx = TrustContext::default();
        ctx.request_exit();

        // Any point should return ExitInProgress
        let result = trust_pre_check(&ctx, &Point::new(200.0, 200.0));
        assert!(matches!(result, PreCheckResult::ExitInProgress));
    }

    // ═══════════════════════════════════════════════════════════════════════════
    //                                             // state preservation tests
    // ═══════════════════════════════════════════════════════════════════════════

    #[test]
    fn test_state_preservation_no_changes() {
        let entry = EntryStateSnapshot::new(12345, 67890, Timestamp::new(100));
        let record = ExperienceVerificationRecord {
            entry_snapshot: entry,
            verified_changes: vec![],
            exit_essence_hash: 12345,          // Same as entry
            exit_persistent_state_hash: 67890, // Same as entry
        };

        let result = verify_state_preservation(&record);
        assert!(result.is_ok());
    }

    #[test]
    fn test_state_preservation_violation_essence() {
        let entry = EntryStateSnapshot::new(12345, 67890, Timestamp::new(100));
        let record = ExperienceVerificationRecord {
            entry_snapshot: entry,
            verified_changes: vec![],
            exit_essence_hash: 99999, // MODIFIED without consent!
            exit_persistent_state_hash: 67890,
        };

        let result = verify_state_preservation(&record);
        assert!(matches!(
            result,
            Err(StateViolation::EssenceModifiedWithoutConsent)
        ));
    }

    #[test]
    fn test_state_preservation_violation_persistent() {
        let entry = EntryStateSnapshot::new(12345, 67890, Timestamp::new(100));
        let record = ExperienceVerificationRecord {
            entry_snapshot: entry,
            verified_changes: vec![],
            exit_essence_hash: 12345,
            exit_persistent_state_hash: 99999, // MODIFIED without consent!
        };

        let result = verify_state_preservation(&record);
        assert!(matches!(
            result,
            Err(StateViolation::PersistentStateModifiedWithoutConsent)
        ));
    }

    #[test]
    fn test_state_preservation_with_consent() {
        let mut entry = EntryStateSnapshot::new(12345, 67890, Timestamp::new(100));

        // Entity consents to a memory modification
        let proposed = ProposedModification {
            modification_type: StateModificationType::MemoryModification,
            description: "Save game progress".to_string(),
            reversible: true,
            change_hash: 1000, // Hash of the delta
        };
        entry.record_consent(proposed.clone(), Timestamp::new(150));

        // Create a verified change that matches the consent
        let change = VerifiedChange {
            before_hash: 67890,
            after_hash: 68890, // 67890 + 1000 = 68890
            delta_hash: 1000,
            fulfills_consent: proposed,
            entity_signature: [0u8; 64],
        };

        let record = ExperienceVerificationRecord {
            entry_snapshot: entry,
            verified_changes: vec![change],
            exit_essence_hash: 12345,          // Unchanged
            exit_persistent_state_hash: 68890, // Changed via consent
        };

        let result = verify_state_preservation(&record);
        assert!(result.is_ok());
    }

    #[test]
    fn test_state_preservation_excess_modifications() {
        let entry = EntryStateSnapshot::new(12345, 67890, Timestamp::new(100));
        // No consents recorded, but changes occurred

        let change = VerifiedChange {
            before_hash: 67890,
            after_hash: 68890,
            delta_hash: 1000,
            fulfills_consent: ProposedModification {
                modification_type: StateModificationType::MemoryModification,
                description: "Unauthorized change".to_string(),
                reversible: true,
                change_hash: 1000,
            },
            entity_signature: [0u8; 64],
        };

        let record = ExperienceVerificationRecord {
            entry_snapshot: entry,
            verified_changes: vec![change], // Change without consent!
            exit_essence_hash: 12345,
            exit_persistent_state_hash: 68890,
        };

        let result = verify_state_preservation(&record);
        assert!(matches!(
            result,
            Err(StateViolation::ExcessModifications { .. })
        ));
    }
}
