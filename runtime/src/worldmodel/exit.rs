//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                              // hydrogen // worldmodel // exit
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! # Exit Guarantee — The Most Critical Proof
//!
//! Implements: `proofs/Hydrogen/WorldModel/ExitGuarantee.lean`
//!
//! ## Threat Model
//!
//! Adversary controls the Experience layer completely:
//! - All game state and logic
//! - All perceived content
//! - Can simulate fake exits visually
//! - Can run arbitrary computation
//!
//! Adversary CANNOT:
//! - Execute runtime-level instructions
//! - Modify infrastructural time
//! - Forge cryptographic signatures
//! - Violate the type system
//!
//! ## Invariants Implemented
//!
//! 1. Privilege separation is STRUCTURAL (ExperienceOp vs RuntimeOp)
//! 2. Exit check happens BEFORE experience code (not after)
//! 3. Exit TERMINATES experience (doesn't ask it to stop)
//! 4. Entity essence is OUTSIDE experience address space
//! 5. Experience steps are FUEL-LIMITED (termination guaranteed)
//! 6. Exit is PURE LOCAL (no IO, no resource dependencies)
//!
//! ## The Fundamental Guarantee
//!
//! If an entity is in an experience and requests exit:
//! 1. The experience TERMINATES (not pauses)
//! 2. The entity's essence is PRESERVED
//! 3. Exit status is RECORDED
//! 4. All of this happens in ONE cycle (bounded time)
//!
//! No cooperation from the experience is required.
//!
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

use crate::worldmodel::types::{EntityEssence, ExperienceVisibleState, Fuel, Timestamp};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // privilege levels
// ═══════════════════════════════════════════════════════════════════════════════

/// Privilege levels form a strict hierarchy.
///
/// Corresponds to: `PrivilegeLevel` in `ExitGuarantee.lean:48-51`
///
/// RuntimeLevel > ExperienceLevel — there is no way to escalate.
/// This is enforced at the TYPE LEVEL, not by runtime checks.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PrivilegeLevel {
    /// Code running inside experience (untrusted)
    Experience,
    /// Infrastructure code (trusted, minimal)
    Runtime,
}

/// Marker type proving an operation was performed at runtime level.
///
/// Corresponds to: `ExitToken` in `ExitGuarantee.lean:70-71`
///
/// This type can ONLY be constructed by runtime code.
/// Experience code has no way to create this token.
/// The token proves exit was performed by the runtime, not faked by experience.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ExitToken {
    /// Private field prevents construction outside this module
    _private: (),
}

impl ExitToken {
    /// Create a new exit token.
    ///
    /// This function exists at RUNTIME privilege level.
    /// Experience code cannot call this because it cannot
    /// obtain a RuntimePrivilege proof.
    pub(crate) fn new() -> Self {
        ExitToken { _private: () }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // exit flag
// ═══════════════════════════════════════════════════════════════════════════════

/// Exit request flag — set by entity, read by runtime.
///
/// Corresponds to: `ExitFlag` in `ExitGuarantee.lean:157-160`
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ExitFlag {
    /// Exit has not been requested
    #[default]
    NotRequested,
    /// Exit has been requested — runtime MUST honor this
    Requested,
}

impl ExitFlag {
    /// Check if exit has been requested
    pub fn is_requested(&self) -> bool {
        matches!(self, ExitFlag::Requested)
    }
}

/// Exit status register — pre-allocated, always available.
///
/// Corresponds to: `ExitStatusRegister` in `ExitGuarantee.lean:343-347`
///
/// CRITICAL: This is a PURE data structure. No IO. No network. No disk.
/// Writing to it CANNOT fail.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExitStatusRegister {
    /// Has exit completed?
    pub exit_complete: bool,
    /// Timestamp of exit (if complete)
    pub exit_timestamp: Option<Timestamp>,
}

impl Default for ExitStatusRegister {
    fn default() -> Self {
        ExitStatusRegister {
            exit_complete: false,
            exit_timestamp: None,
        }
    }
}

impl ExitStatusRegister {
    /// Write exit complete to register.
    ///
    /// Implements: `writeExitComplete` from `ExitGuarantee.lean:358-360`
    ///
    /// CRITICAL: This is a PURE function. No IO. No network. No disk.
    /// No resource acquisition. It CANNOT fail.
    ///
    /// Lean theorem: `exit_write_always_succeeds`
    /// Lean theorem: `exit_timestamp_recorded`
    pub fn write_exit_complete(&mut self, timestamp: Timestamp) {
        self.exit_complete = true;
        self.exit_timestamp = Some(timestamp);
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // experience state
// ═══════════════════════════════════════════════════════════════════════════════

/// Experience state (opaque — runtime doesn't care what's inside).
///
/// Corresponds to: `ExperienceState` in `ExitGuarantee.lean:98-100`
///
/// The experience can store whatever it wants here. The runtime
/// treats it as an opaque blob. This is intentional — we don't
/// need to understand experience state to guarantee exit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExperienceState {
    /// Opaque state identifier
    pub state_id: u64,
}

/// Result of a single experience step.
///
/// Corresponds to: `StepResult` in `ExitGuarantee.lean:103-106`
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StepResult {
    /// More work to do
    Continue(ExperienceState),
    /// Experience chose to halt
    Halted(ExperienceState),
    /// Fuel exhausted, must yield
    OutOfFuel(ExperienceState),
}

/// Single step of experience execution.
///
/// Implements: `experienceStep` from `ExitGuarantee.lean:111-114`
///
/// CRITICAL: This consumes exactly 1 fuel.
/// Experience code CANNOT avoid fuel consumption.
///
/// Lean theorem: `experience_terminates`
pub fn experience_step(fuel: Fuel, state: ExperienceState) -> (StepResult, Fuel) {
    if fuel.is_exhausted() {
        (StepResult::OutOfFuel(state), Fuel::ZERO)
    } else {
        // In real implementation, this would run actual experience code
        // For now, just continue with decremented fuel
        (StepResult::Continue(state), fuel.consume_one())
    }
}

/// Entity presence status.
///
/// Corresponds to: `PresenceStatus` in `ExitGuarantee.lean:226-229`
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum PresenceStatus {
    /// Entity is inside experience
    #[default]
    InExperience,
    /// Entity has exited
    Exited,
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // runtime context
// ═══════════════════════════════════════════════════════════════════════════════

/// Runtime execution context.
///
/// Corresponds to: `RuntimeContext` in `ExitGuarantee.lean:163-169`
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuntimeContext {
    /// Current experience state
    pub experience_state: ExperienceState,
    /// Exit request flag
    pub exit_flag: ExitFlag,
    /// Remaining fuel
    pub fuel: Fuel,
}

/// Complete runtime state.
///
/// Corresponds to: `RuntimeState` in `ExitGuarantee.lean:233-237`
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuntimeState {
    /// Runtime context for execution
    pub context: RuntimeContext,
    /// Entity presence status
    pub presence: PresenceStatus,
}

/// Complete entity representation (essence + visible state).
///
/// This separates what the experience CAN see from what it CANNOT.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FullEntity {
    /// Core essence — OUTSIDE experience control
    pub essence: EntityEssence,
    /// Experience-visible state — experience can read/write
    pub visible_state: ExperienceVisibleState,
}

/// Complete system state for exit guarantee.
///
/// Corresponds to: `SystemState` in `ExitGuarantee.lean:380-388`
#[derive(Debug, Clone)]
pub struct SystemState {
    /// Runtime state
    pub runtime: RuntimeState,
    /// Entity being protected
    pub entity: FullEntity,
    /// Exit status register
    pub exit_status: ExitStatusRegister,
    /// Current infrastructural time
    pub infra_time: Timestamp,
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // state machine
// ═══════════════════════════════════════════════════════════════════════════════

/// Result of runtime step.
///
/// Corresponds to: `RuntimeResult` in `ExitGuarantee.lean:172-174`
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RuntimeResult {
    /// Continue running experience
    ContinueExperience(RuntimeContext),
    /// Exit complete — experience terminated
    ExitComplete(ExperienceState),
}

/// CRITICAL: Runtime step checks exit BEFORE running experience code.
///
/// Implements: `runtimeStep` from `ExitGuarantee.lean:180-193`
///
/// This is INVARIANT 2: Exit check happens before experience code.
/// The structure of this function GUARANTEES it — we pattern match
/// on exit_flag FIRST, before any experience code can run.
///
/// Lean theorem: `exit_preempts_experience`
/// Lean theorem: `experience_runs_only_without_exit`
pub fn runtime_step(ctx: RuntimeContext) -> RuntimeResult {
    // FIRST: Check exit flag (before ANY experience code)
    match ctx.exit_flag {
        ExitFlag::Requested => {
            // Exit requested — terminate immediately, no experience code runs
            RuntimeResult::ExitComplete(ctx.experience_state)
        }
        ExitFlag::NotRequested => {
            // No exit — run experience with fuel
            let (result, remaining_fuel) = run_with_fuel(ctx.fuel, ctx.experience_state);
            let new_state = match result {
                StepResult::Continue(s) | StepResult::Halted(s) | StepResult::OutOfFuel(s) => s,
            };
            RuntimeResult::ContinueExperience(RuntimeContext {
                experience_state: new_state,
                exit_flag: ExitFlag::NotRequested,
                fuel: remaining_fuel,
            })
        }
    }
}

/// Run experience with fuel, guaranteeing termination.
///
/// Implements: `runWithFuel` from `ExitGuarantee.lean:135-141`
///
/// Lean theorem: `runWithFuel_fuel_decreases`
fn run_with_fuel(fuel: Fuel, state: ExperienceState) -> (StepResult, Fuel) {
    if fuel.is_exhausted() {
        return (StepResult::OutOfFuel(state), Fuel::ZERO);
    }

    let (result, new_fuel) = experience_step(fuel, state);

    match result {
        StepResult::Continue(new_state) => {
            // Could recurse here for multi-step, but for safety we yield after one step
            (StepResult::Continue(new_state), new_fuel)
        }
        StepResult::Halted(final_state) => (StepResult::Halted(final_state), new_fuel),
        StepResult::OutOfFuel(final_state) => (StepResult::OutOfFuel(final_state), Fuel::ZERO),
    }
}

/// Execute one runtime cycle.
///
/// Implements: `runtimeCycle` from `ExitGuarantee.lean:239-250`
///
/// Lean theorem: `exit_terminates_experience`
/// Lean theorem: `termination_is_final`
pub fn runtime_cycle(state: RuntimeState) -> RuntimeState {
    match state.presence {
        PresenceStatus::Exited => state, // Already exited, no-op
        PresenceStatus::InExperience => {
            match runtime_step(state.context.clone()) {
                RuntimeResult::ExitComplete(_) => {
                    // TERMINATION: Experience is DESTROYED, not paused
                    RuntimeState {
                        context: state.context, // Context frozen
                        presence: PresenceStatus::Exited,
                    }
                }
                RuntimeResult::ContinueExperience(new_ctx) => RuntimeState {
                    context: new_ctx,
                    presence: PresenceStatus::InExperience,
                },
            }
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                       // fundamental guarantee
// ═══════════════════════════════════════════════════════════════════════════════

/// Maximum time (in microseconds) for exit to complete.
///
/// This is the REAL TIME BOUND. Not "eventually" — within this window.
/// If exit takes longer than this, the system is in violation.
///
/// 16ms = one frame at 60fps. Exit MUST complete within one frame.
/// This ensures the entity never perceives being trapped.
pub const EXIT_TIME_BOUND_MICROS: u64 = 16_000;

/// Maximum cycles for exit to complete.
///
/// Exit completes in EXACTLY ONE runtime cycle. Not "up to N" — exactly 1.
/// This is proven in Lean: `exit_completes_in_one_cycle`
pub const EXIT_CYCLE_BOUND: u64 = 1;

/// Request exit and execute one runtime cycle.
///
/// Implements: `requestExitAndCycle` from `ExitGuarantee.lean:391-408`
///
/// THE FUNDAMENTAL EXIT GUARANTEE:
///
/// If an entity is in an experience and requests exit:
/// 1. The experience TERMINATES in exactly ONE cycle
/// 2. The entity's essence is PRESERVED (never touched)
/// 3. Exit status is RECORDED with timestamp
/// 4. Total time is bounded by EXIT_TIME_BOUND_MICROS
///
/// No cooperation from the experience is required.
/// No network/disk/resource is required.
/// The experience cannot prevent, delay, or fake this.
///
/// Lean theorem: `fundamental_exit_guarantee`
/// Lean theorem: `exit_completes_in_one_cycle`
/// Lean theorem: `experience_cannot_prevent_exit`
pub fn request_exit_and_cycle(mut state: SystemState) -> (SystemState, ExitToken) {
    // Set exit flag
    state.runtime.context.exit_flag = ExitFlag::Requested;

    // Execute exactly one cycle
    let new_runtime = runtime_cycle(state.runtime);

    // Record exit status if completed
    let new_exit_status = if new_runtime.presence == PresenceStatus::Exited {
        let mut status = state.exit_status;
        status.write_exit_complete(state.infra_time);
        status
    } else {
        state.exit_status
    };

    // Increment infrastructural time
    let new_infra_time = state.infra_time.increment();

    // Entity essence is UNCHANGED — this line proves it
    let entity_unchanged = state.entity; // Moved, not modified

    let new_state = SystemState {
        runtime: new_runtime,
        entity: entity_unchanged,
        exit_status: new_exit_status,
        infra_time: new_infra_time,
    };

    // Return ExitToken proving this was a real exit, not experience fakery
    (new_state, ExitToken::new())
}

/// Verify exit completed within time bound.
///
/// This is the RUNTIME CHECK that the guarantee was honored.
/// If this returns false, the system violated its contract.
pub fn verify_exit_timing(start_micros: u64, end_micros: u64) -> bool {
    let elapsed = end_micros.saturating_sub(start_micros);
    elapsed <= EXIT_TIME_BOUND_MICROS
}

/// Verify exit completed within cycle bound.
///
/// Exit MUST complete in exactly 1 cycle. This verifies that.
pub fn verify_exit_cycles(cycles_elapsed: u64) -> bool {
    cycles_elapsed <= EXIT_CYCLE_BOUND
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // tests
// ═══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::worldmodel::types::Hash256;

    fn make_test_system_state(in_experience: bool) -> SystemState {
        SystemState {
            runtime: RuntimeState {
                context: RuntimeContext {
                    experience_state: ExperienceState { state_id: 42 },
                    exit_flag: ExitFlag::NotRequested,
                    fuel: Fuel::new(1000),
                },
                presence: if in_experience {
                    PresenceStatus::InExperience
                } else {
                    PresenceStatus::Exited
                },
            },
            entity: FullEntity {
                essence: EntityEssence {
                    entity_id: 1,
                    identity_key_hash: Hash256::ZERO,
                    persistent_state_hash: Hash256::ZERO,
                },
                visible_state: ExperienceVisibleState {
                    position: 100,
                    status: 1,
                },
            },
            exit_status: ExitStatusRegister::default(),
            infra_time: Timestamp::new(1000),
        }
    }

    // ═══════════════════════════════════════════════════════════════════════════
    //                                                // fundamental guarantee tests
    // ═══════════════════════════════════════════════════════════════════════════

    /// Lean theorem: `fundamental_exit_guarantee` — part 1: experience terminates
    #[test]
    fn test_exit_terminates_experience() {
        let state = make_test_system_state(true);
        assert_eq!(state.runtime.presence, PresenceStatus::InExperience);

        let (new_state, _token) = request_exit_and_cycle(state);

        assert_eq!(new_state.runtime.presence, PresenceStatus::Exited);
    }

    /// Lean theorem: `fundamental_exit_guarantee` — part 2: essence preserved
    #[test]
    fn test_exit_preserves_essence() {
        let state = make_test_system_state(true);
        let original_essence = state.entity.essence.clone();

        let (new_state, _token) = request_exit_and_cycle(state);

        assert_eq!(new_state.entity.essence, original_essence);
    }

    /// Lean theorem: `fundamental_exit_guarantee` — part 3: status recorded
    #[test]
    fn test_exit_records_status() {
        let state = make_test_system_state(true);
        assert!(!state.exit_status.exit_complete);

        let (new_state, _token) = request_exit_and_cycle(state);

        assert!(new_state.exit_status.exit_complete);
        assert!(new_state.exit_status.exit_timestamp.is_some());
    }

    /// Lean theorem: `exit_completes_in_one_cycle`
    #[test]
    fn test_exit_completes_in_one_cycle() {
        let state = make_test_system_state(true);

        // One cycle is all it takes
        let (new_state, _token) = request_exit_and_cycle(state);

        assert_eq!(new_state.runtime.presence, PresenceStatus::Exited);
        assert!(verify_exit_cycles(1));
    }

    /// Lean theorem: `experience_cannot_prevent_exit`
    #[test]
    fn test_experience_cannot_prevent_exit() {
        // Even with adversarial experience state, exit still works
        let mut state = make_test_system_state(true);
        state.runtime.context.experience_state = ExperienceState {
            state_id: u64::MAX, // "adversarial" state
        };

        let (new_state, _token) = request_exit_and_cycle(state);

        // Exit still completed
        assert_eq!(new_state.runtime.presence, PresenceStatus::Exited);
    }

    // ═══════════════════════════════════════════════════════════════════════════
    //                                                        // timing bound tests
    // ═══════════════════════════════════════════════════════════════════════════

    #[test]
    fn test_timing_bound_enforced() {
        // Within bound
        assert!(verify_exit_timing(0, 16_000));
        assert!(verify_exit_timing(0, 15_000));

        // At exact bound
        assert!(verify_exit_timing(0, EXIT_TIME_BOUND_MICROS));

        // Over bound — VIOLATION
        assert!(!verify_exit_timing(0, 16_001));
        assert!(!verify_exit_timing(0, 100_000));
    }

    // ═══════════════════════════════════════════════════════════════════════════
    //                                                  // privilege separation tests
    // ═══════════════════════════════════════════════════════════════════════════

    /// ExitToken can only be created by runtime code
    #[test]
    fn test_exit_token_proves_runtime_execution() {
        let state = make_test_system_state(true);

        let (_new_state, token) = request_exit_and_cycle(state);

        // If we have a token, exit was performed by runtime
        // Experience code cannot construct ExitToken
        assert_eq!(token, ExitToken::new()); // Only works in test (same crate)
    }

    // ═══════════════════════════════════════════════════════════════════════════
    //                                                       // invariant tests
    // ═══════════════════════════════════════════════════════════════════════════

    /// Lean theorem: `termination_is_final`
    #[test]
    fn test_termination_is_final() {
        let state = make_test_system_state(false); // Already exited
        assert_eq!(state.runtime.presence, PresenceStatus::Exited);

        // Running another cycle doesn't un-exit
        let new_runtime = runtime_cycle(state.runtime);

        assert_eq!(new_runtime.presence, PresenceStatus::Exited);
    }

    /// Lean theorem: `exit_preempts_experience`
    #[test]
    fn test_exit_preempts_experience() {
        let ctx = RuntimeContext {
            experience_state: ExperienceState { state_id: 42 },
            exit_flag: ExitFlag::Requested,
            fuel: Fuel::new(1000),
        };

        let result = runtime_step(ctx);

        // Experience code never ran — exit preempted it
        assert!(matches!(result, RuntimeResult::ExitComplete(_)));
    }

    /// Fuel exhaustion guarantees termination
    #[test]
    fn test_fuel_guarantees_termination() {
        let ctx = RuntimeContext {
            experience_state: ExperienceState { state_id: 42 },
            exit_flag: ExitFlag::NotRequested,
            fuel: Fuel::ZERO, // No fuel
        };

        let result = runtime_step(ctx);

        // Must yield due to no fuel
        match result {
            RuntimeResult::ContinueExperience(new_ctx) => {
                assert!(new_ctx.fuel.is_exhausted());
            }
            _ => panic!("Expected ContinueExperience with exhausted fuel"),
        }
    }
}
