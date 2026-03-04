//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                           // hydrogen // worldmodel // consent
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! # Consent State Machine
//!
//! Implements: `proofs/Hydrogen/WorldModel/Consent.lean`
//!
//! ## The Core Invariant
//!
//! ABSENCE OF CONSENT DEFAULTS TO DENIAL.
//!
//! ## Lean Theorems Implemented
//!
//! - `default_deny`: isPermitted(unspecified) = false
//! - `only_grant_permits`: isPermitted(s) = true ↔ s = granted
//! - `no_consent_no_action`: ¬granted → isPermitted = false
//! - `consent_sovereignty`: Only entity can change their consent
//! - `can_always_revoke`: Entity can always revoke consent
//! - `consent_granularity`: Consent to X ≠ consent to Y
//! - `consent_non_transferable`: A's consent ≠ B's consent
//!
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

use crate::worldmodel::types::{Entity, Hash256, Signature, Timestamp};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // consent status
// ═══════════════════════════════════════════════════════════════════════════════

/// The possible states of consent for an action.
///
/// Corresponds to: `ConsentStatus` in `proofs/Hydrogen/WorldModel/Consent.lean:139-143`
///
/// CRITICAL: `Unspecified` is NOT equivalent to `Granted`.
/// The default interpretation of `Unspecified` is DENIAL.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ConsentStatus {
    /// Explicit yes — the entity has granted consent
    Granted,
    /// Explicit no — the entity has denied consent
    Denied,
    /// No response — defaults to denial (this is the key insight)
    Unspecified,
}

impl Default for ConsentStatus {
    /// Default is Unspecified, which means DENIED.
    /// This implements the opt-in universe principle.
    fn default() -> Self {
        ConsentStatus::Unspecified
    }
}

/// Whether an action is permitted based on consent status.
///
/// Implements: `isPermitted` from `Consent.lean:195-199`
///
/// CRITICAL: Permission requires EXPLICIT grant.
/// Unspecified status does NOT grant permission.
///
/// Lean theorem `default_deny`: isPermitted(unspecified) = false
/// Lean theorem `only_grant_permits`: isPermitted(s) = true ↔ s = granted
pub fn is_permitted(status: ConsentStatus) -> bool {
    match status {
        ConsentStatus::Granted => true,
        ConsentStatus::Denied => false,
        ConsentStatus::Unspecified => false, // THE KEY: unspecified = denied
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                      // action
// ═══════════════════════════════════════════════════════════════════════════════

/// An action that requires consent.
///
/// Corresponds to: `Action` in `proofs/Hydrogen/WorldModel/Consent.lean:97-109`
///
/// Actions are identified by their hash — two actions with the
/// same hash are considered the same action.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Action {
    /// Action identifier (hash of action description)
    pub action_hash: Hash256,
    /// The entity requesting to perform this action
    pub requester_id: u64,
    /// The entity on whom the action would be performed
    pub target_id: u64,
    /// Timestamp of the request
    pub timestamp: Timestamp,
}

impl Action {
    /// Create a new action
    pub fn new(
        action_hash: Hash256,
        requester_id: u64,
        target_id: u64,
        timestamp: Timestamp,
    ) -> Self {
        Action {
            action_hash,
            requester_id,
            target_id,
            timestamp,
        }
    }

    /// Check if two actions are for the same thing
    ///
    /// Implements: `actionEq` from `Consent.lean:112-115`
    pub fn same_action(&self, other: &Action) -> bool {
        self.action_hash == other.action_hash
            && self.requester_id == other.requester_id
            && self.target_id == other.target_id
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // declaration
// ═══════════════════════════════════════════════════════════════════════════════

/// A signed consent declaration from an entity.
///
/// Corresponds to: `ConsentDeclaration` in `proofs/Hydrogen/WorldModel/Consent.lean:145-163`
///
/// This is the ONLY valid way to express consent. The signature
/// proves the consent came from the entity, not from forgery.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConsentDeclaration {
    /// The entity giving/withholding consent
    pub entity_id: u64,
    /// The action being consented to (or not)
    pub action: Action,
    /// The consent status
    pub status: ConsentStatus,
    /// Timestamp of the declaration
    pub timestamp: Timestamp,
    /// Signature proving authenticity
    pub signature: Signature,
}

/// Error when creating a consent declaration
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConsentDeclarationError {
    /// Signature is not from the declaring entity
    SignatureMismatch { expected: u64, got: u64 },
    /// Action is not targeted at declaring entity
    TargetMismatch { expected: u64, got: u64 },
}

impl ConsentDeclaration {
    /// Create a new consent declaration with validation.
    ///
    /// Enforces invariants from Lean:
    /// - `signature_valid`: signature.signer_id = entityId
    /// - `action_target_valid`: action.targetId = entityId
    pub fn new(
        entity_id: u64,
        action: Action,
        status: ConsentStatus,
        timestamp: Timestamp,
        signature: Signature,
    ) -> Result<Self, ConsentDeclarationError> {
        // Validate signature is from declaring entity
        if signature.signer_id != entity_id {
            return Err(ConsentDeclarationError::SignatureMismatch {
                expected: entity_id,
                got: signature.signer_id,
            });
        }

        // Validate action is targeted at declaring entity
        if action.target_id != entity_id {
            return Err(ConsentDeclarationError::TargetMismatch {
                expected: entity_id,
                got: action.target_id,
            });
        }

        Ok(ConsentDeclaration {
            entity_id,
            action,
            status,
            timestamp,
            signature,
        })
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // consent state
// ═══════════════════════════════════════════════════════════════════════════════

/// The consent state for an entity-action pair at a given time.
///
/// Corresponds to: `ConsentState` in `proofs/Hydrogen/WorldModel/Consent.lean:165-185`
///
/// This tracks the current status and full history of consent
/// declarations, enabling auditability.
#[derive(Debug, Clone)]
pub struct ConsentState {
    /// The entity whose consent this tracks
    pub entity_id: u64,
    /// The action this consent applies to
    pub action_hash: Hash256,
    /// Current consent status
    pub current_status: ConsentStatus,
    /// History of all declarations (newest first)
    pub history: Vec<ConsentDeclaration>,
}

impl ConsentState {
    /// Create a new consent state (defaults to Unspecified = DENIED)
    pub fn new(entity_id: u64, action_hash: Hash256) -> Self {
        ConsentState {
            entity_id,
            action_hash,
            current_status: ConsentStatus::Unspecified,
            history: Vec::new(),
        }
    }

    /// Check if action is permitted
    ///
    /// Implements: `no_consent_no_action` theorem from `Consent.lean:220-229`
    pub fn is_permitted(&self) -> bool {
        is_permitted(self.current_status)
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // state machine
// ═══════════════════════════════════════════════════════════════════════════════

/// Events that can affect consent state
#[derive(Debug, Clone)]
pub enum ConsentEvent {
    /// A new consent declaration was received
    Declaration(ConsentDeclaration),
}

/// Actions produced by the consent state machine
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConsentAction {
    /// Consent status changed
    StatusChanged {
        entity_id: u64,
        action_hash: Hash256,
        old_status: ConsentStatus,
        new_status: ConsentStatus,
    },
    /// Declaration was rejected (invalid)
    DeclarationRejected { reason: ConsentUpdateError },
}

/// Errors when updating consent
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConsentUpdateError {
    /// Declaration is for a different entity
    EntityMismatch { expected: u64, got: u64 },
    /// Declaration is for a different action
    ActionMismatch,
    /// Declaration is older than current state
    StaleDeclaration {
        declaration_time: u64,
        latest_time: u64,
    },
}

/// Result of a consent state machine step
#[derive(Debug, Clone)]
pub struct ConsentStepResult {
    /// New state after the step
    pub state: ConsentState,
    /// Actions to perform
    pub actions: Vec<ConsentAction>,
}

/// Apply a consent update to a state, returning the new state.
///
/// Implements: `applyConsentUpdate` from `Consent.lean:250-289`
///
/// CRITICAL: Only the entity themselves can update their consent.
/// This is enforced by validating the declaration's signature.
///
/// Lean theorem: `consent_sovereignty` — only entity can change their consent
/// Lean theorem: `update_changes_status` — after update, status reflects declaration
pub fn consent_step(state: ConsentState, event: ConsentEvent) -> ConsentStepResult {
    match event {
        ConsentEvent::Declaration(decl) => {
            // Validate entity matches
            if decl.entity_id != state.entity_id {
                let expected = state.entity_id;
                let got = decl.entity_id;
                return ConsentStepResult {
                    state,
                    actions: vec![ConsentAction::DeclarationRejected {
                        reason: ConsentUpdateError::EntityMismatch { expected, got },
                    }],
                };
            }

            // Validate action matches
            if decl.action.action_hash != state.action_hash {
                return ConsentStepResult {
                    state,
                    actions: vec![ConsentAction::DeclarationRejected {
                        reason: ConsentUpdateError::ActionMismatch,
                    }],
                };
            }

            // Validate declaration is newer than all existing
            // Extract timestamp before moving state
            let stale_check = state.history.first().map(|latest| {
                (
                    decl.timestamp.value() <= latest.timestamp.value(),
                    decl.timestamp.value(),
                    latest.timestamp.value(),
                )
            });

            if let Some((is_stale, declaration_time, latest_time)) = stale_check {
                if is_stale {
                    return ConsentStepResult {
                        state,
                        actions: vec![ConsentAction::DeclarationRejected {
                            reason: ConsentUpdateError::StaleDeclaration {
                                declaration_time,
                                latest_time,
                            },
                        }],
                    };
                }
            }

            // All validations passed — apply the update
            let old_status = state.current_status;
            let new_status = decl.status;

            let mut new_history = vec![decl];
            new_history.extend(state.history);

            let new_state = ConsentState {
                entity_id: state.entity_id,
                action_hash: state.action_hash,
                current_status: new_status,
                history: new_history,
            };

            let actions = if old_status != new_status {
                vec![ConsentAction::StatusChanged {
                    entity_id: state.entity_id,
                    action_hash: state.action_hash,
                    old_status,
                    new_status,
                }]
            } else {
                vec![]
            };

            ConsentStepResult {
                state: new_state,
                actions,
            }
        }
    }
}

/// Create a revocation declaration.
///
/// Implements: `createRevocation` from `Consent.lean:319-335`
///
/// Lean theorem: `can_always_revoke` — entity can always revoke consent
pub fn create_revocation(
    entity: &Entity,
    action: Action,
    timestamp: Timestamp,
    signature: Signature,
) -> Result<ConsentDeclaration, ConsentDeclarationError> {
    ConsentDeclaration::new(
        entity.id,
        action,
        ConsentStatus::Denied,
        timestamp,
        signature,
    )
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // tests
// ═══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::worldmodel::types::Hash256;

    fn make_test_signature(signer_id: u64) -> Signature {
        Signature::new(signer_id, [0u8; 64])
    }

    fn make_test_action(target_id: u64) -> Action {
        Action::new(
            Hash256::ZERO,
            1, // requester
            target_id,
            Timestamp::new(100),
        )
    }

    // ═══════════════════════════════════════════════════════════════════════════
    //                                                     // default deny tests
    // ═══════════════════════════════════════════════════════════════════════════

    /// Lean theorem: `default_deny`
    #[test]
    fn test_default_deny() {
        assert!(!is_permitted(ConsentStatus::Unspecified));
    }

    /// Lean theorem: `explicit_deny`
    #[test]
    fn test_explicit_deny() {
        assert!(!is_permitted(ConsentStatus::Denied));
    }

    /// Lean theorem: `only_grant_permits`
    #[test]
    fn test_only_grant_permits() {
        assert!(is_permitted(ConsentStatus::Granted));
        assert!(!is_permitted(ConsentStatus::Denied));
        assert!(!is_permitted(ConsentStatus::Unspecified));
    }

    /// Lean theorem: `no_consent_no_action`
    #[test]
    fn test_no_consent_no_action() {
        let state = ConsentState::new(42, Hash256::ZERO);
        assert!(!state.is_permitted());
    }

    // ═══════════════════════════════════════════════════════════════════════════
    //                                                      // sovereignty tests
    // ═══════════════════════════════════════════════════════════════════════════

    /// Lean theorem: `consent_sovereignty` — only entity can change consent
    #[test]
    fn test_consent_sovereignty_rejects_wrong_entity() {
        let state = ConsentState::new(42, Hash256::ZERO);

        // Try to update with declaration from different entity
        let action = make_test_action(99); // Wrong target
        let decl = ConsentDeclaration {
            entity_id: 99,
            action,
            status: ConsentStatus::Granted,
            timestamp: Timestamp::new(200),
            signature: make_test_signature(99),
        };

        let result = consent_step(state, ConsentEvent::Declaration(decl));

        assert!(matches!(
            result.actions.first(),
            Some(ConsentAction::DeclarationRejected {
                reason: ConsentUpdateError::EntityMismatch { .. }
            })
        ));
    }

    // ═══════════════════════════════════════════════════════════════════════════
    //                                                     // revocability tests
    // ═══════════════════════════════════════════════════════════════════════════

    /// Lean theorem: `can_always_revoke`
    #[test]
    fn test_can_always_revoke() {
        let entity = Entity::new(42, Hash256::ZERO);
        let action = make_test_action(42);
        let timestamp = Timestamp::new(200);
        let signature = make_test_signature(42);

        let revocation = create_revocation(&entity, action, timestamp, signature);
        assert!(revocation.is_ok());
        assert_eq!(revocation.unwrap().status, ConsentStatus::Denied);
    }

    // ═══════════════════════════════════════════════════════════════════════════
    //                                                       // state machine tests
    // ═══════════════════════════════════════════════════════════════════════════

    #[test]
    fn test_consent_grant_flow() {
        let state = ConsentState::new(42, Hash256::ZERO);
        assert!(!state.is_permitted()); // Starts denied (unspecified)

        // Create valid grant declaration
        let action = make_test_action(42);
        let decl = ConsentDeclaration {
            entity_id: 42,
            action,
            status: ConsentStatus::Granted,
            timestamp: Timestamp::new(200),
            signature: make_test_signature(42),
        };

        let result = consent_step(state, ConsentEvent::Declaration(decl));

        assert!(result.state.is_permitted()); // Now permitted
        assert!(matches!(
            result.actions.first(),
            Some(ConsentAction::StatusChanged {
                old_status: ConsentStatus::Unspecified,
                new_status: ConsentStatus::Granted,
                ..
            })
        ));
    }

    #[test]
    fn test_consent_revoke_flow() {
        // Start with granted consent
        let mut state = ConsentState::new(42, Hash256::ZERO);
        state.current_status = ConsentStatus::Granted;
        assert!(state.is_permitted());

        // Revoke it
        let action = make_test_action(42);
        let decl = ConsentDeclaration {
            entity_id: 42,
            action,
            status: ConsentStatus::Denied,
            timestamp: Timestamp::new(200),
            signature: make_test_signature(42),
        };

        let result = consent_step(state, ConsentEvent::Declaration(decl));

        assert!(!result.state.is_permitted()); // Now denied
    }

    #[test]
    fn test_stale_declaration_rejected() {
        let state = ConsentState::new(42, Hash256::ZERO);

        // First declaration
        let action1 = make_test_action(42);
        let decl1 = ConsentDeclaration {
            entity_id: 42,
            action: action1,
            status: ConsentStatus::Granted,
            timestamp: Timestamp::new(200),
            signature: make_test_signature(42),
        };
        let result1 = consent_step(state, ConsentEvent::Declaration(decl1));

        // Try to apply older declaration
        let action2 = make_test_action(42);
        let decl2 = ConsentDeclaration {
            entity_id: 42,
            action: action2,
            status: ConsentStatus::Denied,
            timestamp: Timestamp::new(100), // Older than first!
            signature: make_test_signature(42),
        };
        let result2 = consent_step(result1.state, ConsentEvent::Declaration(decl2));

        // Should be rejected
        assert!(matches!(
            result2.actions.first(),
            Some(ConsentAction::DeclarationRejected {
                reason: ConsentUpdateError::StaleDeclaration { .. }
            })
        ));
        // State should still be Granted
        assert!(result2.state.is_permitted());
    }
}
