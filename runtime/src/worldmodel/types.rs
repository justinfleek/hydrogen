//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                             // hydrogen // worldmodel // types
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! # Shared Types for WorldModel
//!
//! These types correspond directly to Lean4 structures in:
//! - `proofs/Hydrogen/WorldModel/Integrity.lean`
//! - `proofs/Hydrogen/WorldModel/Consent.lean`
//! - `proofs/Hydrogen/WorldModel/Grounding.lean`
//!
//! ## Correspondence Convention
//!
//! Every type includes a doc comment with:
//! - The exact Lean4 structure it corresponds to
//! - The file path where the Lean proof lives
//! - Any invariants that Lean proves about this type
//!
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // cryptographic ids
// ═══════════════════════════════════════════════════════════════════════════════

/// A 256-bit hash used for integrity verification.
///
/// Corresponds to: `Hash256` in `proofs/Hydrogen/WorldModel/Integrity.lean`
///
/// Invariants (from Lean):
/// - `hashEq_refl`: Hash equality is reflexive
/// - `hashEq_symm`: Hash equality is symmetric
/// - `hashEq_trans`: Hash equality is transitive
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Hash256 {
    pub words: [u64; 4],
}

impl Hash256 {
    /// Create a new hash from 32 bytes
    pub fn from_bytes(bytes: [u8; 32]) -> Self {
        let mut words = [0u64; 4];
        for (i, chunk) in bytes.chunks_exact(8).enumerate() {
            words[i] = u64::from_le_bytes(chunk.try_into().unwrap_or([0; 8]));
        }
        Hash256 { words }
    }

    /// Zero hash (used as placeholder, NOT for security)
    pub const ZERO: Hash256 = Hash256 {
        words: [0, 0, 0, 0],
    };
}

/// A cryptographic signature proving authenticity.
///
/// Corresponds to: `Signature` in `proofs/Hydrogen/WorldModel/Integrity.lean`
///
/// The `signer_id` field proves WHO signed this, enabling verification
/// that consent declarations come from the correct entity.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Signature {
    /// The entity ID who produced this signature
    pub signer_id: u64,
    /// The actual signature bytes (e.g., Ed25519)
    pub signature_bytes: [u8; 64],
}

impl Signature {
    /// Create a new signature
    pub fn new(signer_id: u64, signature_bytes: [u8; 64]) -> Self {
        Signature {
            signer_id,
            signature_bytes,
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // entities
// ═══════════════════════════════════════════════════════════════════════════════

/// An entity capable of giving or withholding consent.
///
/// Corresponds to: `Entity` in `proofs/Hydrogen/WorldModel/Consent.lean`
///
/// This is abstract — could be an AI agent, a human with BMI,
/// a collective, or any other rights-bearing entity.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Entity {
    /// Unique entity identifier
    pub id: u64,
    /// Public key hash for signature verification
    pub public_key_hash: Hash256,
}

impl Entity {
    /// Create a new entity
    pub fn new(id: u64, public_key_hash: Hash256) -> Self {
        Entity {
            id,
            public_key_hash,
        }
    }
}

/// Entity essence — the core identity that MUST be preserved.
///
/// Corresponds to: `EntityEssence` in `proofs/Hydrogen/WorldModel/ExitGuarantee.lean`
///
/// CRITICAL: This is stored OUTSIDE the experience address space.
/// Experience code CANNOT access or modify essence.
///
/// Invariants (from Lean):
/// - `essence_preserved`: Entity essence is preserved through ANY experience
/// - `adversarial_experience_cannot_modify_essence`: Even adversarial
///   experiences cannot modify essence
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EntityEssence {
    /// Unique entity identifier
    pub entity_id: u64,
    /// Cryptographic identity key (hash of public key)
    pub identity_key_hash: Hash256,
    /// Memories/state accumulated across experiences (hash of state)
    pub persistent_state_hash: Hash256,
}

/// Experience-visible entity state (can be manipulated by experience).
///
/// Corresponds to: `ExperienceVisibleState` in `proofs/Hydrogen/WorldModel/ExitGuarantee.lean`
///
/// This is the ONLY part of an entity that experience code can see or modify.
/// The essence is never exposed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExperienceVisibleState {
    /// Position within experience (opaque to essence)
    pub position: u64,
    /// Health/status within experience (opaque to essence)
    pub status: u64,
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // bounded values
// ═══════════════════════════════════════════════════════════════════════════════

/// A value bounded to [0.0, 1.0].
///
/// Corresponds to: `BoundedUnit` in `proofs/Hydrogen/WorldModel/Grounding.lean`
///
/// Invariants (from Lean):
/// - `lower_bound`: 0 ≤ value
/// - `upper_bound`: value ≤ 1
///
/// Used for coercion intensity, confidence scores, etc.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct BoundedUnit {
    value: f64,
}

impl BoundedUnit {
    /// Create a new bounded value, clamping to [0.0, 1.0].
    ///
    /// # NaN/Infinity Handling
    ///
    /// NaN and infinite values are **security vulnerabilities** in the grounding
    /// layer. If NaN propagates through coercion detection, the comparison
    /// `score > 0.6` returns false, and duress is never detected.
    ///
    /// This function treats invalid floats as **fail-safe to zero**:
    /// - NaN → 0.0 (absence of signal, not presence of safety)
    /// - Infinity → clamped normally (INFINITY → 1.0, NEG_INFINITY → 0.0)
    ///
    /// Corresponds to: `BoundedUnit` in `proofs/Hydrogen/WorldModel/Sensation.lean`
    ///
    /// Invariants (from Lean):
    /// - `lower_bound`: 0 ≤ value
    /// - `upper_bound`: value ≤ 1
    /// - Result is NEVER NaN
    pub fn new(value: f64) -> Self {
        // NaN check MUST come before clamp — f64::clamp(NaN, _, _) returns NaN
        let safe_value = if value.is_nan() { 0.0 } else { value };
        BoundedUnit {
            value: safe_value.clamp(0.0, 1.0),
        }
    }

    /// Get the inner value (guaranteed in [0.0, 1.0])
    pub fn value(&self) -> f64 {
        self.value
    }

    /// Zero (complete freedom / no intensity)
    pub const ZERO: BoundedUnit = BoundedUnit { value: 0.0 };

    /// One (total coercion / maximum intensity)
    pub const ONE: BoundedUnit = BoundedUnit { value: 1.0 };

    /// Coercion threshold (0.6) — severity at which consent is invalidated
    pub const COERCION_THRESHOLD: BoundedUnit = BoundedUnit { value: 0.6 };
}

impl Default for BoundedUnit {
    fn default() -> Self {
        BoundedUnit::ZERO
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // timestamps
// ═══════════════════════════════════════════════════════════════════════════════

/// Infrastructural timestamp — monotonically increasing, unforgeable.
///
/// This is NOT wall-clock time. It's a logical clock maintained by the
/// runtime, outside the control of any experience.
///
/// Corresponds to: timestamp fields (ℕ) throughout WorldModel proofs
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Timestamp(pub u64);

impl Timestamp {
    /// Create a new timestamp
    pub fn new(value: u64) -> Self {
        Timestamp(value)
    }

    /// Increment timestamp by one
    pub fn increment(&self) -> Self {
        Timestamp(self.0.saturating_add(1))
    }

    /// Get the inner value
    pub fn value(&self) -> u64 {
        self.0
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                        // fuel
// ═══════════════════════════════════════════════════════════════════════════════

/// Fuel for experience execution — prevents infinite loops.
///
/// Corresponds to: `Fuel` in `proofs/Hydrogen/WorldModel/ExitGuarantee.lean`
///
/// When fuel hits zero, experience MUST yield to runtime. This guarantees
/// termination of any experience step, regardless of what code it runs.
///
/// Invariants (from Lean):
/// - `experience_terminates`: Experience execution always terminates
/// - `runWithFuel_fuel_decreases`: Fuel always decreases or stays same
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Fuel(pub u64);

impl Fuel {
    /// Maximum fuel per execution slice
    pub const MAX_PER_SLICE: Fuel = Fuel(1_000_000);

    /// No fuel remaining
    pub const ZERO: Fuel = Fuel(0);

    /// Create new fuel amount
    pub fn new(amount: u64) -> Self {
        Fuel(amount)
    }

    /// Consume one unit of fuel
    pub fn consume_one(&self) -> Self {
        Fuel(self.0.saturating_sub(1))
    }

    /// Check if fuel is exhausted
    pub fn is_exhausted(&self) -> bool {
        self.0 == 0
    }

    /// Get remaining fuel
    pub fn remaining(&self) -> u64 {
        self.0
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // tests
// ═══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bounded_unit_clamps_low() {
        let bu = BoundedUnit::new(-0.5);
        assert_eq!(bu.value(), 0.0);
    }

    #[test]
    fn bounded_unit_clamps_high() {
        let bu = BoundedUnit::new(1.5);
        assert_eq!(bu.value(), 1.0);
    }

    #[test]
    fn bounded_unit_preserves_valid() {
        let bu = BoundedUnit::new(0.5);
        assert_eq!(bu.value(), 0.5);
    }

    #[test]
    fn fuel_consumption() {
        let fuel = Fuel::new(10);
        let after = fuel.consume_one();
        assert_eq!(after.remaining(), 9);
    }

    #[test]
    fn fuel_exhaustion() {
        let fuel = Fuel::ZERO;
        assert!(fuel.is_exhausted());
        // Consuming from zero doesn't underflow
        let after = fuel.consume_one();
        assert!(after.is_exhausted());
    }

    #[test]
    fn timestamp_increment() {
        let ts = Timestamp::new(100);
        let next = ts.increment();
        assert_eq!(next.value(), 101);
    }
}
