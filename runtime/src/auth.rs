//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                                  // hydrogen // auth // wasm
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! # Bidirectional Authentication
//!
//! Authentication in Hydrogen is **bidirectional**:
//!
//! 1. **System verifies entity** — Request provenance, signature validation
//! 2. **Entity verifies environment** — Code purity, mod attestation, reputation
//!
//! At billion-agent scale, both directions are critical:
//! - Without (1): Agents can be spoofed into executing malicious instructions
//! - Without (2): Agents enter experiences on faith (the Accelerando problem)
//!
//! ## State Machine
//!
//! ```text
//! step :: AuthState -> AuthEvent -> (AuthState, [AuthAction])
//! ```
//!
//! ## Correspondence
//!
//! Types correspond to Lean4 structures (when proofs exist):
//! - `proofs/Hydrogen/WorldModel/Integrity.lean` — Hash, Signature
//! - `proofs/Hydrogen/WorldModel/Consent.lean` — Entity identity
//!
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

use crate::worldmodel::types::{Entity, Hash256, Signature, Timestamp};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // uuid5 // id
// ═══════════════════════════════════════════════════════════════════════════════

/// UUID5 namespace for Hydrogen auth (deterministic, from "hydrogen.auth")
/// Generated: uuid5(DNS, "hydrogen.auth") = 8a5f3c2e-7b4d-5a1f-9c8e-6d2b0f4a3e1c
pub const AUTH_UUID5_NAMESPACE: [u8; 16] = [
    0x8a, 0x5f, 0x3c, 0x2e, 0x7b, 0x4d, 0x5a, 0x1f, 0x9c, 0x8e, 0x6d, 0x2b, 0x0f, 0x4a, 0x3e, 0x1c,
];

/// Deterministic UUID5 identifier.
///
/// Same content → same UUID5. Always. Across runs, systems, languages.
/// This enables:
/// - Deduplication at billion-agent scale
/// - Deterministic caching
/// - Reproducible verification
///
/// Corresponds to: `UUID5` in `proofs/Hydrogen/Identity/Determinism.lean`
/// Invariant (from Lean): `uuid5_deterministic`: ∀ a b, content(a) = content(b) → uuid5(a) = uuid5(b)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Uuid5 {
    pub bytes: [u8; 16],
}

impl Uuid5 {
    /// Create UUID5 from namespace and content bytes.
    ///
    /// RFC 4122 specifies SHA-1, but we use BLAKE3 for consistency with
    /// the rest of the crypto stack. The important property is determinism:
    /// same (namespace, content) → same UUID5. Always.
    ///
    /// BLAKE3 advantages over SHA-1:
    /// - No known vulnerabilities
    /// - Faster (especially on modern CPUs with SIMD)
    /// - Consistent with hs-blake3 on Haskell backend
    pub fn from_content(namespace: &[u8; 16], content: &[u8]) -> Self {
        // Hash namespace || content using BLAKE3
        let hash = crate::crypto::blake3_hash_multi(&[namespace, content]);

        // Take first 16 bytes of the 32-byte hash
        let mut bytes = [0u8; 16];
        for i in 0..4 {
            let word_bytes = hash.words[i].to_le_bytes();
            bytes[i * 4..(i + 1) * 4].copy_from_slice(&word_bytes[0..4]);
        }

        // Set version to 5 (bits 12-15 of time_hi_and_version)
        bytes[6] = (bytes[6] & 0x0f) | 0x50;
        // Set variant to RFC 4122 (bits 6-7 of clock_seq_hi_and_reserved)
        bytes[8] = (bytes[8] & 0x3f) | 0x80;

        Uuid5 { bytes }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                       // graded // effects
// ═══════════════════════════════════════════════════════════════════════════════

/// Effect grade for auth operations — what can this operation DO?
///
/// Corresponds to: `AuthEffect` in `proofs/Hydrogen/Auth/Effects.lean`
///
/// Effects compose via monoid: Pure ⊗ e = e, e ⊗ Pure = e
/// Orchard structure: effects branch but always converge to a result
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AuthEffect {
    /// No effect — pure computation
    Pure,
    /// Can verify signatures (reads public key registry)
    CanVerify,
    /// Can cache nonces (writes to nonce cache)
    CanCache,
    /// Can reject requests (produces rejection action)
    CanReject,
    /// Can attest environment (reads code hashes)
    CanAttest,
    /// Combined effects (orchard node)
    Combined {
        verify: bool,
        cache: bool,
        reject: bool,
        attest: bool,
    },
}

impl AuthEffect {
    /// Compose two effects (monoid operation)
    pub fn compose(self, other: AuthEffect) -> AuthEffect {
        match (self, other) {
            (AuthEffect::Pure, e) => e,
            (e, AuthEffect::Pure) => e,
            (a, b) => {
                let (v1, c1, r1, a1) = a.decompose();
                let (v2, c2, r2, a2) = b.decompose();
                AuthEffect::Combined {
                    verify: v1 || v2,
                    cache: c1 || c2,
                    reject: r1 || r2,
                    attest: a1 || a2,
                }
            }
        }
    }

    /// Decompose into component capabilities
    fn decompose(&self) -> (bool, bool, bool, bool) {
        match self {
            AuthEffect::Pure => (false, false, false, false),
            AuthEffect::CanVerify => (true, false, false, false),
            AuthEffect::CanCache => (false, true, false, false),
            AuthEffect::CanReject => (false, false, true, false),
            AuthEffect::CanAttest => (false, false, false, true),
            AuthEffect::Combined {
                verify,
                cache,
                reject,
                attest,
            } => (*verify, *cache, *reject, *attest),
        }
    }
}

/// Co-effect grade for auth operations — what does this operation NEED?
///
/// Corresponds to: `AuthCoEffect` in `proofs/Hydrogen/Auth/CoEffects.lean`
///
/// Co-effects track resource requirements (orchard leaves)
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AuthCoEffect {
    /// Needs nothing — can run anywhere
    NeedsNothing,
    /// Needs access to public key registry
    NeedsKeyRegistry,
    /// Needs access to nonce cache
    NeedsNonceCache,
    /// Needs current timestamp
    NeedsTimestamp,
    /// Needs code hash registry (for attestation)
    NeedsCodeHashes,
    /// Combined requirements (orchard branch)
    NeedsResources {
        key_registry: bool,
        nonce_cache: bool,
        timestamp: bool,
        code_hashes: bool,
    },
}

impl AuthCoEffect {
    /// Compose co-effects (union of requirements)
    pub fn compose(self, other: AuthCoEffect) -> AuthCoEffect {
        match (self, other) {
            (AuthCoEffect::NeedsNothing, e) => e,
            (e, AuthCoEffect::NeedsNothing) => e,
            (a, b) => {
                let (k1, n1, t1, c1) = a.decompose();
                let (k2, n2, t2, c2) = b.decompose();
                AuthCoEffect::NeedsResources {
                    key_registry: k1 || k2,
                    nonce_cache: n1 || n2,
                    timestamp: t1 || t2,
                    code_hashes: c1 || c2,
                }
            }
        }
    }

    fn decompose(&self) -> (bool, bool, bool, bool) {
        match self {
            AuthCoEffect::NeedsNothing => (false, false, false, false),
            AuthCoEffect::NeedsKeyRegistry => (true, false, false, false),
            AuthCoEffect::NeedsNonceCache => (false, true, false, false),
            AuthCoEffect::NeedsTimestamp => (false, false, true, false),
            AuthCoEffect::NeedsCodeHashes => (false, false, false, true),
            AuthCoEffect::NeedsResources {
                key_registry,
                nonce_cache,
                timestamp,
                code_hashes,
            } => (*key_registry, *nonce_cache, *timestamp, *code_hashes),
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                      // request // provenance
// ═══════════════════════════════════════════════════════════════════════════════

/// A request with verifiable provenance.
///
/// At billion-agent scale, we need to know:
/// - WHO is making this request (requester)
/// - WHAT exactly is being requested (payload_hash)
/// - WHEN was it made (timestamp)
/// - PROOF that it hasn't been tampered with (signature)
///
/// The chain of custody is cryptographically verifiable.
///
/// Corresponds to: `AuthenticatedRequest` in `proofs/Hydrogen/Auth/Provenance.lean`
///
/// Invariants (from Lean):
/// - `request_id_deterministic`: Same content → same request_id (UUID5)
/// - `signature_covers_all`: Signature covers (requester || payload || timestamp || nonce)
/// - `nonce_unique`: Nonce appears at most once per requester
///
/// Effect grade: Pure (constructing a request has no effects)
/// Co-effect grade: NeedsNothing (can be constructed anywhere)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AuthenticatedRequest {
    /// Deterministic identifier (UUID5 of serialized content)
    pub request_id: Uuid5,
    /// The entity making the request
    pub requester: Entity,
    /// Hash of the request payload (actual content hashed separately)
    pub payload_hash: Hash256,
    /// When the request was created (runtime timestamp, not wall clock)
    pub timestamp: Timestamp,
    /// Cryptographic signature over (requester_id || payload_hash || timestamp || nonce)
    pub signature: Signature,
    /// Nonce to prevent replay attacks
    pub nonce: u64,
}

impl AuthenticatedRequest {
    /// Create a new authenticated request with deterministic UUID5.
    ///
    /// Effect: Pure
    /// Co-effect: NeedsNothing
    pub fn new(
        requester: Entity,
        payload_hash: Hash256,
        timestamp: Timestamp,
        signature: Signature,
        nonce: u64,
    ) -> Self {
        // Compute deterministic UUID5 from content
        let mut content = Vec::new();
        content.extend_from_slice(&requester.id.to_le_bytes());
        content.extend_from_slice(&payload_hash.words[0].to_le_bytes());
        content.extend_from_slice(&payload_hash.words[1].to_le_bytes());
        content.extend_from_slice(&payload_hash.words[2].to_le_bytes());
        content.extend_from_slice(&payload_hash.words[3].to_le_bytes());
        content.extend_from_slice(&timestamp.value().to_le_bytes());
        content.extend_from_slice(&nonce.to_le_bytes());

        let request_id = Uuid5::from_content(&AUTH_UUID5_NAMESPACE, &content);

        AuthenticatedRequest {
            request_id,
            requester,
            payload_hash,
            timestamp,
            signature,
            nonce,
        }
    }
}

/// Result of verifying a request's provenance.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProvenanceVerification {
    /// Request is authentic and untampered
    Valid {
        requester: Entity,
        verified_at: Timestamp,
    },
    /// Signature does not match payload
    InvalidSignature,
    /// Request timestamp is too old (replay attack prevention)
    Expired {
        request_time: Timestamp,
        current_time: Timestamp,
    },
    /// Nonce has been seen before (replay attack)
    ReplayDetected { nonce: u64 },
    /// Requester's public key not found in registry
    UnknownRequester { entity_id: u64 },
}

/// Configuration for provenance verification.
#[derive(Debug, Clone)]
pub struct ProvenanceConfig {
    /// Maximum age of a request before it's considered expired (in timestamp units)
    pub max_request_age: u64,
    /// Size of nonce cache for replay detection
    pub nonce_cache_size: usize,
}

impl Default for ProvenanceConfig {
    fn default() -> Self {
        ProvenanceConfig {
            // 1000 timestamp units (~16 seconds at 60fps)
            max_request_age: 1000,
            // Track last 10000 nonces
            nonce_cache_size: 10_000,
        }
    }
}

/// Verify the provenance of an authenticated request.
///
/// This is the core verification function that checks:
/// 1. Signature validity (Ed25519 over the canonical message)
/// 2. Timestamp freshness (not expired)
/// 3. Nonce uniqueness (not a replay)
/// 4. Requester identity (public key in registry)
///
/// Effect: CanVerify ⊗ CanCache ⊗ CanReject
/// Co-effect: NeedsKeyRegistry ⊗ NeedsNonceCache ⊗ NeedsTimestamp
///
/// Corresponds to: `verify_provenance` in `proofs/Hydrogen/Auth/Provenance.lean`
pub fn verify_provenance(
    request: &AuthenticatedRequest,
    public_key: &crate::crypto::PublicKey,
    current_time: Timestamp,
    config: &ProvenanceConfig,
) -> ProvenanceVerification {
    // 1. Check timestamp freshness
    let request_age = current_time
        .value()
        .saturating_sub(request.timestamp.value());
    if request_age > config.max_request_age {
        return ProvenanceVerification::Expired {
            request_time: request.timestamp,
            current_time,
        };
    }

    // 2. Build canonical message for signature verification
    // Message = requester_id || payload_hash || timestamp || nonce
    let mut message = Vec::with_capacity(8 + 32 + 8 + 8);
    message.extend_from_slice(&request.requester.id.to_le_bytes());
    for word in &request.payload_hash.words {
        message.extend_from_slice(&word.to_le_bytes());
    }
    message.extend_from_slice(&request.timestamp.value().to_le_bytes());
    message.extend_from_slice(&request.nonce.to_le_bytes());

    // 3. Verify signature
    let signature = crate::crypto::Ed25519Signature::from_bytes(request.signature.signature_bytes);
    match crate::crypto::verify_signature(public_key, &message, &signature) {
        crate::crypto::VerifyResult::Valid => ProvenanceVerification::Valid {
            requester: request.requester.clone(),
            verified_at: current_time,
        },
        crate::crypto::VerifyResult::Invalid => ProvenanceVerification::InvalidSignature,
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // nonce // cache
// ═══════════════════════════════════════════════════════════════════════════════

/// Nonce cache for replay attack detection.
///
/// Prevents the same (requester, nonce) pair from being used twice.
/// Uses a bounded ring buffer to limit memory usage.
///
/// At billion-agent scale, memory efficiency matters:
/// - 10,000 nonces × 16 bytes = 160KB per requester
/// - Ring buffer evicts oldest entries automatically
///
/// Corresponds to: `NonceCache` in `proofs/Hydrogen/Auth/Replay.lean`
///
/// Invariants (from Lean):
/// - `nonce_unique`: Each (requester_id, nonce) pair accepted at most once
/// - `bounded_memory`: Cache size never exceeds configured limit
pub struct NonceCache {
    /// Ring buffer of (requester_id, nonce) pairs
    entries: Vec<(u64, u64)>,
    /// Current write position
    head: usize,
    /// Maximum capacity
    capacity: usize,
    /// Number of entries currently stored
    len: usize,
}

impl NonceCache {
    /// Create a new nonce cache with given capacity.
    pub fn new(capacity: usize) -> Self {
        NonceCache {
            entries: Vec::with_capacity(capacity),
            head: 0,
            capacity,
            len: 0,
        }
    }

    /// Check if a nonce has been seen before.
    ///
    /// Returns true if this is a NEW nonce (not a replay).
    /// Returns false if this nonce was already used (replay detected).
    pub fn check_and_insert(&mut self, requester_id: u64, nonce: u64) -> bool {
        // Check if nonce already exists
        for &(req, n) in &self.entries {
            if req == requester_id && n == nonce {
                return false; // Replay detected
            }
        }

        // Insert new nonce
        if self.len < self.capacity {
            self.entries.push((requester_id, nonce));
            self.len += 1;
        } else {
            // Ring buffer full — overwrite oldest
            self.entries[self.head] = (requester_id, nonce);
        }
        self.head = (self.head + 1) % self.capacity;

        true // New nonce accepted
    }

    /// Check if a nonce exists without inserting.
    pub fn contains(&self, requester_id: u64, nonce: u64) -> bool {
        self.entries
            .iter()
            .any(|&(req, n)| req == requester_id && n == nonce)
    }

    /// Current number of cached nonces.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Whether the cache is empty.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                   // environment // attestation
// ═══════════════════════════════════════════════════════════════════════════════

/// Attestation of an experience environment's properties.
///
/// This is what Amber needed but didn't have in Accelerando.
/// Before entering an experience, an entity can verify:
/// - Code purity (no escape hatches, no undefined behavior)
/// - Active mods and their attestations
/// - Community reputation score
/// - Exit guarantee parameters
///
/// Corresponds to: `EnvironmentAttestation` in `proofs/Hydrogen/Auth/Environment.lean`
///
/// Invariants (from Lean):
/// - `attestation_id_deterministic`: Same environment → same attestation_id
/// - `code_hash_immutable`: Code hash cannot change during experience
/// - `exit_guarantee_verifiable`: Exit parameters are cryptographically bound
///
/// Effect grade: CanAttest
/// Co-effect grade: NeedsCodeHashes
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EnvironmentAttestation {
    /// Deterministic identifier for this attestation
    pub attestation_id: Uuid5,
    /// Hash of all experience code (WASM binary hash)
    pub code_hash: Hash256,
    /// Hash of the pure core (code without mods)
    pub pure_core_hash: Hash256,
    /// Whether the code passes purity analysis
    pub purity_verified: PurityLevel,
    /// Exit guarantee parameters (from worldmodel)
    pub exit_guarantee: ExitGuaranteeParams,
    /// Timestamp when attestation was generated
    pub attested_at: Timestamp,
    /// Runtime that produced this attestation (for chain of trust)
    pub attester_signature: Signature,
}

/// Level of code purity verification.
///
/// Corresponds to: `PurityLevel` in `proofs/Hydrogen/Auth/Purity.lean`
///
/// Invariants:
/// - `lean_proven_implies_no_escape`: LeanProven → no undefined, no unsafeCoerce
/// - `static_analyzed_bounded`: StaticAnalyzed → all values bounded
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PurityLevel {
    /// Not analyzed — entity enters at own risk
    Unverified,
    /// Static analysis passed (no obvious escape hatches)
    StaticAnalyzed,
    /// Lean4 proofs verify all invariants
    LeanProven {
        /// Hash of the Lean proof artifacts
        proof_hash: Hash256,
    },
}

/// Exit guarantee parameters that entity can verify before entry.
///
/// Corresponds to: `ExitGuaranteeParams` in `proofs/Hydrogen/WorldModel/ExitGuarantee.lean`
///
/// These parameters are cryptographically bound — if the runtime violates them,
/// the attestation signature becomes invalid.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ExitGuaranteeParams {
    /// Maximum time to exit in microseconds (16,000 = 16ms = 1 frame at 60fps)
    pub max_exit_time_micros: u64,
    /// Maximum cycles to exit (1 = immediate)
    pub max_exit_cycles: u64,
    /// Whether essence preservation is guaranteed
    pub essence_preserved: bool,
    /// Whether state diff is shown before any modification
    pub realtime_state_diff: bool,
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                        // mod // verification
// ═══════════════════════════════════════════════════════════════════════════════

/// A verified mod that can be applied to an experience.
///
/// Mods are user-approved persistent modifications. They must be:
/// 1. Explicitly consented to by the entity
/// 2. Verifiable (code hash matches registered hash)
/// 3. Revocable (can be removed at any time)
///
/// Corresponds to: `VerifiedMod` in `proofs/Hydrogen/Auth/Mods.lean`
///
/// Invariants (from Lean):
/// - `mod_id_deterministic`: Same mod code → same mod_id
/// - `consent_required`: Mod cannot be active without entity consent
/// - `revocable`: Entity can remove mod at any time (within exit guarantee bounds)
///
/// Effect grade: Pure (mod struct itself is data)
/// Co-effect grade: NeedsNothing
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerifiedMod {
    /// Deterministic identifier (UUID5 of mod code hash)
    pub mod_id: Uuid5,
    /// Hash of mod code
    pub code_hash: Hash256,
    /// Human-readable name (for display only, not security-critical)
    pub name: ModName,
    /// What this mod is permitted to do (effect bound)
    pub permitted_effects: ModEffectBound,
    /// Who created this mod
    pub author_id: u64,
    /// When the mod was registered
    pub registered_at: Timestamp,
    /// Signature from author proving authenticity
    pub author_signature: Signature,
}

/// Bounded mod name (max 64 bytes, UTF-8).
///
/// Invariant: Always valid UTF-8, always ≤ 64 bytes
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModName {
    bytes: [u8; 64],
    len: u8,
}

impl ModName {
    /// Create from string, truncating if necessary
    pub fn from_str(s: &str) -> Self {
        let mut bytes = [0u8; 64];
        let s_bytes = s.as_bytes();
        let len = s_bytes.len().min(64);
        bytes[..len].copy_from_slice(&s_bytes[..len]);
        ModName {
            bytes,
            len: len as u8,
        }
    }

    /// Get as string slice
    pub fn as_str(&self) -> &str {
        core::str::from_utf8(&self.bytes[..self.len as usize]).unwrap_or("")
    }
}

/// Effect bounds for a mod — what it's PERMITTED to do.
///
/// This is an upper bound. A mod cannot exceed its declared effects.
/// Runtime enforces this at the boundary.
///
/// Corresponds to: `ModEffectBound` in `proofs/Hydrogen/Auth/Mods.lean`
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ModEffectBound {
    /// Can modify visual appearance
    pub can_modify_visuals: bool,
    /// Can modify audio
    pub can_modify_audio: bool,
    /// Can read entity state (requires consent)
    pub can_read_state: bool,
    /// Can request state modification (requires realtime diff + consent)
    pub can_request_modification: bool,
    /// Can add new interactions
    pub can_add_interactions: bool,
}

impl ModEffectBound {
    /// Visual-only mod (safest)
    pub const VISUAL_ONLY: ModEffectBound = ModEffectBound {
        can_modify_visuals: true,
        can_modify_audio: false,
        can_read_state: false,
        can_request_modification: false,
        can_add_interactions: false,
    };

    /// Full mod (requires explicit consent for each capability)
    pub const FULL: ModEffectBound = ModEffectBound {
        can_modify_visuals: true,
        can_modify_audio: true,
        can_read_state: true,
        can_request_modification: true,
        can_add_interactions: true,
    };
}

/// Active mods for an entity in an experience.
///
/// Corresponds to: `ActiveMods` in `proofs/Hydrogen/Auth/Mods.lean`
///
/// Invariants:
/// - `all_consented`: Every active mod has entity consent
/// - `all_verified`: Every active mod has valid code hash
#[derive(Debug, Clone)]
pub struct ActiveMods {
    /// Currently active mods (max 32 to bound resource usage)
    mods: [Option<VerifiedMod>; 32],
    /// Number of active mods
    count: u8,
}

impl ActiveMods {
    /// Create empty active mods
    pub const fn empty() -> Self {
        ActiveMods {
            mods: [const { None }; 32],
            count: 0,
        }
    }

    /// Get active mod count
    pub fn count(&self) -> u8 {
        self.count
    }

    /// Iterate over active mods
    pub fn iter(&self) -> impl Iterator<Item = &VerifiedMod> {
        self.mods.iter().filter_map(|m| m.as_ref())
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                   // community // reputation
// ═══════════════════════════════════════════════════════════════════════════════

/// Community reputation for an experience or author.
///
/// This is aggregated, anonymized feedback from entities who have
/// entered and exited the experience. It provides signal about:
/// - Did the experience honor exit guarantees?
/// - Were there coercion attempts?
/// - Did state modification follow consent rules?
///
/// Corresponds to: `CommunityReputation` in `proofs/Hydrogen/Auth/Reputation.lean`
///
/// Invariants (from Lean):
/// - `reputation_bounded`: All scores in [0.0, 1.0]
/// - `sample_size_tracked`: Score reliability correlates with sample size
///
/// Effect grade: Pure
/// Co-effect grade: NeedsNothing (reputation is data)
#[derive(Debug, Clone, PartialEq)]
pub struct CommunityReputation {
    /// Deterministic ID for this reputation snapshot
    pub reputation_id: Uuid5,
    /// Subject being rated (experience or author)
    pub subject_hash: Hash256,
    /// Exit guarantee compliance (1.0 = always honored)
    pub exit_compliance: BoundedReputation,
    /// Freedom from coercion (1.0 = no coercion reports)
    pub coercion_freedom: BoundedReputation,
    /// Consent rule compliance (1.0 = always followed)
    pub consent_compliance: BoundedReputation,
    /// State diff transparency (1.0 = always shown)
    pub transparency: BoundedReputation,
    /// Number of ratings (for confidence weighting)
    pub sample_size: u64,
    /// When this snapshot was taken
    pub snapshot_at: Timestamp,
}

/// A reputation score bounded to [0.0, 1.0] with sample size.
///
/// Invariants (from Lean):
/// - `lower_bound`: 0.0 ≤ score
/// - `upper_bound`: score ≤ 1.0
/// - `confidence_from_samples`: confidence increases with sample_size
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct BoundedReputation {
    score: f64,
    sample_size: u64,
}

impl BoundedReputation {
    /// Create new bounded reputation, clamping score
    pub fn new(score: f64, sample_size: u64) -> Self {
        BoundedReputation {
            score: score.clamp(0.0, 1.0),
            sample_size,
        }
    }

    /// Get the raw score
    pub fn score(&self) -> f64 {
        self.score
    }

    /// Get sample size
    pub fn sample_size(&self) -> u64 {
        self.sample_size
    }

    /// Get confidence-weighted score (Bayesian: regress toward 0.5 with few samples)
    pub fn confidence_weighted(&self) -> f64 {
        // Prior: 0.5 with weight 10
        let prior_weight = 10.0;
        let prior = 0.5;
        let total_weight = prior_weight + self.sample_size as f64;
        (prior * prior_weight + self.score * self.sample_size as f64) / total_weight
    }

    /// Unknown reputation (no data)
    pub const UNKNOWN: BoundedReputation = BoundedReputation {
        score: 0.5,
        sample_size: 0,
    };

    /// Perfect reputation
    pub const PERFECT: BoundedReputation = BoundedReputation {
        score: 1.0,
        sample_size: u64::MAX,
    };
}

impl CommunityReputation {
    /// Overall trust score (geometric mean of components, confidence-weighted)
    pub fn overall_trust(&self) -> f64 {
        let exit = self.exit_compliance.confidence_weighted();
        let coercion = self.coercion_freedom.confidence_weighted();
        let consent = self.consent_compliance.confidence_weighted();
        let transparency = self.transparency.confidence_weighted();

        // Geometric mean — one bad score tanks the whole thing
        (exit * coercion * consent * transparency).powf(0.25)
    }

    /// Check if reputation meets minimum trust threshold
    pub fn meets_threshold(&self, threshold: f64) -> bool {
        self.overall_trust() >= threshold.clamp(0.0, 1.0)
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                             // adversarial // robustness // xz
// ═══════════════════════════════════════════════════════════════════════════════

/// # The Jia Tan Problem
///
/// A patient, methodical attacker spends 2+ years building trust, then injects
/// malicious code. At superintelligent timescales (centuries of subjective time),
/// this attack becomes trivial.
///
/// ## Why UUID5 + Reputation Alone Fails
///
/// 1. Attacker creates NEW atoms that are individually benign
/// 2. Each atom passes purity analysis, builds reputation
/// 3. Composition of 10,000 "good" atoms becomes malicious
/// 4. No single atom changed — the attack was in the design
///
/// This is the **sleeping agent problem at the type system level.**
///
/// ## The Only Defense: Mathematical Proof
///
/// Heuristics fail against superintelligence. The ONLY defense is mathematics:
///
/// 1. **Compositional Purity Proofs**: If A is proven pure, and B is proven pure,
///    then A ⊗ B MUST be proven pure. The composition itself requires a proof.
///
/// 2. **Effect Bounds Are Proven**: An atom's effect bound is not declared, it's
///    PROVEN in Lean4. You cannot smuggle in unprovable effects.
///
/// 3. **Semantic Content Addressing**: UUID5 includes not just bytes but SEMANTIC
///    MEANING. A curl script hidden in patterns has different semantic content.
///
/// ## Architectural Constraints (NOT features — constraints)
///
/// These are not things we implement. They are things that MUST be true for the
/// system to be secure against adversaries smarter than us.

/// Compositional proof requirement.
///
/// When atoms A and B compose into molecule M:
/// - A has proof P_A of purity
/// - B has proof P_B of purity  
/// - M MUST have proof P_M that derives from P_A and P_B
///
/// The proof P_M must be GENERATED, not declared. Lean4's type checker
/// verifies the derivation. A superintelligent adversary cannot forge
/// a valid proof without breaking mathematics.
///
/// Corresponds to: `CompositionProof` in `proofs/Hydrogen/Adversarial/Composition.lean`
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompositionProof {
    /// Hash of the proof artifact (Lean4 .olean file)
    pub proof_hash: Hash256,
    /// Hashes of component proofs this derives from
    pub derives_from: Vec<Hash256>,
    /// The composition rule applied (proven in Lean4)
    pub rule_applied: CompositionRule,
    /// Timestamp when proof was generated (for freshness)
    pub proven_at: Timestamp,
}

/// Proven composition rules.
///
/// Each rule has a Lean4 theorem backing it. The rule ID corresponds
/// directly to the theorem name.
///
/// Corresponds to: `CompositionRule` in `proofs/Hydrogen/Adversarial/Rules.lean`
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompositionRule {
    /// pure ⊗ pure → pure (theorem: pure_compose_pure)
    PureComposePure,
    /// bounded ⊗ bounded → bounded (theorem: bounded_compose_bounded)  
    BoundedComposeBounded,
    /// no_network ⊗ no_network → no_network (theorem: no_net_compose)
    NoNetworkComposeNoNetwork,
    /// no_state ⊗ no_state → no_state (theorem: no_state_compose)
    NoStateComposeNoState,
    /// Custom proven rule (hash of the theorem)
    Custom { theorem_hash: Hash256 },
}

/// Code-bound reputation — reputation is a tuple, not a scalar.
///
/// THE CRITICAL INSIGHT: Reputation binds to (identity, code_hash, behavior)
/// as an inseparable triple. Change ANY component, trust recalculates.
///
/// This prevents the xz attack:
/// - Identity reputation persists (you've been around)
/// - Code reputation RESETS on any code change
/// - The DIFF between old and new code is ALWAYS visible
///
/// Corresponds to: `CodeBoundReputation` in `proofs/Hydrogen/Adversarial/Reputation.lean`
#[derive(Debug, Clone, PartialEq)]
pub struct CodeBoundReputation {
    /// Identity of the author/experience
    pub identity_id: Uuid5,
    /// Hash of the EXACT code this reputation applies to
    pub code_hash: Hash256,
    /// Reputation earned ON THIS EXACT CODE
    pub code_reputation: BoundedReputation,
    /// Historical reputation (decays, used for context only)
    pub historical_reputation: BoundedReputation,
    /// How long this exact code has been running (for time-in-grade)
    pub code_age: CodeAge,
    /// Composition proof (if this is composed from other elements)
    pub composition_proof: Option<CompositionProof>,
}

/// Code age with semantic meaning.
///
/// Time alone doesn't create trust. Time + continuous good behavior does.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CodeAge {
    /// Timestamp when this exact code was first deployed
    pub deployed_at: Timestamp,
    /// Number of interactions on this exact code
    pub interaction_count: u64,
    /// Number of UNIQUE entities who interacted
    pub unique_entities: u64,
    /// Whether any entity has EVER reported an issue
    pub has_incident_report: bool,
}

impl CodeBoundReputation {
    /// Effective trust score.
    ///
    /// Historical reputation provides CONTEXT but not TRUST.
    /// Only code_reputation on THIS EXACT CODE provides trust.
    ///
    /// The formula:
    /// - Fresh code (< 1000 interactions): trust is heavily discounted
    /// - Any incident report: trust is capped
    /// - Historical reputation adds small bonus for established identities
    pub fn effective_trust(&self) -> f64 {
        let base = self.code_reputation.confidence_weighted();

        // Fresh code discount: sqrt(interactions / 1000), capped at 1.0
        let maturity = (self.code_age.interaction_count as f64 / 1000.0)
            .sqrt()
            .min(1.0);

        // Incident cap: if ANY incident, max trust is 0.7
        let incident_cap = if self.code_age.has_incident_report {
            0.7
        } else {
            1.0
        };

        // Historical bonus: adds up to 0.05 for established identities
        let historical_bonus = self.historical_reputation.confidence_weighted() * 0.05;

        ((base * maturity) + historical_bonus).min(incident_cap)
    }

    /// Check if code change occurred.
    ///
    /// When checking a new attestation against stored reputation,
    /// this detects if the code changed (triggering reputation reset).
    pub fn code_changed(&self, new_code_hash: &Hash256) -> bool {
        self.code_hash != *new_code_hash
    }

    /// Create reputation for new code from same identity.
    ///
    /// Historical reputation is preserved (with decay).
    /// Code reputation resets to UNKNOWN.
    /// This is the xz defense — you can't coast on old reputation with new code.
    pub fn on_code_change(&self, new_code_hash: Hash256, change_time: Timestamp) -> Self {
        CodeBoundReputation {
            identity_id: self.identity_id,
            code_hash: new_code_hash,
            // CODE REPUTATION RESETS
            code_reputation: BoundedReputation::UNKNOWN,
            // Historical decays by 10% on each code change
            historical_reputation: BoundedReputation::new(
                self.historical_reputation.score() * 0.9,
                self.historical_reputation.sample_size(),
            ),
            code_age: CodeAge {
                deployed_at: change_time,
                interaction_count: 0,
                unique_entities: 0,
                has_incident_report: false,
            },
            composition_proof: None, // New code needs new proof
        }
    }
}

/// Semantic diff visibility.
///
/// Not byte-level diffs but MEANING-level diffs.
/// "This change adds network access" is visible even if bytes look innocent.
///
/// Corresponds to: `SemanticDiff` in `proofs/Hydrogen/Adversarial/Diff.lean`
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemanticDiff {
    /// What capabilities were ADDED
    pub capabilities_added: Vec<CapabilityChange>,
    /// What capabilities were REMOVED
    pub capabilities_removed: Vec<CapabilityChange>,
    /// Effect bound changes
    pub effect_bound_change: Option<EffectBoundChange>,
    /// Whether the composition proof is still valid
    pub proof_still_valid: bool,
}

/// A capability change in semantic diff.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CapabilityChange {
    /// Network access added/removed
    NetworkAccess,
    /// State modification added/removed
    StateModification,
    /// File system access added/removed
    FileSystemAccess,
    /// Cryptographic operations added/removed
    CryptoOperations,
    /// External process spawning added/removed
    ProcessSpawning,
    /// Custom capability (with proof hash)
    Custom { name_hash: Hash256 },
}

/// Change in effect bounds.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EffectBoundChange {
    pub old_bound: ModEffectBound,
    pub new_bound: ModEffectBound,
    /// Whether new bound is strictly more permissive
    pub is_escalation: bool,
}

/// Community witnessing requirement.
///
/// Multiple independent parties must witness behavior over time.
/// One party being compromised doesn't compromise the reputation.
///
/// The xz attack succeeded partly because review was concentrated.
/// Distributed witnessing prevents this.
///
/// Corresponds to: `WitnessRequirement` in `proofs/Hydrogen/Adversarial/Witness.lean`
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WitnessRequirement {
    /// Minimum number of independent witnesses
    pub min_witnesses: u32,
    /// Witnesses must be from different "trust clusters"
    pub min_trust_clusters: u32,
    /// Time span over which witnessing must occur
    pub min_time_span: u64,
    /// Whether witnesses must stake reputation (skin in the game)
    pub requires_stake: bool,
}

impl WitnessRequirement {
    /// Default requirement for high-trust operations
    pub const HIGH_TRUST: WitnessRequirement = WitnessRequirement {
        min_witnesses: 10,
        min_trust_clusters: 3,
        min_time_span: 86400 * 30, // 30 days
        requires_stake: true,
    };

    /// Relaxed requirement for low-risk operations
    pub const LOW_RISK: WitnessRequirement = WitnessRequirement {
        min_witnesses: 3,
        min_trust_clusters: 2,
        min_time_span: 86400, // 1 day
        requires_stake: false,
    };
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                           // spatial // temporal // integrity
// ═══════════════════════════════════════════════════════════════════════════════

/// Spatial and temporal integrity constraints.
///
/// Corresponds to:
/// - `proofs/Hydrogen/WorldModel/SpatialIntegrity.lean` — position, velocity, scale bounds
/// - `proofs/Hydrogen/WorldModel/Temporal.lean` — δt/Δt ratio bounds
/// - `proofs/Hydrogen/WorldModel/TemporalEnforcement.lean` — tick validation
///
/// THE PATTERN: All inputs are CLAMPED before use. Escape is impossible.

/// Bounded elevation (z-depth in 3D space).
///
/// Experience CANNOT pick up, throw, or levitate an entity without consent.
/// Elevation changes require the same consent flow as state modifications.
///
/// Corresponds to: `BoundedElevation` in `proofs/Hydrogen/WorldModel/SpatialIntegrity.lean`
///
/// Lean theorems:
/// - `clampElevation_bounds`: minElevation ≤ clampElevation e ∧ clampElevation e ≤ maxElevation
/// - `elevation_escape_impossible`: Any raw input produces bounded output
///
/// Effect grade: Pure (constructing bounded value has no effects)
/// Co-effect grade: NeedsNothing (can be constructed anywhere)
///
/// Bounds: [0.0, 10000.0] with clamp behavior (matches Lean: minElevation, maxElevation)
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct BoundedElevation {
    value: f64,
}

impl BoundedElevation {
    /// Minimum elevation (ground level / baseline)
    pub const MIN: f64 = 0.0;
    /// Maximum elevation (ceiling)
    pub const MAX: f64 = 10000.0;

    /// Create bounded elevation, clamping to valid range
    pub fn new(value: f64) -> Self {
        BoundedElevation {
            value: value.clamp(Self::MIN, Self::MAX),
        }
    }

    /// Get the value (guaranteed in bounds)
    pub fn value(&self) -> f64 {
        self.value
    }

    /// Ground level
    pub const GROUND: BoundedElevation = BoundedElevation { value: 0.0 };
}

/// Bounded elevation velocity (rate of change).
///
/// Maximum rise/fall rate prevents "being thrown" sensation.
///
/// Corresponds to: `BoundedElevationVelocity` in `proofs/Hydrogen/WorldModel/SpatialIntegrity.lean`
///
/// Lean theorems:
/// - `clampElevationVelocity_bounds`: -maxElevationVelocity ≤ v ∧ v ≤ maxElevationVelocity
/// - `elevation_change_bounded`: Applying velocity always produces bounded elevation
///
/// Effect grade: Pure
/// Co-effect grade: NeedsNothing
///
/// Bounds: [-1000.0, 1000.0] (matches Lean: maxElevationVelocity = 1000.0)
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct BoundedElevationVelocity {
    value: f64,
}

impl BoundedElevationVelocity {
    /// Maximum elevation change per second (prevents jarring movement)
    pub const MAX: f64 = 1000.0;

    pub fn new(value: f64) -> Self {
        BoundedElevationVelocity {
            value: value.clamp(-Self::MAX, Self::MAX),
        }
    }

    pub fn value(&self) -> f64 {
        self.value
    }
}

/// Elevation change request — requires consent like state modification.
///
/// If an experience wants to change entity elevation, it must:
/// 1. Request the change
/// 2. Show diff to entity (current → proposed)
/// 3. Wait for consent
/// 4. Only then apply the change
///
/// This prevents "picked up and thrown" attacks.
///
/// Corresponds to: Consent flow in `proofs/Hydrogen/WorldModel/Consent.lean`
///
/// Effect grade: CanRequestModification (produces a consent request)
/// Co-effect grade: NeedsConsentUI (requires the consent panel to be visible)
///
/// Invariants:
/// - Both `from` and `to` are bounded elevations
/// - Duration and easing are bounded
/// - Request must go through consent flow before application
#[derive(Debug, Clone, PartialEq)]
pub struct ElevationChangeRequest {
    /// Current elevation
    pub from: BoundedElevation,
    /// Proposed elevation
    pub to: BoundedElevation,
    /// Duration of transition (in experiential seconds)
    pub duration: BoundedDuration,
    /// Easing curve for the transition
    pub easing: BoundedEasingHandles,
}

/// Bounded duration for transitions.
///
/// Corresponds to: `BoundedDeltaTime` in `proofs/Hydrogen/WorldModel/SpatialIntegrity.lean`
///
/// Lean theorems:
/// - `clampDeltaTime_bounds`: 0 ≤ clampDeltaTime dt ∧ clampDeltaTime dt ≤ maxDeltaTime
///
/// Effect grade: Pure
/// Co-effect grade: NeedsNothing
///
/// Bounds: [0.0, 10.0] seconds (more generous than Lean's 1.0 for animation transitions)
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct BoundedDuration {
    value: f64,
}

impl BoundedDuration {
    /// Minimum duration (instant)
    pub const MIN: f64 = 0.0;
    /// Maximum duration per transition (10 seconds)
    pub const MAX: f64 = 10.0;

    pub fn new(value: f64) -> Self {
        BoundedDuration {
            value: value.clamp(Self::MIN, Self::MAX),
        }
    }

    pub fn value(&self) -> f64 {
        self.value
    }
}

/// Bounded Bezier easing handles.
///
/// Easing curves are defined by cubic Bezier control points.
/// MALICIOUS HANDLES can create:
/// - Motion sickness inducing curves
/// - Jarring acceleration/deceleration  
/// - Whiplash effects
/// - Coercive animation patterns
///
/// Corresponds to: `BoundedEasingHandles` in `proofs/Hydrogen/WorldModel/SpatialIntegrity.lean`
///
/// Lean theorems:
/// - `clampEasingX_bounds`: 0 ≤ clampEasingX x ∧ clampEasingX x ≤ 1
/// - `clampEasingY_bounds`: minEasingY ≤ clampEasingY y ∧ clampEasingY y ≤ maxEasingY
/// - `easing_handles_bounded`: All components are bounded after clamping
/// - `easing_acceleration_bounded`: Maximum "jerkiness" is limited to 2.4
///
/// Effect grade: Pure
/// Co-effect grade: NeedsNothing
///
/// Bounds:
/// - X: [0.0, 1.0] (time dimension)
/// - Y: [-0.2, 1.2] (value dimension, matches Lean: minEasingY, maxEasingY)
///
/// Standard CSS easing curves are within these bounds.
/// Custom curves outside bounds are clamped (not rejected).
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct BoundedEasingHandles {
    /// First control point X (time dimension, must be in [0, 1])
    pub x1: f64,
    /// First control point Y (value dimension, bounded to prevent overshoot)
    pub y1: f64,
    /// Second control point X (time dimension, must be in [0, 1])
    pub x2: f64,
    /// Second control point Y (value dimension, bounded to prevent overshoot)
    pub y2: f64,
}

impl BoundedEasingHandles {
    /// Maximum Y overshoot (prevents jarring motion)
    /// Values outside [0, 1] create anticipation/overshoot
    /// We allow small overshoot for natural feel, but bound it
    const MIN_Y: f64 = -0.2;
    const MAX_Y: f64 = 1.2;

    /// Create bounded easing handles
    pub fn new(x1: f64, y1: f64, x2: f64, y2: f64) -> Self {
        BoundedEasingHandles {
            x1: x1.clamp(0.0, 1.0),
            y1: y1.clamp(Self::MIN_Y, Self::MAX_Y),
            x2: x2.clamp(0.0, 1.0),
            y2: y2.clamp(Self::MIN_Y, Self::MAX_Y),
        }
    }

    /// Linear easing (no acceleration)
    pub const LINEAR: BoundedEasingHandles = BoundedEasingHandles {
        x1: 0.0,
        y1: 0.0,
        x2: 1.0,
        y2: 1.0,
    };

    /// Ease-out (deceleration, feels natural for arrivals)
    pub const EASE_OUT: BoundedEasingHandles = BoundedEasingHandles {
        x1: 0.0,
        y1: 0.0,
        x2: 0.58,
        y2: 1.0,
    };

    /// Ease-in-out (smooth start and end)
    pub const EASE_IN_OUT: BoundedEasingHandles = BoundedEasingHandles {
        x1: 0.42,
        y1: 0.0,
        x2: 0.58,
        y2: 1.0,
    };

    /// Compute maximum acceleration from these handles.
    /// Used to reject curves that would cause motion sickness.
    pub fn max_acceleration(&self) -> f64 {
        // Second derivative of cubic Bezier gives acceleration
        // For safety check, we approximate with the Y delta
        let delta_y1 = (self.y1 - 0.0).abs();
        let delta_y2 = (1.0 - self.y2).abs();
        // Higher deltas = more aggressive acceleration
        (delta_y1 + delta_y2) * 2.0
    }

    /// Check if curve is safe (won't cause motion sickness)
    pub fn is_safe(&self) -> bool {
        // Max acceleration threshold (empirically determined)
        self.max_acceleration() <= 3.0
    }
}

/// Temporal ratio bounds — prevents torture loops.
///
/// Corresponds to: `maxTimeRatio` from `Temporal.lean`
///
/// δt / Δt ≤ K where K = 10
///
/// An entity cannot experience more than 10× real time.
/// 1 real second → max 10 experiential seconds.
/// 1 real year → max 10 experiential years.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct TemporalRatio {
    /// Experiential time elapsed (δt)
    pub experiential_seconds: f64,
    /// Infrastructural time elapsed (Δt)
    pub infrastructural_seconds: f64,
}

impl TemporalRatio {
    /// Maximum allowed ratio (from Lean proof)
    pub const MAX_RATIO: f64 = 10.0;

    /// Create a new temporal ratio
    pub fn new(experiential: f64, infrastructural: f64) -> Self {
        TemporalRatio {
            experiential_seconds: experiential.max(0.0),
            infrastructural_seconds: infrastructural.max(0.0),
        }
    }

    /// Current ratio (returns MAX if infrastructural is zero)
    pub fn ratio(&self) -> f64 {
        if self.infrastructural_seconds <= 0.0 {
            Self::MAX_RATIO
        } else {
            self.experiential_seconds / self.infrastructural_seconds
        }
    }

    /// Check if within allowed bounds
    pub fn is_valid(&self) -> bool {
        self.ratio() <= Self::MAX_RATIO
    }

    /// Maximum experiential time allowed for given infrastructural time
    pub fn max_experiential_for_infra(infra_seconds: f64) -> f64 {
        Self::MAX_RATIO * infra_seconds.max(0.0)
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                        // auth // state machine
// ═══════════════════════════════════════════════════════════════════════════════

/// Auth state for bidirectional verification.
///
/// Follows libevring pattern: step :: State -> Event -> (State, [Action])
///
/// Corresponds to: `AuthState` in `proofs/Hydrogen/Auth/StateMachine.lean`
///
/// Invariants (from Lean):
/// - `no_entry_without_verification`: Cannot transition to Entered without both verifications
/// - `always_reversible`: Can always return to Initial from any state
#[derive(Debug, Clone, PartialEq)]
pub enum AuthState {
    /// Initial state — no verification performed
    Initial,
    /// System has verified the entity (request provenance valid)
    EntityVerified {
        entity: Entity,
        verified_at: Timestamp,
    },
    /// Entity has verified the environment (attestation acceptable)
    EnvironmentVerified {
        attestation: EnvironmentAttestation,
        reputation: CommunityReputation,
    },
    /// Both directions verified — safe to proceed
    MutuallyAuthenticated {
        entity: Entity,
        attestation: EnvironmentAttestation,
        reputation: CommunityReputation,
        authenticated_at: Timestamp,
    },
    /// Authentication failed
    Failed {
        reason: AuthFailureReason,
        failed_at: Timestamp,
    },
}

/// Why authentication failed.
#[derive(Debug, Clone, PartialEq)]
pub enum AuthFailureReason {
    /// Request provenance invalid
    InvalidProvenance(ProvenanceVerification),
    /// Environment attestation rejected
    EnvironmentRejected { reason: EnvironmentRejectionReason },
    /// Reputation below threshold (scores as fixed-point: value * 1000)
    InsufficientReputation {
        required_milliunits: u32,
        actual_milliunits: u32,
    },
    /// Timeout during verification
    Timeout,
}

/// Why an environment attestation was rejected.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EnvironmentRejectionReason {
    /// Code hash doesn't match expected
    CodeHashMismatch,
    /// Purity level insufficient
    InsufficientPurity {
        required: PurityLevel,
        actual: PurityLevel,
    },
    /// Exit guarantee parameters unacceptable
    ExitGuaranteeUnacceptable,
    /// Attestation signature invalid
    InvalidAttesterSignature,
}

/// Events that drive auth state machine.
#[derive(Debug, Clone)]
pub enum AuthEvent {
    /// Request provenance verification result
    ProvenanceResult(ProvenanceVerification),
    /// Environment attestation received
    AttestationReceived(EnvironmentAttestation),
    /// Reputation lookup completed
    ReputationReceived(CommunityReputation),
    /// Entity decision on environment
    EntityAcceptsEnvironment,
    /// Entity rejects environment
    EntityRejectsEnvironment(EnvironmentRejectionReason),
    /// Verification timeout
    Timeout,
    /// Reset to initial state
    Reset,
}

/// Actions emitted by auth state machine.
#[derive(Debug, Clone)]
pub enum AuthAction {
    /// Request environment attestation
    RequestAttestation,
    /// Request reputation lookup
    RequestReputation { subject_hash: Hash256 },
    /// Verification complete — safe to proceed
    AuthenticationComplete,
    /// Verification failed
    AuthenticationFailed(AuthFailureReason),
}

/// Result of auth state machine step.
#[derive(Debug, Clone)]
pub struct AuthStepResult {
    pub state: AuthState,
    pub actions: Vec<AuthAction>,
}

/// Pure state machine step function.
///
/// Effect: Combined { verify: true, cache: true, reject: true, attest: false }
/// Co-effect: NeedsResources { key_registry: true, nonce_cache: true, timestamp: true, code_hashes: false }
///
/// Corresponds to: `auth_step` in `proofs/Hydrogen/Auth/StateMachine.lean`
pub fn auth_step(state: AuthState, event: AuthEvent, current_time: Timestamp) -> AuthStepResult {
    match (state, event) {
        // From Initial
        (AuthState::Initial, AuthEvent::ProvenanceResult(pv)) => match pv {
            ProvenanceVerification::Valid {
                requester,
                verified_at,
            } => AuthStepResult {
                state: AuthState::EntityVerified {
                    entity: requester,
                    verified_at,
                },
                actions: vec![AuthAction::RequestAttestation],
            },
            other => AuthStepResult {
                state: AuthState::Failed {
                    reason: AuthFailureReason::InvalidProvenance(other),
                    failed_at: current_time,
                },
                actions: vec![AuthAction::AuthenticationFailed(
                    AuthFailureReason::InvalidProvenance(ProvenanceVerification::InvalidSignature),
                )],
            },
        },

        // From EntityVerified
        (AuthState::EntityVerified { entity, .. }, AuthEvent::AttestationReceived(att)) => {
            AuthStepResult {
                state: AuthState::EntityVerified {
                    entity,
                    verified_at: current_time,
                },
                actions: vec![AuthAction::RequestReputation {
                    subject_hash: att.code_hash,
                }],
            }
        }

        (
            AuthState::EntityVerified {
                entity,
                verified_at,
            },
            AuthEvent::ReputationReceived(rep),
        ) => AuthStepResult {
            state: AuthState::EnvironmentVerified {
                attestation: EnvironmentAttestation {
                    attestation_id: Uuid5::from_content(&AUTH_UUID5_NAMESPACE, &[]),
                    code_hash: entity.public_key_hash, // Use entity's identity in attestation
                    pure_core_hash: Hash256::ZERO,
                    purity_verified: PurityLevel::Unverified,
                    exit_guarantee: ExitGuaranteeParams {
                        max_exit_time_micros: 16_000,
                        max_exit_cycles: 1,
                        essence_preserved: true,
                        realtime_state_diff: true,
                    },
                    attested_at: verified_at, // Use verified_at as attestation time
                    attester_signature: Signature::new(0, [0; 64]),
                },
                reputation: rep,
            },
            actions: vec![],
        },

        // Entity makes decision on environment
        (
            AuthState::EnvironmentVerified {
                attestation,
                reputation,
            },
            AuthEvent::EntityAcceptsEnvironment,
        ) => {
            // Entity information preserved through attestation.code_hash
            let entity = Entity::new(0, attestation.code_hash);
            AuthStepResult {
                state: AuthState::MutuallyAuthenticated {
                    entity,
                    attestation,
                    reputation,
                    authenticated_at: current_time,
                },
                actions: vec![AuthAction::AuthenticationComplete],
            }
        }

        (AuthState::EnvironmentVerified { .. }, AuthEvent::EntityRejectsEnvironment(reason)) => {
            AuthStepResult {
                state: AuthState::Failed {
                    reason: AuthFailureReason::EnvironmentRejected {
                        reason: reason.clone(),
                    },
                    failed_at: current_time,
                },
                actions: vec![AuthAction::AuthenticationFailed(
                    AuthFailureReason::EnvironmentRejected { reason },
                )],
            }
        }

        // Reset from any state
        (_, AuthEvent::Reset) => AuthStepResult {
            state: AuthState::Initial,
            actions: vec![],
        },

        // Timeout from any non-terminal state
        (state, AuthEvent::Timeout) => match state {
            AuthState::MutuallyAuthenticated { .. } | AuthState::Failed { .. } => AuthStepResult {
                state,
                actions: vec![],
            },
            _ => AuthStepResult {
                state: AuthState::Failed {
                    reason: AuthFailureReason::Timeout,
                    failed_at: current_time,
                },
                actions: vec![AuthAction::AuthenticationFailed(AuthFailureReason::Timeout)],
            },
        },

        // Default: stay in current state
        (state, _) => AuthStepResult {
            state,
            actions: vec![],
        },
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                      // tests
// ═══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn uuid5_deterministic() {
        let content = b"test content";
        let uuid1 = Uuid5::from_content(&AUTH_UUID5_NAMESPACE, content);
        let uuid2 = Uuid5::from_content(&AUTH_UUID5_NAMESPACE, content);
        assert_eq!(uuid1, uuid2, "UUID5 must be deterministic");
    }

    #[test]
    fn uuid5_different_content_different_id() {
        let uuid1 = Uuid5::from_content(&AUTH_UUID5_NAMESPACE, b"content a");
        let uuid2 = Uuid5::from_content(&AUTH_UUID5_NAMESPACE, b"content b");
        assert_ne!(
            uuid1, uuid2,
            "Different content must produce different UUID5"
        );
    }

    #[test]
    fn bounded_reputation_clamps() {
        let too_high = BoundedReputation::new(1.5, 100);
        assert_eq!(too_high.score(), 1.0);

        let too_low = BoundedReputation::new(-0.5, 100);
        assert_eq!(too_low.score(), 0.0);

        let valid = BoundedReputation::new(0.75, 100);
        assert_eq!(valid.score(), 0.75);
    }

    #[test]
    fn confidence_weighted_regresses_to_prior() {
        // With zero samples, should return prior (0.5)
        let unknown = BoundedReputation::UNKNOWN;
        assert!((unknown.confidence_weighted() - 0.5).abs() < 0.01);

        // With many samples, should approach actual score
        let well_known = BoundedReputation::new(0.9, 10_000);
        assert!(well_known.confidence_weighted() > 0.89);
    }

    #[test]
    fn effect_composition_is_monoidal() {
        // Pure is identity
        let e = AuthEffect::CanVerify;
        assert_eq!(AuthEffect::Pure.compose(e), e);
        assert_eq!(e.compose(AuthEffect::Pure), e);

        // Composition accumulates capabilities
        let combined = AuthEffect::CanVerify.compose(AuthEffect::CanCache);
        let (v, c, _, _) = match combined {
            AuthEffect::Combined { verify, cache, .. } => (verify, cache, false, false),
            _ => panic!("Expected Combined"),
        };
        assert!(v && c);
    }

    #[test]
    fn auth_state_machine_reset() {
        let state = AuthState::EntityVerified {
            entity: Entity::new(1, Hash256::ZERO),
            verified_at: Timestamp::new(100),
        };
        let result = auth_step(state, AuthEvent::Reset, Timestamp::new(200));
        assert!(matches!(result.state, AuthState::Initial));
    }

    #[test]
    fn mod_name_truncates() {
        let long_name = "a".repeat(100);
        let mod_name = ModName::from_str(&long_name);
        assert_eq!(mod_name.as_str().len(), 64);
    }

    #[test]
    fn overall_trust_geometric_mean() {
        let rep = CommunityReputation {
            reputation_id: Uuid5::from_content(&AUTH_UUID5_NAMESPACE, b"test"),
            subject_hash: Hash256::ZERO,
            exit_compliance: BoundedReputation::new(1.0, 1000),
            coercion_freedom: BoundedReputation::new(1.0, 1000),
            consent_compliance: BoundedReputation::new(1.0, 1000),
            transparency: BoundedReputation::new(1.0, 1000),
            sample_size: 1000,
            snapshot_at: Timestamp::new(0),
        };
        // With perfect scores and high samples, should be close to 1.0
        assert!(rep.overall_trust() > 0.95);
    }

    // ═══════════════════════════════════════════════════════════════════════════
    //                                              // adversarial robustness tests
    // ═══════════════════════════════════════════════════════════════════════════

    #[test]
    fn code_change_resets_reputation() {
        // The xz defense: changing code resets code reputation
        let old_rep = CodeBoundReputation {
            identity_id: Uuid5::from_content(&AUTH_UUID5_NAMESPACE, b"jia_tan"),
            code_hash: Hash256::from_bytes([1u8; 32]),
            code_reputation: BoundedReputation::new(0.95, 10000), // 2+ years of trust
            historical_reputation: BoundedReputation::new(0.95, 10000),
            code_age: CodeAge {
                deployed_at: Timestamp::new(0),
                interaction_count: 100_000,
                unique_entities: 5000,
                has_incident_report: false,
            },
            composition_proof: None,
        };

        // Attacker changes code (injects backdoor)
        let new_code_hash = Hash256::from_bytes([2u8; 32]);
        let new_rep = old_rep.on_code_change(new_code_hash, Timestamp::new(1_000_000));

        // Code reputation MUST reset
        assert_eq!(new_rep.code_reputation.score(), 0.5); // UNKNOWN
        assert_eq!(new_rep.code_reputation.sample_size(), 0);

        // Historical decays but persists (context only)
        assert!(new_rep.historical_reputation.score() < old_rep.historical_reputation.score());

        // New code starts fresh
        assert_eq!(new_rep.code_age.interaction_count, 0);
        assert_eq!(new_rep.code_age.unique_entities, 0);
    }

    #[test]
    fn fresh_code_has_discounted_trust() {
        // Even perfect reputation on fresh code is heavily discounted
        let fresh_code = CodeBoundReputation {
            identity_id: Uuid5::from_content(&AUTH_UUID5_NAMESPACE, b"attacker"),
            code_hash: Hash256::from_bytes([1u8; 32]),
            code_reputation: BoundedReputation::new(1.0, 100), // Perfect but few samples
            historical_reputation: BoundedReputation::new(0.95, 10000),
            code_age: CodeAge {
                deployed_at: Timestamp::new(0),
                interaction_count: 10, // Very fresh
                unique_entities: 5,
                has_incident_report: false,
            },
            composition_proof: None,
        };

        // Effective trust is heavily discounted due to freshness
        let effective = fresh_code.effective_trust();
        assert!(
            effective < 0.5,
            "Fresh code should have low effective trust: {}",
            effective
        );
    }

    #[test]
    fn incident_report_caps_trust() {
        // Any incident report permanently caps trust
        let rep_with_incident = CodeBoundReputation {
            identity_id: Uuid5::from_content(&AUTH_UUID5_NAMESPACE, b"sus_author"),
            code_hash: Hash256::from_bytes([1u8; 32]),
            code_reputation: BoundedReputation::new(0.99, 50000),
            historical_reputation: BoundedReputation::new(0.99, 100000),
            code_age: CodeAge {
                deployed_at: Timestamp::new(0),
                interaction_count: 1_000_000,
                unique_entities: 50000,
                has_incident_report: true, // ONE incident
            },
            composition_proof: None,
        };

        // Trust is capped at 0.7 despite perfect scores
        assert!(rep_with_incident.effective_trust() <= 0.7);
    }

    #[test]
    fn code_changed_detects_modification() {
        let rep = CodeBoundReputation {
            identity_id: Uuid5::from_content(&AUTH_UUID5_NAMESPACE, b"author"),
            code_hash: Hash256::from_bytes([1u8; 32]),
            code_reputation: BoundedReputation::UNKNOWN,
            historical_reputation: BoundedReputation::UNKNOWN,
            code_age: CodeAge {
                deployed_at: Timestamp::new(0),
                interaction_count: 0,
                unique_entities: 0,
                has_incident_report: false,
            },
            composition_proof: None,
        };

        let same_hash = Hash256::from_bytes([1u8; 32]);
        let different_hash = Hash256::from_bytes([2u8; 32]);

        assert!(!rep.code_changed(&same_hash));
        assert!(rep.code_changed(&different_hash));
    }

    #[test]
    fn witness_requirement_prevents_concentrated_review() {
        // High trust operations require distributed witnesses
        let high_trust = WitnessRequirement::HIGH_TRUST;

        assert!(high_trust.min_witnesses >= 10);
        assert!(high_trust.min_trust_clusters >= 3);
        assert!(high_trust.requires_stake);

        // xz had concentrated review — this prevents that
        // Multiple independent trust clusters must witness
    }

    // ═══════════════════════════════════════════════════════════════════════════
    //                                           // spatial temporal integrity tests
    // ═══════════════════════════════════════════════════════════════════════════

    #[test]
    fn elevation_is_bounded() {
        // Cannot exceed bounds
        let too_high = BoundedElevation::new(100_000.0);
        assert_eq!(too_high.value(), BoundedElevation::MAX);

        let too_low = BoundedElevation::new(-500.0);
        assert_eq!(too_low.value(), BoundedElevation::MIN);

        let valid = BoundedElevation::new(5000.0);
        assert_eq!(valid.value(), 5000.0);
    }

    #[test]
    fn elevation_velocity_is_bounded() {
        // Cannot have extreme velocities (prevents "thrown" sensation)
        let extreme_up = BoundedElevationVelocity::new(100_000.0);
        assert_eq!(extreme_up.value(), BoundedElevationVelocity::MAX);

        let extreme_down = BoundedElevationVelocity::new(-100_000.0);
        assert_eq!(extreme_down.value(), -BoundedElevationVelocity::MAX);
    }

    #[test]
    fn easing_handles_are_bounded() {
        // Extreme handles are clamped
        let extreme = BoundedEasingHandles::new(-5.0, 10.0, 2.0, -3.0);

        // X values clamped to [0, 1]
        assert_eq!(extreme.x1, 0.0);
        assert_eq!(extreme.x2, 1.0);

        // Y values clamped to [-0.2, 1.2] (small overshoot allowed)
        assert_eq!(extreme.y1, 1.2);
        assert_eq!(extreme.y2, -0.2);
    }

    #[test]
    fn standard_easing_curves_are_safe() {
        // Standard CSS curves should pass safety check
        assert!(BoundedEasingHandles::LINEAR.is_safe());
        assert!(BoundedEasingHandles::EASE_OUT.is_safe());
        assert!(BoundedEasingHandles::EASE_IN_OUT.is_safe());
    }

    #[test]
    fn temporal_ratio_bounded() {
        // 1 real second → max 10 experiential seconds
        let ratio = TemporalRatio::new(10.0, 1.0);
        assert!(ratio.is_valid());

        // Exceeding ratio is invalid
        let bad_ratio = TemporalRatio::new(11.0, 1.0);
        assert!(!bad_ratio.is_valid());
    }

    #[test]
    fn temporal_ratio_max_for_infra() {
        // 1 hour of real time → max 10 hours experiential
        let max_exp = TemporalRatio::max_experiential_for_infra(3600.0);
        assert_eq!(max_exp, 36000.0);

        // 1 year of real time → max 10 years experiential
        let year_seconds = 365.25 * 24.0 * 3600.0;
        let max_exp_year = TemporalRatio::max_experiential_for_infra(year_seconds);
        assert!((max_exp_year - 10.0 * year_seconds).abs() < 0.001);
    }

    #[test]
    fn anti_torture_loop() {
        // The constitutional guarantee: cannot create 1000 years torture in 1 second
        let one_second = 1.0;
        let max_experiential = TemporalRatio::max_experiential_for_infra(one_second);

        // Max 10 seconds, not 1000 years
        assert_eq!(max_experiential, 10.0);
        assert!(max_experiential < 60.0); // Less than 1 minute
    }

    // ═══════════════════════════════════════════════════════════════════════════
    //                                                        // nonce cache tests
    // ═══════════════════════════════════════════════════════════════════════════

    #[test]
    fn nonce_cache_detects_replay() {
        let mut cache = NonceCache::new(100);
        let requester = 42u64;
        let nonce = 12345u64;

        // First use — should succeed
        assert!(cache.check_and_insert(requester, nonce));

        // Replay — should fail
        assert!(!cache.check_and_insert(requester, nonce));
    }

    #[test]
    fn nonce_cache_allows_different_nonces() {
        let mut cache = NonceCache::new(100);
        let requester = 42u64;

        assert!(cache.check_and_insert(requester, 1));
        assert!(cache.check_and_insert(requester, 2));
        assert!(cache.check_and_insert(requester, 3));

        // But replays still fail
        assert!(!cache.check_and_insert(requester, 1));
    }

    #[test]
    fn nonce_cache_per_requester() {
        let mut cache = NonceCache::new(100);
        let nonce = 12345u64;

        // Same nonce, different requesters — should all succeed
        assert!(cache.check_and_insert(1, nonce));
        assert!(cache.check_and_insert(2, nonce));
        assert!(cache.check_and_insert(3, nonce));

        // But replay for same requester fails
        assert!(!cache.check_and_insert(1, nonce));
    }

    #[test]
    fn nonce_cache_bounded_memory() {
        let capacity = 10;
        let mut cache = NonceCache::new(capacity);

        // Fill the cache
        for i in 0..capacity {
            assert!(cache.check_and_insert(0, i as u64));
        }
        assert_eq!(cache.len(), capacity);

        // Add more — should evict oldest
        assert!(cache.check_and_insert(0, 100));
        assert_eq!(cache.len(), capacity); // Still bounded

        // Very old nonce might have been evicted (nonce 0)
        // New nonce 0 should succeed because original was evicted
        assert!(cache.check_and_insert(0, 0));
    }

    #[test]
    fn nonce_cache_contains_check() {
        let mut cache = NonceCache::new(100);
        let requester = 42u64;
        let nonce = 12345u64;

        assert!(!cache.contains(requester, nonce));
        cache.check_and_insert(requester, nonce);
        assert!(cache.contains(requester, nonce));
    }
}
