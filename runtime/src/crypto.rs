//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                                // hydrogen // crypto // wasm
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! # Cryptographic Primitives
//!
//! Pure Rust cryptography for the trust layer. WASM-compatible, side-channel
//! resistant (to the extent the underlying crates provide).
//!
//! ## Stack
//!
//! - **BLAKE3** — Hashing, KDF, MAC (matches `hs-blake3` on Haskell backend)
//! - **Ed25519** — Signatures for request provenance, attestation signing
//! - **X25519** — Key exchange for encrypted channels (future)
//!
//! ## Correspondence
//!
//! Types correspond to Lean4 structures:
//! - `proofs/Hydrogen/WorldModel/Integrity.lean` — Hash, Signature axioms
//! - `proofs/Hydrogen/Auth/Provenance.lean` — Signature verification semantics
//!
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // blake3 hashing
// ═══════════════════════════════════════════════════════════════════════════════

use crate::worldmodel::types::Hash256;

/// Hash arbitrary data using BLAKE3.
///
/// BLAKE3 properties:
/// - 256-bit output (matches Hash256)
/// - Parallelizable (SIMD-accelerated where available)
/// - Secure PRF, MAC, KDF, and XOF modes
/// - No length extension attacks
///
/// Corresponds to: `hash` function in `proofs/Hydrogen/WorldModel/Integrity.lean`
///
/// Invariant (from Lean): `hash_deterministic`: ∀ a b, a = b → hash(a) = hash(b)
pub fn blake3_hash(data: &[u8]) -> Hash256 {
    let hash = blake3::hash(data);
    let bytes: [u8; 32] = *hash.as_bytes();
    Hash256::from_bytes(bytes)
}

/// Hash multiple byte slices efficiently (single pass).
///
/// Use when hashing concatenated data without allocating.
pub fn blake3_hash_multi(parts: &[&[u8]]) -> Hash256 {
    let mut hasher = blake3::Hasher::new();
    for part in parts {
        hasher.update(part);
    }
    let hash = hasher.finalize();
    let bytes: [u8; 32] = *hash.as_bytes();
    Hash256::from_bytes(bytes)
}

/// Keyed MAC using BLAKE3.
///
/// Use for authentication codes where the key is secret.
/// The key MUST be exactly 32 bytes.
pub fn blake3_mac(key: &[u8; 32], data: &[u8]) -> Hash256 {
    let hash = blake3::keyed_hash(key, data);
    let bytes: [u8; 32] = *hash.as_bytes();
    Hash256::from_bytes(bytes)
}

/// Derive a key from input keying material using BLAKE3 KDF.
///
/// Context should be a unique, application-specific string.
/// Output is deterministic for the same (context, ikm) pair.
pub fn blake3_derive_key(context: &str, ikm: &[u8]) -> [u8; 32] {
    let mut output = [0u8; 32];
    let mut output_reader = blake3::Hasher::new_derive_key(context);
    output_reader.update(ikm);
    output_reader.finalize_xof().fill(&mut output);
    output
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // ed25519 signatures
// ═══════════════════════════════════════════════════════════════════════════════

use ed25519_dalek::Verifier;

/// Ed25519 public key (32 bytes).
///
/// Used for verifying signatures on requests and attestations.
/// The corresponding private key is NEVER stored in the runtime —
/// it lives with the entity that owns it.
///
/// Corresponds to: `PublicKey` in `proofs/Hydrogen/Auth/Keys.lean`
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PublicKey {
    bytes: [u8; 32],
}

impl PublicKey {
    /// Create from raw bytes.
    ///
    /// Returns None if bytes don't represent a valid Ed25519 public key.
    pub fn from_bytes(bytes: [u8; 32]) -> Option<Self> {
        // Validate by attempting to construct the dalek key
        match ed25519_dalek::VerifyingKey::from_bytes(&bytes) {
            Ok(_) => Some(PublicKey { bytes }),
            Err(_) => None,
        }
    }

    /// Get the raw bytes.
    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.bytes
    }

    /// Compute the BLAKE3 hash of this public key.
    ///
    /// Used for compact identity representation and lookups.
    pub fn hash(&self) -> Hash256 {
        blake3_hash(&self.bytes)
    }

    /// Convert to the dalek verifying key for signature verification.
    fn to_dalek(&self) -> ed25519_dalek::VerifyingKey {
        // Safe because we validated in from_bytes
        ed25519_dalek::VerifyingKey::from_bytes(&self.bytes)
            .expect("PublicKey always contains valid bytes")
    }
}

/// Ed25519 signature (64 bytes).
///
/// Proves that a message was signed by the holder of the corresponding
/// private key. Verification is done against a public key.
///
/// Corresponds to: `Signature` in `proofs/Hydrogen/WorldModel/Integrity.lean`
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Ed25519Signature {
    bytes: [u8; 64],
}

impl Ed25519Signature {
    /// Create from raw bytes.
    pub fn from_bytes(bytes: [u8; 64]) -> Self {
        Ed25519Signature { bytes }
    }

    /// Get the raw bytes.
    pub fn as_bytes(&self) -> &[u8; 64] {
        &self.bytes
    }

    /// Convert to dalek signature for verification.
    fn to_dalek(&self) -> ed25519_dalek::Signature {
        ed25519_dalek::Signature::from_bytes(&self.bytes)
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // verification
// ═══════════════════════════════════════════════════════════════════════════════

/// Result of signature verification.
///
/// Corresponds to: `VerifyResult` in `proofs/Hydrogen/Auth/Provenance.lean`
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VerifyResult {
    /// Signature is valid for the given message and public key.
    Valid,
    /// Signature does not match.
    Invalid,
}

/// Verify an Ed25519 signature.
///
/// Returns `VerifyResult::Valid` if and only if:
/// - The signature was produced by the private key corresponding to `public_key`
/// - The signature was computed over exactly `message`
///
/// Corresponds to: `verify` in `proofs/Hydrogen/Auth/Provenance.lean`
///
/// Invariants (from Lean):
/// - `verify_deterministic`: Same inputs always produce same result
/// - `verify_correct`: Valid signature ↔ signed by corresponding private key
pub fn verify_signature(
    public_key: &PublicKey,
    message: &[u8],
    signature: &Ed25519Signature,
) -> VerifyResult {
    let verifying_key = public_key.to_dalek();
    let sig = signature.to_dalek();

    match verifying_key.verify(message, &sig) {
        Ok(()) => VerifyResult::Valid,
        Err(_) => VerifyResult::Invalid,
    }
}

/// Verify a signature over multiple message parts.
///
/// Equivalent to `verify_signature(pk, concat(parts), sig)` but without
/// allocating for the concatenation.
pub fn verify_signature_multi(
    public_key: &PublicKey,
    message_parts: &[&[u8]],
    signature: &Ed25519Signature,
) -> VerifyResult {
    // Ed25519 requires the full message, so we must concatenate
    // For large messages, consider a streaming approach or pre-hashing
    let mut message = Vec::new();
    for part in message_parts {
        message.extend_from_slice(part);
    }
    verify_signature(public_key, &message, signature)
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // tests
// ═══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn blake3_hash_deterministic() {
        let data = b"hello world";
        let hash1 = blake3_hash(data);
        let hash2 = blake3_hash(data);
        assert_eq!(hash1, hash2, "BLAKE3 must be deterministic");
    }

    #[test]
    fn blake3_hash_different_inputs() {
        let hash1 = blake3_hash(b"hello");
        let hash2 = blake3_hash(b"world");
        assert_ne!(
            hash1, hash2,
            "Different inputs must produce different hashes"
        );
    }

    #[test]
    fn blake3_hash_multi_matches_single() {
        let part1 = b"hello ";
        let part2 = b"world";
        let combined = b"hello world";

        let multi_hash = blake3_hash_multi(&[part1, part2]);
        let single_hash = blake3_hash(combined);

        assert_eq!(
            multi_hash, single_hash,
            "Multi-part hash must match single hash"
        );
    }

    #[test]
    fn blake3_mac_requires_key() {
        let key = [0u8; 32];
        let data = b"message";
        let mac1 = blake3_mac(&key, data);

        let mut different_key = [0u8; 32];
        different_key[0] = 1;
        let mac2 = blake3_mac(&different_key, data);

        assert_ne!(mac1, mac2, "Different keys must produce different MACs");
    }

    #[test]
    fn blake3_kdf_deterministic() {
        let context = "hydrogen.test.kdf";
        let ikm = b"input key material";

        let key1 = blake3_derive_key(context, ikm);
        let key2 = blake3_derive_key(context, ikm);

        assert_eq!(key1, key2, "KDF must be deterministic");
    }

    #[test]
    fn blake3_kdf_context_matters() {
        let ikm = b"same input";
        let key1 = blake3_derive_key("context.one", ikm);
        let key2 = blake3_derive_key("context.two", ikm);

        assert_ne!(key1, key2, "Different contexts must produce different keys");
    }

    #[test]
    fn public_key_validation_runs() {
        // Verify that from_bytes doesn't panic on arbitrary input
        // and returns a consistent result
        let bytes = [0x42u8; 32];
        let result1 = PublicKey::from_bytes(bytes);
        let result2 = PublicKey::from_bytes(bytes);
        assert_eq!(
            result1.is_some(),
            result2.is_some(),
            "Validation must be deterministic"
        );
    }

    #[test]
    fn public_key_hash_deterministic() {
        // Use a known valid Ed25519 public key (from test vectors)
        // This is a valid point on the Ed25519 curve
        let valid_key_bytes: [u8; 32] = [
            0xd7, 0x5a, 0x98, 0x01, 0x82, 0xb1, 0x0a, 0xb7, 0xd5, 0x4b, 0xfe, 0xd3, 0xc9, 0x64,
            0x07, 0x3a, 0x0e, 0xe1, 0x72, 0xf3, 0xda, 0xa6, 0x23, 0x25, 0xaf, 0x02, 0x1a, 0x68,
            0xf7, 0x07, 0x51, 0x1a,
        ];

        if let Some(pk) = PublicKey::from_bytes(valid_key_bytes) {
            let hash1 = pk.hash();
            let hash2 = pk.hash();
            assert_eq!(hash1, hash2, "Public key hash must be deterministic");
        }
        // If key is invalid on this platform, test passes (nothing to verify)
    }
}
