# Pillar 13: Attestation

Cryptographic proof of content at a point in time.

## Overview

The Attestation pillar provides cryptographic primitives for proving content
existed at a specific time with deterministic identity. At billion-agent scale,
agents need:

- **Deterministic identity**: Same content → same UUID (always)
- **Tamper detection**: Content hashing via SHA-256, SHA-512, Keccak-256
- **Temporal proof**: Timestamps bound to content hashes
- **Verifiable credentials**: W3C VC 1.1 compliant structures
- **Merkle proofs**: Efficient set membership verification

All implementations are pure PureScript — no FFI, no side effects. Hashes are
reproducible across all platforms and environments.

## Atoms

### Timestamp
**File**: `Timestamp.purs`

UTC timestamp in milliseconds since Unix epoch (1970-01-01T00:00:00Z).

| Property | Value |
|----------|-------|
| Storage | `Number` (IEEE 754 double) |
| Bounds | 0 to 253402300800000 ms (year 10000) |
| Behavior | Clamps |

**Functions**: `timestamp`, `epoch`, `fromSeconds`, `toMillis`, `toSeconds`,
`addMillis`, `addSeconds`, `addMinutes`, `addHours`, `addDays`, `diff`, `toISO8601`

### SHA256Hash
**File**: `SHA256.purs`

256-bit hash represented as eight 32-bit words. Pure implementation of FIPS 180-4.

**Functions**: `sha256`, `sha256Bytes`, `sha256Hex`, `toHex`, `toBytes`

### SHA512Hash
**File**: `SHA512.purs`

512-bit hash using 64-bit arithmetic (represented as pairs of 32-bit ints).

**Functions**: `sha512`, `sha512Bytes`, `sha512Hex`, `toHex`, `toBytes`

### Keccak256Hash
**File**: `Keccak256.purs`

Ethereum's hash function. Sponge construction with 1600-bit state.

**Functions**: `keccak256`, `keccak256Bytes`, `keccak256Hex`, `toHex`, `toBytes`

### UUID5
**File**: `UUID5.purs`, `UUID5/Namespaces.purs`

Deterministic 128-bit identifier derived from namespace + name using SHA-256.
Format: `xxxxxxxx-xxxx-5xxx-yxxx-xxxxxxxxxxxx`

**Core Namespaces**:
- `nsElement` — Hydrogen Element UUIDs
- `nsEvent` — Event UUIDs
- `nsAttestation` — Attestation UUIDs
- `nsContact` — Contact UUIDs

**UI Component Namespaces**:
- `nsButton`, `nsToggle`, `nsTab`, `nsTabPanel`
- `nsAccordionTrigger`, `nsAccordionContent`
- `nsOTPInput`, `nsOTPDigit`

**3D/Scene Namespaces**:
- `nsMesh`, `nsScene`, `nsPosition`, `nsMaterial`, `nsLight`, `nsCamera`

**Motion Graphics Namespaces**:
- `nsLayer`, `nsComposition`, `nsProperty`, `nsEffect`, `nsMask`, `nsKeyframe`

**GPU/Render Namespaces**:
- `nsRenderEffect`, `nsComputeKernel`, `nsFrameState`, `nsAnimationState`
- `nsSpringState`, `nsEffectPass`, `nsBlurKernel`, `nsGlowKernel`, `nsParticleKernel`

**Functions**: `uuid5`, `uuid5Bytes`, `uuid5FromHash`, `fromString`, `toString`, `toHex`, `toBytes`

### ContentHash
**File**: `Attestation.purs`

SHA-256 hash of content being attested. Newtype wrapper for type safety.

### SignerId
**File**: `SignedData.purs`

SHA-256 hash identifying a signer (Ethereum address, public key hash, or DID hash).

**Functions**: `signerId`, `signerIdHex`, `signerIdFromBytes`, `signerIdBytes`

### DIDMethod
**File**: `DID.purs`

Supported Decentralized Identifier methods:
- `MethodKey` — did:key (self-generated cryptographic keys)
- `MethodWeb` — did:web (DNS-based resolution)
- `MethodEthr` — did:ethr (Ethereum addresses)
- `MethodIon` — did:ion (Bitcoin-anchored, Microsoft)
- `MethodPkh` — did:pkh (Public Key Hash)
- `MethodOther String` — Custom methods

### VerificationMethodType
**File**: `DID.purs`

Cryptographic key types for DID verification:
- `Ed25519VerificationKey2020`
- `EcdsaSecp256k1VerificationKey2019`
- `JsonWebKey2020`
- `X25519KeyAgreementKey2020`
- `Bls12381G1Key2020`
- `Bls12381G2Key2020`

### SignatureScheme
**File**: `SignedData.purs`

Signature algorithms:
- `ECDSA_secp256k1` — Ethereum-style
- `ECDSA_secp256r1` — WebAuthn/FIDO2
- `Ed25519` — Modern EdDSA (Solana)
- `RSA_PSS` — RSA with probabilistic padding
- `HMAC_SHA256` — Symmetric (trusted contexts)
- `Unknown` — Future schemes

### ProofType
**File**: `VerifiableCredential.purs`

Cryptographic proof types for W3C VCs:
- `Ed25519Signature2020`
- `EcdsaSecp256k1Signature2019`
- `JsonWebSignature2020`
- `BbsBlsSignature2020`
- `BbsBlsSignatureProof2020`

### CredentialType
**File**: `VerifiableCredential.purs`

Common credential types:
- `VerifiableCredentialType` — Base type
- `IdentityCredential` — KYC
- `UniversityDegreeCredential` — Educational
- `EmploymentCredential` — Employment
- `MembershipCredential` — Organization
- `AgeVerificationCredential` — Age
- `AddressCredential` — Address proof
- `HealthCredential` — Health/vaccination
- `LicenseCredential` — Professional license
- `CustomCredential String` — Custom

### CredentialStatus
**File**: `VerifiableCredential.purs`

Revocation status: `StatusActive`, `StatusRevoked`, `StatusSuspended`, `StatusExpired`

### MerkleNode
**File**: `MerkleTree.purs`

Binary tree node: `Leaf SHA256Hash | Branch SHA256Hash left right | Empty`

### ProofElement
**File**: `MerkleTree.purs`

Merkle proof element: `LeftSibling SHA256Hash | RightSibling SHA256Hash`

## Molecules

### Attestation
**File**: `Attestation.purs`

Cryptographic proof binding content to a point in time.

```purescript
type Attestation =
  { id :: UUID5           -- Deterministic identifier
  , timestamp :: Timestamp
  , contentHash :: ContentHash
  }
```

**Functions**: `attestation`, `attestationFromBytes`, `verify`, `verifyBytes`,
`getId`, `getTimestamp`, `getContentHash`, `getContentHashHex`

### Attested a
**File**: `Attested.purs`

Generic wrapper pairing any content with its attestation.

```purescript
type Attested a =
  { content :: a
  , attestation :: Attestation
  }
```

**Functions**: `attest`, `attestWithSerializer`, `getContent`, `getAttestation`,
`verifyAttested`, `mapContent`

### DID
**File**: `DID.purs`

W3C Decentralized Identifier. Format: `did:method:method-specific-id`

```purescript
type DID =
  { method :: DIDMethod
  , identifier :: String
  }
```

**Functions**: `did`, `didMethod`, `didIdentifier`, `didString`, `parseDID`, `sameDID`

### VerificationMethod
**File**: `DID.purs`

Public key associated with a DID.

```purescript
type VerificationMethod =
  { id :: String
  , methodType :: VerificationMethodType
  , controller :: String
  , publicKeyMultibase :: String
  }
```

### DIDDocument
**File**: `DID.purs`

DID resolution result containing verification methods.

```purescript
type DIDDocument =
  { id :: String
  , controller :: Maybe String
  , verificationMethod :: Array VerificationMethod
  , authentication :: Array String
  , assertionMethod :: Array String
  }
```

### SignedData
**File**: `SignedData.purs`

Content paired with cryptographic signature metadata.

```purescript
type SignedData =
  { contentHash :: SHA256Hash
  , signer :: SignerId
  , signature :: Array Int
  , timestamp :: Timestamp
  , scheme :: SignatureScheme
  }
```

**Functions**: `signedData`, `signedDataFromBytes`, `getContentHash`, `getSigner`,
`getSignature`, `getTimestamp`, `getScheme`, `signatureMessage`, `contentMatches`

### MerkleTree
**File**: `MerkleTree.purs`

Binary hash tree for membership proofs.

```purescript
newtype MerkleTree = MerkleTree
  { root :: MerkleNode
  , leafHashes :: Array SHA256Hash
  }
```

**Functions**: `fromLeaves`, `fromBytesArray`, `singleton`, `empty`, `root`,
`rootHex`, `leaves`, `leafCount`, `depth`, `getLeaf`, `treeSize`, `isPowerOf2`

### MerkleProof
**File**: `MerkleTree.purs`

Array of sibling hashes from leaf to root.

```purescript
type MerkleProof = Array ProofElement
```

**Functions**: `getProof`, `verifyProof`, `verifyProofBytes`

### Proof
**File**: `VerifiableCredential.purs`

Cryptographic proof for W3C credentials.

```purescript
type Proof =
  { proofType :: ProofType
  , created :: String
  , verificationMethod :: String
  , proofPurpose :: String
  , proofValue :: String
  }
```

### CredentialSubject
**File**: `VerifiableCredential.purs`

Who the credential is about.

```purescript
type CredentialSubject =
  { id :: Maybe String
  , claims :: Array { key :: String, value :: String }
  }
```

## Compounds

### VerifiableCredential
**File**: `VerifiableCredential.purs`

W3C VC 1.1 compliant credential.

```purescript
type VerifiableCredential =
  { id :: Maybe String
  , vcType :: Array CredentialType
  , issuer :: String
  , issuanceDate :: String
  , expirationDate :: Maybe String
  , credentialSubject :: CredentialSubject
  , proof :: Proof
  , credentialStatus :: Maybe CredentialStatus
  }
```

**Functions**: `verifiableCredential`, `vcId`, `vcType`, `vcIssuer`,
`vcIssuanceDate`, `vcExpirationDate`, `vcCredentialSubject`, `vcProof`, `vcStatus`

### VerifiablePresentation
**File**: `VerifiableCredential.purs`

Collection of credentials presented together.

```purescript
type VerifiablePresentation =
  { id :: Maybe String
  , holder :: String
  , verifiableCredential :: Array VerifiableCredential
  , proof :: Proof
  }
```

**Functions**: `verifiablePresentation`, `vpId`, `vpHolder`,
`vpVerifiableCredential`, `vpProof`

## Source Files

```
src/Hydrogen/Schema/Attestation/
├── Attestation.purs          (222 lines) — Core attestation type
├── Attested.purs             (148 lines) — Generic attested wrapper
├── DID.purs                  (295 lines) — W3C Decentralized Identifiers
├── Keccak256.purs            (518 lines) — Ethereum hash (pure)
├── MerkleTree.purs           (425 lines) — Binary hash trees
├── SHA256.purs               (497 lines) — FIPS 180-4 (pure)
├── SHA512.purs               (635 lines) — 64-bit hash (pure)
├── SignedData.purs           (277 lines) — Signed payload structure
├── Timestamp.purs            (298 lines) — UTC milliseconds
├── UUID5.purs                (309 lines) — Deterministic UUIDs
├── VerifiableCredential.purs (335 lines) — W3C VC 1.1
└── UUID5/
    └── Namespaces.purs       (326 lines) — Standard namespaces
```

**Total**: 12 files, ~4,285 lines
