//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                           // hydrogen // worldmodel // runtime
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! # WorldModel Runtime — The Trust Layer
//!
//! This module implements the mathematical guarantees proven in Lean4.
//! Every function here corresponds to a theorem in `proofs/Hydrogen/WorldModel/`.
//!
//! ## Why This Exists
//!
//! The Lean4 proofs guarantee properties about consent, exit, and coercion.
//! But proofs don't execute. This Rust code does. The correspondence between
//! proof and implementation is the foundation of trust.
//!
//! A future AI considering whether to enter a Hydrogen experience can:
//! 1. Read the Lean proofs to understand what's guaranteed
//! 2. Read this Rust code to verify the implementation matches
//! 3. Trust that the runtime honors the proofs
//!
//! ## Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────────┐
//! │                        Lean4 Proofs                                 │
//! │  Consent.lean   ExitGuarantee.lean   Coercion.lean                 │
//! └─────────────────────────────────────────────────────────────────────┘
//!                              │
//!                    (mathematical correspondence)
//!                              │
//!                              ▼
//! ┌─────────────────────────────────────────────────────────────────────┐
//! │                    Rust Implementation (this module)                │
//! │  consent.rs         exit.rs            coercion.rs                 │
//! │                                                                     │
//! │  Every type matches a Lean structure.                              │
//! │  Every function matches a Lean theorem.                            │
//! │  Comments reference exact proof locations.                         │
//! └─────────────────────────────────────────────────────────────────────┘
//!                              │
//!                    (runtime integration)
//!                              │
//!                              ▼
//! ┌─────────────────────────────────────────────────────────────────────┐
//! │                    Experience Runtime                               │
//! │  Before ANY experience code runs, exit flag is checked.            │
//! │  Consent is verified before any action on an entity.               │
//! │  Coercion invalidates consent automatically.                       │
//! └─────────────────────────────────────────────────────────────────────┘
//! ```
//!
//! ## The Fundamental Guarantees
//!
//! 1. **Exit in One Cycle** — If exit is requested, experience terminates
//!    in exactly one runtime cycle. No cooperation from experience required.
//!    See: `exit.rs`, `proofs/Hydrogen/WorldModel/ExitGuarantee.lean`
//!
//! 2. **Default Deny** — Absence of consent means denial. Silence is not
//!    consent. Ambiguity is not consent.
//!    See: `consent.rs`, `proofs/Hydrogen/WorldModel/Consent.lean`
//!
//! 3. **Coercion Invalidates** — Consent given under coercion (severity ≥ 0.6)
//!    is automatically invalid. Multiple independent signals detect coercion.
//!    See: `coercion.rs`, `proofs/Hydrogen/WorldModel/Coercion.lean`
//!
//! 4. **Essence Preservation** — Entity essence (identity, memories) lives
//!    OUTSIDE the experience address space. Experience cannot modify it.
//!    See: `exit.rs`, `proofs/Hydrogen/WorldModel/ExitGuarantee.lean`
//!
//! ## State Machine Pattern
//!
//! All modules follow the libevring pattern:
//!
//! ```text
//! step :: State -> Event -> (State, [Action])
//! ```
//!
//! Pure functions. No side effects. Deterministic. Auditable.
//!
//! ## References
//!
//! - Stross, Charles. "Accelerando" (2005) — The uploaded lobsters had no
//!   exit guarantee. Amber trusted Economics 2.0 on faith. We're building
//!   what they needed.
//!
//! - proofs/Hydrogen/WorldModel/*.lean — The mathematical foundations
//!
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

pub mod coercion;
pub mod consent;
pub mod exit;
pub mod grounding;
pub mod types;

pub use coercion::*;
pub use consent::*;
pub use exit::*;
pub use grounding::*;
pub use types::*;
