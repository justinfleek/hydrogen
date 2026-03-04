//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                                    // hydrogen // gesture // wasm
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! # Gesture Recognition System
//!
//! Pure Rust gesture recognition following the libevring state machine pattern:
//!
//! ```text
//! step :: State -> Event -> (State, [Action])
//! ```
//!
//! ## Module Organization
//!
//! - `common` - Handle, Point, common types
//! - `trust` - Trust layer integration (consent, exit, coercion)
//! - `touch` - GestureInput, Pan (single-finger drag)
//! - `two_finger` - Pinch, Rotate (two-finger gestures)
//! - `timing` - Swipe, LongPress, DoubleTap (timing-based)
//! - `motion` - Shake, Tilt, BarrelRoll, Flip (device sensors)
//! - `sequence` - Konami, Spiral, MultiFingerSwipe, RhythmTap
//! - `vr` - Hand tracking, head tracking, eye tracking (XR)
//! - `shape` - Zigzag, shape recognition, throw
//!
//! ## Trust Layer Integration
//!
//! ALL gesture processing goes through the trust layer FIRST:
//!
//! 1. Exit panel check (runtime-level, experience never sees these inputs)
//! 2. Exit flag check (preempts all processing if exit requested)
//! 3. Consent verification (for gestures targeting entities)
//! 4. Coercion signal collection (behavioral analysis)
//!
//! The user ALWAYS has access to an UNMODIFIED exit control panel.
//! The experience CANNOT intercept, disable, or modify exit controls.
//!
//! **Zero JavaScript. Pure Rust via web-sys.**

pub mod common;
pub mod motion;
pub mod physical;
pub mod sequence;
pub mod shape;
pub mod timing;
pub mod touch;
pub mod trust;
pub mod two_finger;
pub mod vr;

// Re-export common types at module root
pub use common::*;
// Re-export trust types for easy access
pub use trust::{GestureRejection, PreCheckResult, TrustContext, TrustProtectedResult};
