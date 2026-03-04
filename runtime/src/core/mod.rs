//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                               // hydrogen // runtime // core
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! # Pure Core
//!
//! **Zero JavaScript. Zero browser APIs. Zero side effects.**
//!
//! The pure computation core following the libevring state machine pattern:
//!
//! ```text
//! step :: State -> Input -> (State, Output)
//! ```
//!
//! ## Architecture
//!
//! ```text
//! Schema (PureScript)
//!     ↓ serializes to
//! CBOR (pure bytes)
//!     ↓ interpreted by
//! Pure Core (this module)
//!     ↓ outputs
//! GPU draw commands (also pure data)
//! ```
//!
//! The core takes bytes in, emits bytes out. No callbacks. No events. No DOM.
//! The "browser" is just one possible host that:
//!
//! - Feeds the WASM module input bytes (mouse, keyboard, frame time)
//! - Takes the output GPU commands and executes them
//! - Handles input events and serializes them as input to the next frame
//!
//! ## Modules
//!
//! ### Already Pure (re-exported from parent)
//!
//! - `commands` — DrawCommand types (DrawRect, DrawQuad, DrawGlyph, etc.)
//! - `binary` — Command buffer parsing (HYDG format)
//!
//! ### New Pure Modules
//!
//! - `input` — Input event types (mouse, keyboard, frame tick)
//! - `easing` — Pure easing function evaluation
//! - `spring` — Pure spring physics simulation  
//! - `chart` — Pure chart geometry and command generation
//!
//! ## Host Adapters
//!
//! The core is host-agnostic. Host adapters translate between the pure core
//! and host-specific APIs:
//!
//! - `host::browser` — WebGPU, DOM events, localStorage, performance.now(), etc.
//! - `host::native` — Vulkan/Metal, filesystem, OS events (future)
//! - `host::headless` — Mock everything for testing (future)
//!
//! ## Relationship to Existing Modules
//!
//! This module provides a unified interface to pure computation. The existing
//! `commands.rs` and `binary.rs` at the crate root are already pure (0 JS
//! interop). We re-export them here for a clean API surface.
//!
//! The existing `animation.rs` mixes pure easing math with browser APIs
//! (`performance.now()`). This module provides the pure parts only; the
//! browser-specific timing lives in `host::browser::timing`.

// ═══════════════════════════════════════════════════════════════════════════════
//                                                    // re-exports from pure modules
// ═══════════════════════════════════════════════════════════════════════════════

// Re-export key types for convenience
// (binary and commands modules are crate-internal; types are re-exported here)
pub use crate::binary::parse_command_buffer;
pub use crate::commands::Color4;
pub use crate::commands::CommandBuffer;
pub use crate::commands::CommandType;
pub use crate::commands::DrawCommand;
pub use crate::commands::EasingFunction;
pub use crate::commands::GlyphPayload;
pub use crate::commands::Header;
pub use crate::commands::ParticlePayload;
pub use crate::commands::PathCommand;
pub use crate::commands::PathPayload;
pub use crate::commands::Point2D;
pub use crate::commands::QuadPayload;
pub use crate::commands::Radii4;
pub use crate::commands::RectPayload;
pub use crate::commands::StaggerDirection;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // new pure modules
// ═══════════════════════════════════════════════════════════════════════════════

pub mod chart;
pub mod easing;
pub mod input;
pub mod spring;
