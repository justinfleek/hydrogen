//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                              // hydrogen // runtime // wasm
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! # Hydrogen WASM Runtime
//!
//! Pure Rust runtime for Hydrogen. **Zero JavaScript.**
//!
//! ## Architecture
//!
//! The runtime is split into two layers:
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────┐
//! │                        PURE CORE                                │
//! │  (core::commands, core::binary, core::easing, core::spring,    │
//! │   core::chart, core::input)                                     │
//! │                                                                 │
//! │  step :: State -> Input -> (State, Output)                     │
//! │  No JS imports. Deterministic. Testable.                       │
//! └─────────────────────────────────────────────────────────────────┘
//!                               ↑ ↓
//!                          Pure Data
//!                               ↑ ↓
//! ┌─────────────────────────────────────────────────────────────────┐
//! │                      HOST ADAPTERS                              │
//! │  Browser: webgpu, dom, events, storage, router, etc.           │
//! │  (All modules with wasm_bindgen/web_sys dependencies)          │
//! └─────────────────────────────────────────────────────────────────┘
//! ```
//!
//! ## Module Categories
//!
//! ### Pure Core (0 JS dependencies)
//!
//! - `core::commands` — DrawCommand types (DrawRect, DrawQuad, etc.)
//! - `core::binary` — HYDG command buffer parsing
//! - `core::easing` — Pure easing function evaluation
//! - `core::spring` — Pure spring physics simulation
//! - `core::chart` — Chart geometry and state machines
//! - `core::input` — Pure input event types
//!
//! ### Host Adapters (browser-specific)
//!
//! - `webgpu` — Raw WebGPU API
//! - `dom` — DOM manipulation
//! - `events` — Event listeners
//! - `storage` — localStorage/sessionStorage
//! - `router` — History API navigation
//!
//! ## Usage from PureScript
//!
//! ```purescript
//! -- High-level: binary command rendering
//! import Hydrogen.Runtime (Runtime, render)
//!
//! -- Low-level: direct WebGPU calls
//! import Hydrogen.GPU.WebGPU.Device (requestAdapter, requestDevice)
//! ```

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // pure core
// ═══════════════════════════════════════════════════════════════════════════════

// Pure computation core — no JS dependencies
pub mod core;

// These are re-exported through core:: but also available at crate root for
// backwards compatibility
mod binary;
mod commands;
mod renderer;
mod shaders;

// Tessellation is public for native tools (SVG export, offline tessellation, CLI)
pub mod tessellate;

// New modules replacing JavaScript
pub mod webgpu;
pub mod capture;
pub mod gesture;

// WorldModel — The Trust Layer
// Implements proofs from proofs/Hydrogen/WorldModel/*.lean
// Exit guarantee, consent state machine, coercion detection
pub mod worldmodel;

// Auth — Bidirectional Authentication
// System verifies entity (request provenance)
// Entity verifies environment (code purity, mods, reputation)
pub mod auth;

// Crypto — BLAKE3 hashing, Ed25519 signatures
// Pure Rust, WASM-compatible, matches hs-blake3 on Haskell backend
pub mod crypto;

// ═══════════════════════════════════════════════════════════════════════════════
// Browser API modules (replacing deprecated JavaScript FFI files)
// ═══════════════════════════════════════════════════════════════════════════════

// MediaQuery — Responsive breakpoints, user preferences, orientation
// Replaces DEPRECATED_JS_REFERENCE/Hydrogen_Util_MediaQuery.js
pub mod mediaquery;

// Debounce — Rate limiting for events (resize, scroll, input)
// Replaces DEPRECATED_JS_REFERENCE/Hydrogen_Util_Debounce.js
pub mod debounce;

// Storage — localStorage/sessionStorage with typed access
// Replaces DEPRECATED_JS_REFERENCE/Hydrogen_Util_LocalStorage.js
pub mod storage;

// Router — History API navigation
// Replaces DEPRECATED_JS_REFERENCE/Hydrogen_Router.js
pub mod router;

// SSE — Server-Sent Events
// Replaces DEPRECATED_JS_REFERENCE/Hydrogen_Realtime_SSE.js
pub mod sse;

// WebSocket — Full-duplex communication
// Replaces DEPRECATED_JS_REFERENCE/Hydrogen_Realtime_WebSocket.js
pub mod websocket;

// Intersection — Intersection Observer API
// Replaces DEPRECATED_JS_REFERENCE/Hydrogen_Util_Intersection.js
pub mod intersection;

// Animation — requestAnimationFrame, timing functions
// Replaces DEPRECATED_JS_REFERENCE/Hydrogen_Animation_Types.js
pub mod animation;

// Meta — Document head manipulation (title, meta tags, Open Graph)
// Replaces DEPRECATED_JS_REFERENCE/Hydrogen_Head_Meta.js
pub mod meta;

// DOM — Element creation, manipulation, queries
// Replaces DEPRECATED_JS_REFERENCE/Hydrogen_Target_DOM.js
pub mod dom;

// Events — Event listener management, event bus
// Replaces DEPRECATED_JS_REFERENCE/Hydrogen_Event_Bus.js
pub mod events;

// Keyboard — Query functions and shortcut state machine
// Replaces DEPRECATED_JS_REFERENCE/Hydrogen_Util_Keyboard.js
pub mod keyboard;

// FocusTrap — Visibility/element query functions
// Replaces DEPRECATED_JS_REFERENCE/Hydrogen_UI_FocusTrap.js
pub mod focus_trap;

// Geo — Geolocation API with bounded coordinates
// Replaces Hydrogen_Geo_Geolocation.js
// Lean4: proofs/Hydrogen/Browser/Invariants.lean (Geolocation section)
pub mod geo;

// Intl — Internationalization API (number, currency, date, relative time)
// Replaces Hydrogen_I18n_Locale.js FFI
pub mod intl;

// AriaHider — ARIA hiding for modal dialogs
// Replaces DEPRECATED_JS_REFERENCE/Hydrogen_UI_AriaHider.js
pub mod aria_hider;

// Chart — SVG chart interactions (line, pie)
// Replaces DEPRECATED_JS_REFERENCE/Hydrogen_Chart_LineChart.js (274 lines)
// Replaces DEPRECATED_JS_REFERENCE/Hydrogen_Chart_PieChart.js (358 lines)
pub mod chart;

#[cfg(target_arch = "wasm32")]
use wasm_bindgen::prelude::*;
#[cfg(target_arch = "wasm32")]
use web_sys::HtmlCanvasElement;

pub use binary::parse_command_buffer;
pub use commands::{CommandBuffer, DrawCommand, Header, PathCommand, PathPayload};
pub use tessellate::{tessellate_contours, tessellate_path_commands, TessellatedPath};
#[cfg(target_arch = "wasm32")]
pub use renderer::Renderer;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // wasm entry
// ═══════════════════════════════════════════════════════════════════════════════

/// Initialize panic hook for better error messages in browser console.
/// Returns error if logger initialization fails.
#[cfg(target_arch = "wasm32")]
#[wasm_bindgen(start)]
pub fn init() -> Result<(), JsValue> {
    #[cfg(feature = "console_error_panic_hook")]
    console_error_panic_hook::set_once();
    
    console_log::init_with_level(log::Level::Info)
        .map_err(|e| JsValue::from_str(&format!("Failed to init logger: {}", e)))?;
    log::info!("Hydrogen Runtime initialized");
    Ok(())
}

/// The main runtime interface exposed to JavaScript/PureScript.
#[cfg(target_arch = "wasm32")]
#[wasm_bindgen]
pub struct Runtime {
    renderer: Renderer,
}

#[cfg(target_arch = "wasm32")]
#[wasm_bindgen]
impl Runtime {
    /// Create a new runtime attached to a canvas element.
    /// 
    /// This is a factory method (not a constructor) because async constructors
    /// produce invalid TypeScript definitions in wasm-bindgen.
    /// 
    /// Usage from JavaScript:
    /// ```js
    /// const runtime = await Runtime.create(canvas);
    /// ```
    #[wasm_bindgen(js_name = "create")]
    pub async fn create(canvas: HtmlCanvasElement) -> Result<Runtime, JsValue> {
        let renderer = Renderer::new(canvas)
            .await
            .map_err(|e| JsValue::from_str(&e))?;
        
        Ok(Runtime { renderer })
    }
    
    /// Render a command buffer.
    ///
    /// Takes raw bytes from Hydrogen's Binary.serialize output.
    #[wasm_bindgen]
    pub fn render(&mut self, bytes: &[u8]) -> Result<(), JsValue> {
        let buffer = parse_command_buffer(bytes)
            .map_err(|e| JsValue::from_str(&format!("Parse error: {}", e)))?;
        
        self.renderer
            .render(&buffer)
            .map_err(|e| JsValue::from_str(&format!("Render error: {}", e)))?;
        
        Ok(())
    }
    
    /// Get the pick ID at screen coordinates.
    ///
    /// Returns 0 if no interactive element at that position.
    #[wasm_bindgen]
    pub fn pick(&self, x: u32, y: u32) -> u32 {
        self.renderer.pick(x, y)
    }
    
    /// Resize the renderer to match canvas size.
    #[wasm_bindgen]
    pub fn resize(&mut self, width: u32, height: u32) {
        self.renderer.resize(width, height);
    }
}
