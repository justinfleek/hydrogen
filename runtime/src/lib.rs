//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                              // hydrogen // runtime // wasm
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! # Hydrogen WASM Runtime
//!
//! Pure Rust runtime for Hydrogen. **Zero JavaScript.**
//!
//! This crate provides:
//!
//! 1. **High-level rendering** - Binary command buffer → WebGPU rendering
//! 2. **Low-level WebGPU FFI** - Direct WebGPU API for PureScript
//! 3. **Browser APIs** - DOM, events, storage, etc. (replacing all .js files)
//!
//! ## Architecture
//!
//! ```text
//! PureScript (Hydrogen)
//!     ↓
//! ┌───────────────────────────────────────────────────┐
//! │  Rust WASM (this crate)                           │
//! │  ┌─────────────────┐  ┌─────────────────────────┐ │
//! │  │ High-level API  │  │ Low-level WebGPU FFI   │ │
//! │  │ (Runtime)       │  │ (webgpu module)        │ │
//! │  └────────┬────────┘  └───────────┬────────────┘ │
//! │           │                       │              │
//! │           └───────────┬───────────┘              │
//! │                       ↓                          │
//! │               Browser WebGPU                     │
//! └───────────────────────────────────────────────────┘
//! ```
//!
//! ## Modules
//!
//! - `webgpu` - Raw WebGPU API (replaces Device.js)
//! - `dom` - DOM manipulation (replaces DOM.js, Target/DOM.js)
//! - `events` - Event listeners (replaces Input.js, Gesture.js)
//! - `storage` - localStorage/sessionStorage (replaces LocalStorage.js)
//! - `router` - History API (replaces Router.js)
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

mod binary;
mod commands;
mod renderer;
mod shaders;
mod tessellate;

// New modules replacing JavaScript
pub mod webgpu;

#[cfg(target_arch = "wasm32")]
use wasm_bindgen::prelude::*;
#[cfg(target_arch = "wasm32")]
use web_sys::HtmlCanvasElement;

pub use binary::parse_command_buffer;
pub use commands::{CommandBuffer, DrawCommand, Header};
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
