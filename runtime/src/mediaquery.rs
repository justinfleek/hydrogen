//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                          // hydrogen // runtime // mediaquery
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! # Media Query API
//!
//! Replaces `Hydrogen_Util_MediaQuery.js` with Rust/WASM implementation.
//!
//! ## State Machine
//!
//! Media queries follow a simple two-state machine:
//!
//! ```text
//! ┌─────────────┐    query matches    ┌─────────────┐
//! │  NotMatched │ ──────────────────► │   Matched   │
//! └─────────────┘                     └─────────────┘
//!        ▲                                   │
//!        └───────── query stops matching ────┘
//! ```
//!
//! ## Integration
//!
//! - No haptics (passive query)
//! - No elevation (viewport-level)
//! - Bounded: breakpoint pixels are bounded integers
//!
//! ─────────────────────────────────────────────────────────────────────────────

use wasm_bindgen::closure::Closure;
use wasm_bindgen::prelude::*;
use wasm_bindgen::JsCast;
use web_sys::{window, MediaQueryList, MediaQueryListEvent};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // core query
// ═══════════════════════════════════════════════════════════════════════════════

/// Check if a media query currently matches.
///
/// Returns `false` if window or matchMedia is unavailable (SSR safety).
#[wasm_bindgen]
pub fn mediaquery_matches(query: &str) -> bool {
    match get_media_query_list(query) {
        Some(mql) => mql.matches(),
        None => false,
    }
}

/// Get a MediaQueryList for a query string.
fn get_media_query_list(query: &str) -> Option<MediaQueryList> {
    window()?.match_media(query).ok()?
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // change listener
// ═══════════════════════════════════════════════════════════════════════════════

/// Handle for a media query change listener. Drop to unsubscribe.
#[wasm_bindgen]
pub struct MediaQueryHandle {
    mql: MediaQueryList,
    closure: Closure<dyn Fn(MediaQueryListEvent)>,
}

impl Drop for MediaQueryHandle {
    fn drop(&mut self) {
        // Remove the event listener when handle is dropped
        if self
            .mql
            .remove_event_listener_with_callback("change", self.closure.as_ref().unchecked_ref())
            .is_err()
        {
            web_sys::console::warn_1(&"Failed to remove media query listener".into());
        }
    }
}

/// Subscribe to media query changes.
///
/// Returns a handle that unsubscribes when dropped.
/// Callback receives `true` when query matches, `false` when it doesn't.
#[wasm_bindgen]
pub fn mediaquery_on_change(
    query: String,
    callback: js_sys::Function,
) -> Result<MediaQueryHandle, JsValue> {
    let mql = get_media_query_list(&query)
        .ok_or_else(|| JsValue::from_str("matchMedia not available"))?;

    let closure = Closure::new(move |event: MediaQueryListEvent| {
        let matches = event.matches();
        if callback
            .call1(&JsValue::NULL, &JsValue::from_bool(matches))
            .is_err()
        {
            web_sys::console::warn_1(&"Media query change callback failed".into());
        }
    });

    mql.add_event_listener_with_callback("change", closure.as_ref().unchecked_ref())
        .map_err(|e| JsValue::from_str(&format!("addEventListener failed: {:?}", e)))?;

    Ok(MediaQueryHandle { mql, closure })
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // breakpoints
// ═══════════════════════════════════════════════════════════════════════════════

/// Standard breakpoint values in pixels (Tailwind conventions).
///
/// Bounded: All values are positive integers within u16 range.
#[wasm_bindgen]
pub struct Breakpoints;

#[wasm_bindgen]
impl Breakpoints {
    /// sm: 640px
    #[wasm_bindgen]
    pub fn sm() -> u16 {
        640
    }

    /// md: 768px
    #[wasm_bindgen]
    pub fn md() -> u16 {
        768
    }

    /// lg: 1024px
    #[wasm_bindgen]
    pub fn lg() -> u16 {
        1024
    }

    /// xl: 1280px
    #[wasm_bindgen]
    pub fn xl() -> u16 {
        1280
    }

    /// 2xl: 1536px
    #[wasm_bindgen]
    pub fn xxl() -> u16 {
        1536
    }
}

/// Breakpoint enumeration matching PureScript `Breakpoint` type.
#[wasm_bindgen]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Breakpoint {
    /// < 768px
    Mobile = 0,
    /// >= 768px and < 1024px
    Tablet = 1,
    /// >= 1024px and < 1280px
    Desktop = 2,
    /// >= 1280px
    LargeDesktop = 3,
}

/// Get the current breakpoint based on viewport width.
#[wasm_bindgen]
pub fn mediaquery_current_breakpoint() -> Breakpoint {
    if mediaquery_matches("(min-width: 1280px)") {
        Breakpoint::LargeDesktop
    } else if mediaquery_matches("(min-width: 1024px)") {
        Breakpoint::Desktop
    } else if mediaquery_matches("(min-width: 768px)") {
        Breakpoint::Tablet
    } else {
        Breakpoint::Mobile
    }
}

/// Check if viewport is mobile (< 768px).
#[wasm_bindgen]
pub fn mediaquery_is_mobile() -> bool {
    !mediaquery_matches("(min-width: 768px)")
}

/// Check if viewport is tablet (>= 768px and < 1024px).
#[wasm_bindgen]
pub fn mediaquery_is_tablet() -> bool {
    mediaquery_matches("(min-width: 768px)") && !mediaquery_matches("(min-width: 1024px)")
}

/// Check if viewport is desktop (>= 1024px).
#[wasm_bindgen]
pub fn mediaquery_is_desktop() -> bool {
    mediaquery_matches("(min-width: 1024px)")
}

/// Check if viewport is large desktop (>= 1280px).
#[wasm_bindgen]
pub fn mediaquery_is_large_desktop() -> bool {
    mediaquery_matches("(min-width: 1280px)")
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // user preferences
// ═══════════════════════════════════════════════════════════════════════════════

/// Check if user prefers dark color scheme.
#[wasm_bindgen]
pub fn mediaquery_prefers_dark() -> bool {
    mediaquery_matches("(prefers-color-scheme: dark)")
}

/// Check if user prefers light color scheme.
#[wasm_bindgen]
pub fn mediaquery_prefers_light() -> bool {
    mediaquery_matches("(prefers-color-scheme: light)")
}

/// Check if user prefers reduced motion.
///
/// Important for accessibility — disable animations when true.
#[wasm_bindgen]
pub fn mediaquery_prefers_reduced_motion() -> bool {
    mediaquery_matches("(prefers-reduced-motion: reduce)")
}

/// Check if user prefers reduced transparency.
#[wasm_bindgen]
pub fn mediaquery_prefers_reduced_transparency() -> bool {
    mediaquery_matches("(prefers-reduced-transparency: reduce)")
}

/// Check if user prefers high contrast.
#[wasm_bindgen]
pub fn mediaquery_prefers_contrast() -> bool {
    mediaquery_matches("(prefers-contrast: more)")
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // orientation
// ═══════════════════════════════════════════════════════════════════════════════

/// Orientation enumeration.
#[wasm_bindgen]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Orientation {
    Portrait = 0,
    Landscape = 1,
}

/// Get current device orientation.
#[wasm_bindgen]
pub fn mediaquery_orientation() -> Orientation {
    if mediaquery_matches("(orientation: portrait)") {
        Orientation::Portrait
    } else {
        Orientation::Landscape
    }
}

/// Check if device is in portrait orientation.
#[wasm_bindgen]
pub fn mediaquery_is_portrait() -> bool {
    mediaquery_matches("(orientation: portrait)")
}

/// Check if device is in landscape orientation.
#[wasm_bindgen]
pub fn mediaquery_is_landscape() -> bool {
    mediaquery_matches("(orientation: landscape)")
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // display features
// ═══════════════════════════════════════════════════════════════════════════════

/// Check if display is high DPI (retina, >= 2x pixel ratio).
#[wasm_bindgen]
pub fn mediaquery_is_high_dpi() -> bool {
    mediaquery_matches("(-webkit-min-device-pixel-ratio: 2), (min-resolution: 192dpi)")
}

/// Check if device supports touch input.
///
/// Uses hover:none + pointer:coarse heuristic.
#[wasm_bindgen]
pub fn mediaquery_is_touch() -> bool {
    mediaquery_matches("(hover: none) and (pointer: coarse)")
}

/// Check if currently in print mode.
#[wasm_bindgen]
pub fn mediaquery_is_print() -> bool {
    mediaquery_matches("print")
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // color scheme listener
// ═══════════════════════════════════════════════════════════════════════════════

/// Subscribe to color scheme changes.
///
/// Callback receives `true` for dark mode, `false` for light mode.
#[wasm_bindgen]
pub fn mediaquery_on_color_scheme_change(
    callback: js_sys::Function,
) -> Result<MediaQueryHandle, JsValue> {
    mediaquery_on_change("(prefers-color-scheme: dark)".to_string(), callback)
}

/// Subscribe to orientation changes.
///
/// Callback receives `true` for portrait, `false` for landscape.
#[wasm_bindgen]
pub fn mediaquery_on_orientation_change(
    callback: js_sys::Function,
) -> Result<MediaQueryHandle, JsValue> {
    mediaquery_on_change("(orientation: portrait)".to_string(), callback)
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // breakpoint listener
// ═══════════════════════════════════════════════════════════════════════════════

/// Handle for breakpoint change listener (multiple underlying listeners).
#[wasm_bindgen]
pub struct BreakpointHandle {
    /// Underlying media query handles (dropped when this is dropped).
    #[allow(dead_code)]
    handles: Vec<MediaQueryHandle>,
}

/// Subscribe to breakpoint changes.
///
/// Callback receives the new Breakpoint value (0-3).
#[wasm_bindgen]
pub fn mediaquery_on_breakpoint_change(
    callback: js_sys::Function,
) -> Result<BreakpointHandle, JsValue> {
    let mut handles = Vec::with_capacity(3);

    // Subscribe to each breakpoint boundary
    let queries = [
        "(min-width: 768px)",
        "(min-width: 1024px)",
        "(min-width: 1280px)",
    ];

    for query in queries {
        let cb = callback.clone();
        let closure = Closure::new(move |_event: MediaQueryListEvent| {
            let bp = mediaquery_current_breakpoint();
            if cb.call1(&JsValue::NULL, &JsValue::from(bp as u8)).is_err() {
                web_sys::console::warn_1(&"Breakpoint change callback failed".into());
            }
        });

        let mql = get_media_query_list(query)
            .ok_or_else(|| JsValue::from_str("matchMedia not available"))?;

        mql.add_event_listener_with_callback("change", closure.as_ref().unchecked_ref())
            .map_err(|e| JsValue::from_str(&format!("addEventListener failed: {:?}", e)))?;

        handles.push(MediaQueryHandle { mql, closure });
    }

    Ok(BreakpointHandle { handles })
}
