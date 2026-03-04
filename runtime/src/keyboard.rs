//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                                  // hydrogen // keyboard // wasm
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! Keyboard utilities and state machine.
//!
//! Replaces: DEPRECATED_JS_REFERENCE/Hydrogen_Util_Keyboard.js
//!
//! # Architecture
//!
//! - Query functions: Read browser state, return data
//! - State machine: Pure keyboard shortcut/sequence matching
//! - PureScript handles event listener lifecycle
//!
//! # State Machine
//!
//! ```text
//! step :: KeyboardState -> KeyboardInput -> (KeyboardState, [KeyboardAction])
//! ```

use wasm_bindgen::prelude::*;
use wasm_bindgen::JsCast;
use web_sys::{window, Element, HtmlElement};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // query functions
// ═══════════════════════════════════════════════════════════════════════════════

fn get_active_element() -> Option<Element> {
    window()?.document()?.active_element()
}

/// Check if an input element is currently focused.
/// Returns true if focus is on input, textarea, select, or contenteditable.
#[wasm_bindgen]
pub fn keyboard_is_input_focused() -> bool {
    let Some(active) = get_active_element() else {
        return false;
    };

    let tag = active.tag_name().to_lowercase();
    if tag == "input" || tag == "textarea" || tag == "select" {
        return true;
    }

    active
        .dyn_ref::<HtmlElement>()
        .map(|el| el.is_content_editable())
        .unwrap_or(false)
}

/// Detect macOS/iOS platform for Cmd key handling.
#[wasm_bindgen]
pub fn keyboard_is_mac_platform() -> bool {
    window()
        .and_then(|w| w.navigator().platform().ok())
        .map(|p| {
            p.contains("Mac") || p.contains("iPhone") || p.contains("iPad") || p.contains("iPod")
        })
        .unwrap_or(false)
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // input event
// ═══════════════════════════════════════════════════════════════════════════════

/// Keyboard input event (what happened).
/// Serialized from browser KeyboardEvent by PureScript.
#[derive(Clone, Debug)]
pub struct KeyboardInput {
    pub key: String,
    pub code: String,
    pub ctrl: bool,
    pub alt: bool,
    pub shift: bool,
    pub meta: bool,
    pub time_ms: f64,
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                           // shortcut matching
// ═══════════════════════════════════════════════════════════════════════════════

/// Shortcut definition for matching.
#[derive(Clone, Debug)]
pub struct ShortcutDef {
    pub key: String,
    pub ctrl: bool,
    pub alt: bool,
    pub shift: bool,
    pub meta: bool,
}

/// Check if input matches shortcut definition.
pub fn shortcut_matches(input: &KeyboardInput, def: &ShortcutDef, is_mac: bool) -> bool {
    // Normalize key comparison
    let key_lower = input.key.to_lowercase();
    let def_key_lower = def.key.to_lowercase();
    let code_match = input.code.to_lowercase() == format!("key{}", def_key_lower);
    let key_match = key_lower == def_key_lower || code_match;

    if !key_match {
        return false;
    }

    // On Mac, Ctrl+Key should match Cmd+Key for cross-platform shortcuts
    let ctrl_match = def.ctrl == (input.ctrl || (input.meta && !is_mac));
    let alt_match = def.alt == input.alt;
    let shift_match = def.shift == input.shift;
    let meta_match = def.meta == input.meta;

    ctrl_match && alt_match && shift_match && meta_match
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                        // sequence state machine
// ═══════════════════════════════════════════════════════════════════════════════

/// Sequence matcher state.
#[derive(Clone, Debug)]
pub struct SequenceState {
    /// Keys received so far
    pub buffer: Vec<String>,
    /// Timestamp of last key
    pub last_key_time_ms: f64,
}

impl Default for SequenceState {
    fn default() -> Self {
        SequenceState {
            buffer: Vec::new(),
            last_key_time_ms: 0.0,
        }
    }
}

/// Result of sequence step.
#[derive(Clone, Debug)]
pub enum SequenceResult {
    /// No match, continue accumulating
    Continue,
    /// Sequence matched
    Matched,
    /// Buffer cleared (timeout or mismatch)
    Reset,
}

/// Sequence step result with new state.
pub struct SequenceStepResult {
    pub state: SequenceState,
    pub result: SequenceResult,
}

/// Pure sequence state machine step.
///
/// ```text
/// step :: SequenceState -> KeyboardInput -> SequenceConfig -> SequenceStepResult
/// ```
pub fn sequence_step(
    state: SequenceState,
    input: &KeyboardInput,
    target_keys: &[String],
    timeout_ms: f64,
) -> SequenceStepResult {
    // Check timeout
    let time_delta = input.time_ms - state.last_key_time_ms;
    if state.last_key_time_ms > 0.0 && time_delta > timeout_ms {
        // Timeout: reset and start fresh with this key
        let mut new_buffer = Vec::new();
        new_buffer.push(input.key.to_lowercase());
        return SequenceStepResult {
            state: SequenceState {
                buffer: new_buffer,
                last_key_time_ms: input.time_ms,
            },
            result: SequenceResult::Reset,
        };
    }

    // Add key to buffer
    let mut new_buffer = state.buffer.clone();
    new_buffer.push(input.key.to_lowercase());

    // Check for match
    let target_lower: Vec<String> = target_keys.iter().map(|k| k.to_lowercase()).collect();

    if new_buffer.len() == target_lower.len() {
        let matches = new_buffer
            .iter()
            .zip(target_lower.iter())
            .all(|(a, b)| a == b);
        if matches {
            return SequenceStepResult {
                state: SequenceState::default(),
                result: SequenceResult::Matched,
            };
        }
    }

    // Check prefix match
    let is_prefix = new_buffer
        .iter()
        .zip(target_lower.iter())
        .all(|(a, b)| a == b);

    if is_prefix && new_buffer.len() < target_lower.len() {
        // Valid prefix, continue accumulating
        SequenceStepResult {
            state: SequenceState {
                buffer: new_buffer,
                last_key_time_ms: input.time_ms,
            },
            result: SequenceResult::Continue,
        }
    } else {
        // Mismatch, reset
        SequenceStepResult {
            state: SequenceState::default(),
            result: SequenceResult::Reset,
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // wasm exports
// ═══════════════════════════════════════════════════════════════════════════════

/// WASM-exported shortcut match check.
/// Takes flattened parameters for easy FFI.
#[wasm_bindgen]
pub fn keyboard_shortcut_matches(
    input_key: &str,
    input_code: &str,
    input_ctrl: bool,
    input_alt: bool,
    input_shift: bool,
    input_meta: bool,
    def_key: &str,
    def_ctrl: bool,
    def_alt: bool,
    def_shift: bool,
    def_meta: bool,
) -> bool {
    let input = KeyboardInput {
        key: input_key.to_string(),
        code: input_code.to_string(),
        ctrl: input_ctrl,
        alt: input_alt,
        shift: input_shift,
        meta: input_meta,
        time_ms: 0.0,
    };

    let def = ShortcutDef {
        key: def_key.to_string(),
        ctrl: def_ctrl,
        alt: def_alt,
        shift: def_shift,
        meta: def_meta,
    };

    shortcut_matches(&input, &def, keyboard_is_mac_platform())
}
