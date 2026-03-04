//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                                // hydrogen // focus_trap // wasm
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! Focus trap utilities for modal dialogs.
//!
//! Replaces: DEPRECATED_JS_REFERENCE/Hydrogen_UI_FocusTrap.js
//!
//! # Architecture
//!
//! Query functions only. PureScript handles:
//! - Focus scope lifecycle
//! - Tab key event handling
//! - Focus restoration

use wasm_bindgen::prelude::*;
use wasm_bindgen::JsCast;
use web_sys::{window, HtmlElement, Node};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // query functions
// ═══════════════════════════════════════════════════════════════════════════════

/// Check if an element is visible (not display:none, visibility:hidden, or hidden attr).
#[wasm_bindgen]
pub fn focus_trap_is_visible(element: &HtmlElement) -> bool {
    let Some(win) = window() else {
        return false;
    };

    let Ok(Some(style)) = win.get_computed_style(element) else {
        return false;
    };

    if let Ok(display) = style.get_property_value("display") {
        if display == "none" {
            return false;
        }
    }

    if let Ok(visibility) = style.get_property_value("visibility") {
        if visibility == "hidden" {
            return false;
        }
    }

    if element.hidden() {
        return false;
    }

    let rect = element.get_bounding_client_rect();
    rect.width() > 0.0 || rect.height() > 0.0
}

/// Convert a Node to HtmlElement if it is one.
/// Returns None if the node is not an HtmlElement.
#[wasm_bindgen]
pub fn focus_trap_node_to_element(node: &Node) -> Option<HtmlElement> {
    if node.node_type() != 1 {
        return None;
    }
    node.dyn_ref::<HtmlElement>().cloned()
}

/// Referential equality check for DOM nodes.
#[wasm_bindgen]
pub fn focus_trap_ref_eq(a: &JsValue, b: &JsValue) -> bool {
    a == b
}
