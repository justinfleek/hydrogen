//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                                // hydrogen // aria_hider // wasm
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! ARIA hiding for modal dialogs.
//!
//! Replaces: DEPRECATED_JS_REFERENCE/Hydrogen_UI_AriaHider.js
//!
//! When a modal opens, siblings must be hidden from screen readers
//! via aria-hidden="true". This module provides the DOM manipulation.

use wasm_bindgen::prelude::*;
use web_sys::{Element, HtmlElement};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // hidden state
// ═══════════════════════════════════════════════════════════════════════════════

/// Record of an element's original aria-hidden state.
#[wasm_bindgen]
pub struct HiddenElement {
    element: Element,
    original: Option<String>,
}

/// State tracking all hidden elements for restoration.
#[wasm_bindgen]
pub struct AriaHiderState {
    hidden: Vec<HiddenElement>,
}

#[wasm_bindgen]
impl AriaHiderState {
    /// Number of elements hidden.
    #[wasm_bindgen(getter)]
    pub fn count(&self) -> usize {
        self.hidden.len()
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // hide/restore
// ═══════════════════════════════════════════════════════════════════════════════

/// Hide all siblings of the given element from screen readers.
/// Walks up the DOM tree, hiding siblings at each level.
#[wasm_bindgen]
pub fn aria_hider_hide_others(element: &HtmlElement) -> AriaHiderState {
    let mut hidden = Vec::new();
    let mut current: Option<Element> = Some(element.clone().into());

    while let Some(el) = current {
        if let Some(parent) = el.parent_element() {
            let children = parent.children();
            let len = children.length();

            for i in 0..len {
                if let Some(sibling) = children.item(i) {
                    // Skip self
                    if sibling == el {
                        continue;
                    }

                    // Skip elements that should be ignored
                    if should_ignore(&sibling) {
                        continue;
                    }

                    // Store original and set aria-hidden
                    let original = sibling.get_attribute("aria-hidden");
                    if sibling.set_attribute("aria-hidden", "true").is_ok() {
                        hidden.push(HiddenElement {
                            element: sibling,
                            original,
                        });
                    }
                }
            }

            // Check if we've reached body
            if parent.tag_name().to_lowercase() == "body" {
                break;
            }

            current = Some(parent);
        } else {
            break;
        }
    }

    AriaHiderState { hidden }
}

/// Restore original aria-hidden values for all hidden elements.
#[wasm_bindgen]
pub fn aria_hider_restore_others(state: AriaHiderState) {
    for entry in state.hidden {
        match &entry.original {
            Some(value) => {
                let _ = entry.element.set_attribute("aria-hidden", value);
            }
            None => {
                let _ = entry.element.remove_attribute("aria-hidden");
            }
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // helpers
// ═══════════════════════════════════════════════════════════════════════════════

fn should_ignore(el: &Element) -> bool {
    let tag = el.tag_name().to_lowercase();

    // Skip script, style, template
    if tag == "script" || tag == "style" || tag == "template" {
        return true;
    }

    // Skip portal containers
    if el.has_attribute("data-hydrogen-portal") {
        return true;
    }

    // Skip live regions
    if let Some(live) = el.get_attribute("aria-live") {
        if live == "polite" || live == "assertive" {
            return true;
        }
    }

    // Skip already hidden
    if let Some(hidden) = el.get_attribute("aria-hidden") {
        if hidden == "true" {
            return true;
        }
    }

    false
}
