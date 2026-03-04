//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                                // hydrogen // runtime // dom
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! # DOM Target Operations
//!
//! Pure Rust/WASM DOM manipulation via web-sys. **Zero JavaScript.**
//!
//! This module provides the minimal browser API surface needed to render
//! Hydrogen Elements to DOM. All operations use typed web-sys bindings.
//!
//! ## Architecture
//!
//! ```text
//! Element (pure data) → DomTarget (this module) → Browser DOM
//! ```
//!
//! The interpreter calls these functions to execute Element → DOM.
//! No JavaScript. No reflection. Pure typed web-sys calls.

use wasm_bindgen::prelude::*;
use wasm_bindgen::JsCast;
use web_sys::{Document, Element, HtmlElement, HtmlInputElement, Window};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                           // namespaced attrs
// ═══════════════════════════════════════════════════════════════════════════════

/// Set a namespaced attribute on an element.
/// Used for SVG attributes like xlink:href.
#[wasm_bindgen]
pub fn dom_set_attribute_ns(
    element: &Element,
    namespace: Option<String>,
    name: &str,
    value: &str,
) -> Result<(), JsValue> {
    element
        .set_attribute_ns(namespace.as_deref(), name, value)
        .map_err(|e| JsValue::from_str(&format!("setAttributeNS failed: {:?}", e)))
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                           // document access
// ═══════════════════════════════════════════════════════════════════════════════

/// Get the window object.
fn get_window() -> Result<Window, JsValue> {
    web_sys::window().ok_or_else(|| JsValue::from_str("No window"))
}

/// Get the document object.
fn get_document() -> Result<Document, JsValue> {
    get_window()?
        .document()
        .ok_or_else(|| JsValue::from_str("No document"))
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                           // properties
// ═══════════════════════════════════════════════════════════════════════════════

/// Set the 'value' property on an input element.
/// Uses typed HtmlInputElement API instead of reflection.
#[wasm_bindgen]
pub fn dom_set_input_value(element: &HtmlElement, value: &str) -> Result<(), JsValue> {
    let input: &HtmlInputElement = element
        .dyn_ref()
        .ok_or_else(|| JsValue::from_str("Element is not an input"))?;
    input.set_value(value);
    Ok(())
}

/// Get the 'value' property from an input element.
#[wasm_bindgen]
pub fn dom_get_input_value(element: &HtmlElement) -> Result<String, JsValue> {
    let input: &HtmlInputElement = element
        .dyn_ref()
        .ok_or_else(|| JsValue::from_str("Element is not an input"))?;
    Ok(input.value())
}

/// Set the 'checked' property on an input element.
#[wasm_bindgen]
pub fn dom_set_input_checked(element: &HtmlElement, checked: bool) -> Result<(), JsValue> {
    let input: &HtmlInputElement = element
        .dyn_ref()
        .ok_or_else(|| JsValue::from_str("Element is not an input"))?;
    input.set_checked(checked);
    Ok(())
}

/// Get the 'checked' property from an input element.
#[wasm_bindgen]
pub fn dom_get_input_checked(element: &HtmlElement) -> Result<bool, JsValue> {
    let input: &HtmlInputElement = element
        .dyn_ref()
        .ok_or_else(|| JsValue::from_str("Element is not an input"))?;
    Ok(input.checked())
}

/// Set the 'disabled' property on an input element.
#[wasm_bindgen]
pub fn dom_set_input_disabled(element: &HtmlElement, disabled: bool) -> Result<(), JsValue> {
    let input: &HtmlInputElement = element
        .dyn_ref()
        .ok_or_else(|| JsValue::from_str("Element is not an input"))?;
    input.set_disabled(disabled);
    Ok(())
}

/// Set inner text content (safe — no HTML parsing).
#[wasm_bindgen]
pub fn dom_set_text_content(element: &Element, text: &str) {
    element.set_text_content(Some(text));
}

/// Get inner text content.
#[wasm_bindgen]
pub fn dom_get_text_content(element: &Element) -> Option<String> {
    element.text_content()
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                           // styles
// ═══════════════════════════════════════════════════════════════════════════════

/// Set a CSS style property on an element.
#[wasm_bindgen]
pub fn dom_set_style_property(
    element: &HtmlElement,
    property: &str,
    value: &str,
) -> Result<(), JsValue> {
    element
        .style()
        .set_property(property, value)
        .map_err(|e| JsValue::from_str(&format!("setStyleProperty failed: {:?}", e)))
}

/// Remove a CSS style property from an element.
#[wasm_bindgen]
pub fn dom_remove_style_property(element: &HtmlElement, property: &str) -> Result<(), JsValue> {
    element
        .style()
        .remove_property(property)
        .map(|_| ())
        .map_err(|e| JsValue::from_str(&format!("removeStyleProperty failed: {:?}", e)))
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                           // element creation
// ═══════════════════════════════════════════════════════════════════════════════

/// Create an element with optional namespace.
#[wasm_bindgen]
pub fn dom_create_element(tag_name: &str, namespace: Option<String>) -> Result<Element, JsValue> {
    let document = get_document()?;

    match namespace {
        Some(ns) => document
            .create_element_ns(Some(&ns), tag_name)
            .map_err(|e| JsValue::from_str(&format!("createElementNS failed: {:?}", e))),
        None => document
            .create_element(tag_name)
            .map_err(|e| JsValue::from_str(&format!("createElement failed: {:?}", e))),
    }
}

/// Create a text node.
#[wasm_bindgen]
pub fn dom_create_text_node(text: &str) -> Result<web_sys::Text, JsValue> {
    let document = get_document()?;
    Ok(document.create_text_node(text))
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                           // tree manipulation
// ═══════════════════════════════════════════════════════════════════════════════

/// Append a child node.
#[wasm_bindgen]
pub fn dom_append_child(parent: &Element, child: &web_sys::Node) -> Result<(), JsValue> {
    parent
        .append_child(child)
        .map(|_| ())
        .map_err(|e| JsValue::from_str(&format!("appendChild failed: {:?}", e)))
}

/// Remove a child node.
#[wasm_bindgen]
pub fn dom_remove_child(parent: &Element, child: &web_sys::Node) -> Result<(), JsValue> {
    parent
        .remove_child(child)
        .map(|_| ())
        .map_err(|e| JsValue::from_str(&format!("removeChild failed: {:?}", e)))
}

/// Insert before a reference node.
#[wasm_bindgen]
pub fn dom_insert_before(
    parent: &Element,
    new_node: &web_sys::Node,
    reference_node: Option<web_sys::Node>,
) -> Result<(), JsValue> {
    parent
        .insert_before(new_node, reference_node.as_ref())
        .map(|_| ())
        .map_err(|e| JsValue::from_str(&format!("insertBefore failed: {:?}", e)))
}

/// Replace a child node.
#[wasm_bindgen]
pub fn dom_replace_child(
    parent: &Element,
    new_child: &web_sys::Node,
    old_child: &web_sys::Node,
) -> Result<(), JsValue> {
    parent
        .replace_child(new_child, old_child)
        .map(|_| ())
        .map_err(|e| JsValue::from_str(&format!("replaceChild failed: {:?}", e)))
}

/// Clear all children from an element.
#[wasm_bindgen]
pub fn dom_clear_children(element: &Element) {
    element.set_inner_html("");
}
