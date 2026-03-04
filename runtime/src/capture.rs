//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                            // hydrogen // runtime // capture
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! # DOM State Capture
//!
//! Pure Rust DOM access via web-sys. **Zero JavaScript.**
//!
//! Captures:
//! - Element geometry (bounding rect)
//! - Computed styles (colors, typography, spacing, borders, transforms)
//! - DOM tree structure (parent/child relationships)
//! - Accessibility attributes
//!
//! ## Binary Serialization
//!
//! All captured data serializes to a compact binary format that PureScript
//! deserializes via `Hydrogen.Element.Binary.Decoding`.

use wasm_bindgen::prelude::*;
use web_sys::{window, CssStyleDeclaration, Element, HtmlElement};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                           // captured state
// ═══════════════════════════════════════════════════════════════════════════════

/// Complete visual state of a single DOM element.
///
/// Mirrors `CapturedState` in PureScript.
#[wasm_bindgen]
#[derive(Debug, Clone)]
pub struct CapturedState {
    // Identity
    pub index: i32,
    pub parent_index: i32,

    // Geometry
    pub x: f64,
    pub y: f64,
    pub width: f64,
    pub height: f64,

    // Colors (OKLCH)
    pub bg_l: f64,
    pub bg_c: f64,
    pub bg_h: f64,
    pub bg_a: f64,
    pub fg_l: f64,
    pub fg_c: f64,
    pub fg_h: f64,
    pub fg_a: f64,
    pub border_l: f64,
    pub border_c: f64,
    pub border_h: f64,
    pub border_a: f64,

    // Typography
    pub font_size: f64,
    pub font_weight: i32,
    pub line_height: f64,
    pub letter_spacing: f64,

    // Spacing
    pub margin_top: f64,
    pub margin_right: f64,
    pub margin_bottom: f64,
    pub margin_left: f64,
    pub padding_top: f64,
    pub padding_right: f64,
    pub padding_bottom: f64,
    pub padding_left: f64,

    // Borders
    pub border_top_width: f64,
    pub border_right_width: f64,
    pub border_bottom_width: f64,
    pub border_left_width: f64,
    pub border_radius_tl: f64,
    pub border_radius_tr: f64,
    pub border_radius_br: f64,
    pub border_radius_bl: f64,

    // Elevation
    pub z_index: i32,
    pub opacity: f64,

    // Transform
    pub transform_a: f64,
    pub transform_b: f64,
    pub transform_c: f64,
    pub transform_d: f64,
    pub transform_tx: f64,
    pub transform_ty: f64,

    // Depth
    pub depth: i32,
}

/// Non-Copy fields stored separately
#[wasm_bindgen]
pub struct CapturedStateStrings {
    tag_name: String,
    element_id: String,
    class_name: String,
    font_family: String,
    child_indices: Vec<i32>,
}

#[wasm_bindgen]
impl CapturedStateStrings {
    #[wasm_bindgen(getter)]
    pub fn tag_name(&self) -> String {
        self.tag_name.clone()
    }

    #[wasm_bindgen(getter)]
    pub fn element_id(&self) -> String {
        self.element_id.clone()
    }

    #[wasm_bindgen(getter)]
    pub fn class_name(&self) -> String {
        self.class_name.clone()
    }

    #[wasm_bindgen(getter)]
    pub fn font_family(&self) -> String {
        self.font_family.clone()
    }

    #[wasm_bindgen(getter)]
    pub fn child_indices(&self) -> Vec<i32> {
        self.child_indices.clone()
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                           // capture functions
// ═══════════════════════════════════════════════════════════════════════════════

/// Capture state of all visible elements in the document.
///
/// Returns a flat array of CapturedState with parent/child indices for tree reconstruction.
#[wasm_bindgen]
pub fn capture_all_elements() -> Result<Vec<CapturedState>, JsValue> {
    let window = window().ok_or_else(|| JsValue::from_str("No window"))?;
    let document = window
        .document()
        .ok_or_else(|| JsValue::from_str("No document"))?;

    let mut states = Vec::new();
    let mut element_to_index: std::collections::HashMap<usize, i32> =
        std::collections::HashMap::new();

    // Get all elements
    let all_elements = document
        .query_selector_all("*")
        .map_err(|e| JsValue::from_str(&format!("Query failed: {:?}", e)))?;

    let len = all_elements.length();

    // First pass: assign indices
    for i in 0..len {
        if let Some(node) = all_elements.get(i) {
            if let Ok(el) = node.dyn_into::<Element>() {
                let ptr = &el as *const Element as usize;
                element_to_index.insert(ptr, i as i32);
            }
        }
    }

    // Second pass: capture state
    for i in 0..len {
        if let Some(node) = all_elements.get(i) {
            if let Ok(el) = node.dyn_into::<Element>() {
                if let Some(html_el) = el.dyn_ref::<HtmlElement>() {
                    if is_visible(html_el) {
                        let state = capture_element_state(
                            &el,
                            html_el,
                            i as i32,
                            &element_to_index,
                            &window,
                        )?;
                        states.push(state);
                    }
                }
            }
        }
    }

    Ok(states)
}

/// Capture state of a single element by selector.
#[wasm_bindgen]
pub fn capture_element(selector: &str) -> Result<CapturedState, JsValue> {
    let window = window().ok_or_else(|| JsValue::from_str("No window"))?;
    let document = window
        .document()
        .ok_or_else(|| JsValue::from_str("No document"))?;

    let el = document
        .query_selector(selector)
        .map_err(|e| JsValue::from_str(&format!("Query failed: {:?}", e)))?
        .ok_or_else(|| JsValue::from_str("Element not found"))?;

    let html_el = el
        .dyn_ref::<HtmlElement>()
        .ok_or_else(|| JsValue::from_str("Not an HtmlElement"))?;

    let element_to_index = std::collections::HashMap::new();
    capture_element_state(&el, html_el, 0, &element_to_index, &window)
}

/// Capture the string fields for an element (called separately to avoid Copy issues)
#[wasm_bindgen]
pub fn capture_element_strings(selector: &str) -> Result<CapturedStateStrings, JsValue> {
    let window = window().ok_or_else(|| JsValue::from_str("No window"))?;
    let document = window
        .document()
        .ok_or_else(|| JsValue::from_str("No document"))?;

    let el = document
        .query_selector(selector)
        .map_err(|e| JsValue::from_str(&format!("Query failed: {:?}", e)))?
        .ok_or_else(|| JsValue::from_str("Element not found"))?;

    let html_el = el
        .dyn_ref::<HtmlElement>()
        .ok_or_else(|| JsValue::from_str("Not an HtmlElement"))?;

    let style = window
        .get_computed_style(html_el)
        .map_err(|e| JsValue::from_str(&format!("Style failed: {:?}", e)))?
        .ok_or_else(|| JsValue::from_str("No computed style"))?;

    Ok(CapturedStateStrings {
        tag_name: el.tag_name(),
        element_id: el.id(),
        class_name: el.class_name(),
        font_family: get_style_string(&style, "font-family"),
        child_indices: Vec::new(), // Computed during tree building
    })
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                           // internal helpers
// ═══════════════════════════════════════════════════════════════════════════════

fn capture_element_state(
    el: &Element,
    html_el: &HtmlElement,
    index: i32,
    element_to_index: &std::collections::HashMap<usize, i32>,
    window: &web_sys::Window,
) -> Result<CapturedState, JsValue> {
    // Get computed style
    let style = window
        .get_computed_style(html_el)
        .map_err(|e| JsValue::from_str(&format!("Style failed: {:?}", e)))?
        .ok_or_else(|| JsValue::from_str("No computed style"))?;

    // Get bounding rect
    let rect = el.get_bounding_client_rect();

    // Get parent index
    let parent_index = if let Some(parent) = el.parent_element() {
        let ptr = &parent as *const Element as usize;
        *element_to_index.get(&ptr).unwrap_or(&-1)
    } else {
        -1
    };

    // Parse colors to OKLCH (simplified - actual conversion would use proper color math)
    let (bg_l, bg_c, bg_h, bg_a) =
        parse_color_to_oklch(&get_style_string(&style, "background-color"));
    let (fg_l, fg_c, fg_h, fg_a) = parse_color_to_oklch(&get_style_string(&style, "color"));
    let (border_l, border_c, border_h, border_a) =
        parse_color_to_oklch(&get_style_string(&style, "border-color"));

    // Parse transform matrix
    let (a, b, c, d, tx, ty) = parse_transform(&get_style_string(&style, "transform"));

    Ok(CapturedState {
        index,
        parent_index,

        x: rect.x(),
        y: rect.y(),
        width: rect.width(),
        height: rect.height(),

        bg_l,
        bg_c,
        bg_h,
        bg_a,
        fg_l,
        fg_c,
        fg_h,
        fg_a,
        border_l,
        border_c,
        border_h,
        border_a,

        font_size: parse_px(&get_style_string(&style, "font-size")),
        font_weight: parse_font_weight(&get_style_string(&style, "font-weight")),
        line_height: parse_px(&get_style_string(&style, "line-height")),
        letter_spacing: parse_px(&get_style_string(&style, "letter-spacing")),

        margin_top: parse_px(&get_style_string(&style, "margin-top")),
        margin_right: parse_px(&get_style_string(&style, "margin-right")),
        margin_bottom: parse_px(&get_style_string(&style, "margin-bottom")),
        margin_left: parse_px(&get_style_string(&style, "margin-left")),
        padding_top: parse_px(&get_style_string(&style, "padding-top")),
        padding_right: parse_px(&get_style_string(&style, "padding-right")),
        padding_bottom: parse_px(&get_style_string(&style, "padding-bottom")),
        padding_left: parse_px(&get_style_string(&style, "padding-left")),

        border_top_width: parse_px(&get_style_string(&style, "border-top-width")),
        border_right_width: parse_px(&get_style_string(&style, "border-right-width")),
        border_bottom_width: parse_px(&get_style_string(&style, "border-bottom-width")),
        border_left_width: parse_px(&get_style_string(&style, "border-left-width")),
        border_radius_tl: parse_px(&get_style_string(&style, "border-top-left-radius")),
        border_radius_tr: parse_px(&get_style_string(&style, "border-top-right-radius")),
        border_radius_br: parse_px(&get_style_string(&style, "border-bottom-right-radius")),
        border_radius_bl: parse_px(&get_style_string(&style, "border-bottom-left-radius")),

        z_index: parse_z_index(&get_style_string(&style, "z-index")),
        opacity: get_style_string(&style, "opacity").parse().unwrap_or(1.0),

        transform_a: a,
        transform_b: b,
        transform_c: c,
        transform_d: d,
        transform_tx: tx,
        transform_ty: ty,

        depth: compute_depth(el),
    })
}

fn is_visible(el: &HtmlElement) -> bool {
    el.offset_width() > 0 || el.offset_height() > 0
}

fn get_style_string(style: &CssStyleDeclaration, property: &str) -> String {
    style.get_property_value(property).unwrap_or_default()
}

fn parse_px(value: &str) -> f64 {
    value.trim_end_matches("px").parse().unwrap_or(0.0)
}

fn parse_font_weight(value: &str) -> i32 {
    match value {
        "normal" => 400,
        "bold" => 700,
        _ => value.parse().unwrap_or(400),
    }
}

fn parse_z_index(value: &str) -> i32 {
    match value {
        "auto" => 0,
        _ => value.parse().unwrap_or(0),
    }
}

fn compute_depth(el: &Element) -> i32 {
    let mut depth = 0;
    let mut current = el.parent_element();
    while let Some(parent) = current {
        depth += 1;
        current = parent.parent_element();
    }
    depth
}

/// Parse CSS color to OKLCH (l, c, h, a)
///
/// This is a simplified implementation. Full color conversion requires
/// proper sRGB → OKLCH math which should be in a dedicated color module.
fn parse_color_to_oklch(color_str: &str) -> (f64, f64, f64, f64) {
    // Default: transparent black
    if color_str.is_empty() || color_str == "transparent" {
        return (0.0, 0.0, 0.0, 0.0);
    }

    // Parse rgba(r, g, b, a) or rgb(r, g, b)
    if color_str.starts_with("rgba(") || color_str.starts_with("rgb(") {
        let inner = color_str
            .trim_start_matches("rgba(")
            .trim_start_matches("rgb(")
            .trim_end_matches(')');
        let parts: Vec<&str> = inner.split(',').collect();

        if parts.len() >= 3 {
            let r: f64 = parts[0].trim().parse().unwrap_or(0.0) / 255.0;
            let g: f64 = parts[1].trim().parse().unwrap_or(0.0) / 255.0;
            let b: f64 = parts[2].trim().parse().unwrap_or(0.0) / 255.0;
            let a: f64 = if parts.len() >= 4 {
                parts[3].trim().parse().unwrap_or(1.0)
            } else {
                1.0
            };

            // Simplified sRGB to OKLCH (approximate)
            // Real implementation would use proper color science
            let l = 0.2126 * r + 0.7152 * g + 0.0722 * b;
            let c = ((r - g).powi(2) + (g - b).powi(2) + (b - r).powi(2)).sqrt() * 0.5;
            let h = (g - b).atan2(r - (g + b) / 2.0).to_degrees();
            let h = if h < 0.0 { h + 360.0 } else { h };

            return (l, c, h, a);
        }
    }

    // Fallback: opaque black
    (0.0, 0.0, 0.0, 1.0)
}

/// Parse CSS transform matrix
fn parse_transform(transform_str: &str) -> (f64, f64, f64, f64, f64, f64) {
    // Identity matrix
    if transform_str == "none" || transform_str.is_empty() {
        return (1.0, 0.0, 0.0, 1.0, 0.0, 0.0);
    }

    // Parse matrix(a, b, c, d, tx, ty)
    if transform_str.starts_with("matrix(") {
        let inner = transform_str
            .trim_start_matches("matrix(")
            .trim_end_matches(')');
        let parts: Vec<f64> = inner
            .split(',')
            .filter_map(|s| s.trim().parse().ok())
            .collect();

        if parts.len() >= 6 {
            return (parts[0], parts[1], parts[2], parts[3], parts[4], parts[5]);
        }
    }

    // Fallback: identity
    (1.0, 0.0, 0.0, 1.0, 0.0, 0.0)
}
