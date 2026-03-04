//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                         // hydrogen // runtime // chart // line
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! # Line Chart
//!
//! SVG line chart animations and interactions.
//!
//! Replaces: `DEPRECATED_JS_REFERENCE/Hydrogen_Chart_LineChart.js` (274 lines)
//!
//! ## Features
//!
//! - Path drawing animation (stroke-dasharray/dashoffset)
//! - Crosshair following mouse
//! - Tooltip display
//! - Dot highlighting
//! - Path length/point queries
//!
//! ## State Machine
//!
//! ```text
//! LineChartState:
//!   Idle → (MouseEnter) → Hovering
//!   Hovering → (MouseMove) → Hovering [update crosshair]
//!   Hovering → (MouseLeave) → Idle
//!   Idle → (Animate) → Animating
//!   Animating → (AnimationTick) → Animating | Idle
//! ```
//!
//! ## Integration
//!
//! - Uses `crate::animation::Easing::EaseOutCubic` for line draw
//! - Coordinates with PureScript chart rendering

use super::common::{ChartPadding, TooltipPosition};
use wasm_bindgen::closure::Closure;
use wasm_bindgen::prelude::*;
use wasm_bindgen::JsCast;
use web_sys::{window, Document, Element, HtmlElement, SvgPathElement, SvgsvgElement};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // line animation
// ═══════════════════════════════════════════════════════════════════════════════

/// Animate line drawing from start to end using stroke-dasharray.
///
/// # Arguments
/// * `container_id` - Container element ID
/// * `duration_ms` - Animation duration in milliseconds
/// * `easing` - Easing function (uses CSS transition)
#[wasm_bindgen]
pub fn line_animate(container_id: &str, duration_ms: f64) -> Result<(), JsValue> {
    let document = get_document()?;
    let container = get_element_by_id(&document, container_id)?;
    let paths = container.query_selector_all("path[data-animate='true']")?;

    for i in 0..paths.length() {
        if let Some(node) = paths.get(i) {
            if let Ok(path) = node.dyn_into::<SvgPathElement>() {
                let length = path.get_total_length();

                // Set initial state
                let style = path.style();
                style.set_property("stroke-dasharray", &length.to_string())?;
                style.set_property("stroke-dashoffset", &length.to_string())?;

                // Set transition
                let transition = format!("stroke-dashoffset {}ms ease-out", duration_ms);
                style.set_property("transition", &transition)?;

                // Force reflow by reading a layout property
                let _ = path.get_bounding_client_rect();

                // Trigger animation
                style.set_property("stroke-dashoffset", "0")?;
            }
        }
    }

    Ok(())
}

/// Reset line animation to initial state.
#[wasm_bindgen]
pub fn line_reset(container_id: &str) -> Result<(), JsValue> {
    let document = get_document()?;
    let container = get_element_by_id(&document, container_id)?;
    let paths = container.query_selector_all("path[data-animate='true']")?;

    for i in 0..paths.length() {
        if let Some(node) = paths.get(i) {
            if let Ok(path) = node.dyn_into::<SvgPathElement>() {
                let length = path.get_total_length();
                let style = path.style();
                style.set_property("transition", "none")?;
                style.set_property("stroke-dasharray", &length.to_string())?;
                style.set_property("stroke-dashoffset", &length.to_string())?;
            }
        }
    }

    Ok(())
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // crosshair
// ═══════════════════════════════════════════════════════════════════════════════

/// Handle for crosshair cleanup. Drop to remove event listeners.
#[wasm_bindgen]
pub struct LineCrosshairHandle {
    container_id: String,
    v_line: Element,
    h_line: Element,
    _mousemove_closure: Closure<dyn Fn(web_sys::MouseEvent)>,
    _mouseleave_closure: Closure<dyn Fn(web_sys::Event)>,
}

#[wasm_bindgen]
impl LineCrosshairHandle {
    /// Get the container ID this crosshair is attached to.
    #[wasm_bindgen(getter)]
    pub fn container_id(&self) -> String {
        self.container_id.clone()
    }

    /// Clean up crosshair resources.
    #[wasm_bindgen]
    pub fn cleanup(&self) -> Result<(), JsValue> {
        // Remove crosshair lines
        if let Some(parent) = self.v_line.parent_element() {
            parent.remove_child(&self.v_line)?;
        }
        if let Some(parent) = self.h_line.parent_element() {
            parent.remove_child(&self.h_line)?;
        }
        // Note: Event listeners are automatically cleaned up when closures are dropped
        // The _mousemove_closure and _mouseleave_closure fields prevent premature drop
        Ok(())
    }
}

/// Initialize crosshair for line chart.
///
/// # Arguments
/// * `container_id` - Container element ID
/// * `padding` - Chart padding
/// * `on_move` - Callback with cursor position
#[wasm_bindgen]
pub fn line_init_crosshair(
    container_id: &str,
    padding: &ChartPadding,
    on_move: js_sys::Function,
) -> Result<LineCrosshairHandle, JsValue> {
    let document = get_document()?;
    let container = get_element_by_id(&document, container_id)?;
    let svg = get_svg_element(&container)?;

    // Create crosshair lines
    let v_line = create_crosshair_line(&document)?;
    let h_line = create_crosshair_line(&document)?;
    svg.append_child(&v_line)?;
    svg.append_child(&h_line)?;

    // Clone for closures
    let v_line_clone = v_line.clone();
    let h_line_clone = h_line.clone();
    let svg_clone = svg.clone();
    let padding_clone = *padding;
    let on_move_clone = on_move.clone();

    let mousemove_closure = Closure::new(move |event: web_sys::MouseEvent| {
        if let Err(e) = handle_crosshair_move(
            &event,
            &svg_clone,
            &v_line_clone,
            &h_line_clone,
            &padding_clone,
            &on_move_clone,
        ) {
            web_sys::console::warn_1(&format!("Crosshair move error: {:?}", e).into());
        }
    });

    let v_line_leave = v_line.clone();
    let h_line_leave = h_line.clone();
    let on_move_leave = on_move.clone();

    let mouseleave_closure = Closure::new(move |_event: web_sys::Event| {
        hide_element(&v_line_leave);
        hide_element(&h_line_leave);
        let pos = TooltipPosition::hidden();
        let _ = on_move_leave.call1(
            &JsValue::NULL,
            &serde_wasm_bindgen::to_value(&CrosshairCallbackData {
                x: pos.x,
                y: pos.y,
                visible: pos.visible,
            })
            .unwrap_or(JsValue::NULL),
        );
    });

    svg.add_event_listener_with_callback("mousemove", mousemove_closure.as_ref().unchecked_ref())?;
    svg.add_event_listener_with_callback(
        "mouseleave",
        mouseleave_closure.as_ref().unchecked_ref(),
    )?;

    Ok(LineCrosshairHandle {
        container_id: container_id.to_string(),
        v_line,
        h_line,
        _mousemove_closure: mousemove_closure,
        _mouseleave_closure: mouseleave_closure,
    })
}

#[derive(serde::Serialize)]
struct CrosshairCallbackData {
    x: f64,
    y: f64,
    visible: bool,
}

fn handle_crosshair_move(
    event: &web_sys::MouseEvent,
    svg: &SvgsvgElement,
    v_line: &Element,
    h_line: &Element,
    padding: &ChartPadding,
    on_move: &js_sys::Function,
) -> Result<(), JsValue> {
    let rect = svg.get_bounding_client_rect();
    let client_x = event.client_x() as f64;
    let client_y = event.client_y() as f64;

    let local_x = client_x - rect.left();
    let local_y = client_y - rect.top();

    let viewbox = match svg.view_box().base_val() {
        Some(vb) => vb,
        None => return Ok(()),
    };
    let vb_width = viewbox.width() as f64;
    let vb_height = viewbox.height() as f64;

    if rect.width() <= 0.0 || rect.height() <= 0.0 {
        return Ok(());
    }

    let scale_x = vb_width / rect.width();
    let scale_y = vb_height / rect.height();
    let svg_x = local_x * scale_x;
    let svg_y = local_y * scale_y;

    // Check if within data area
    if svg_x >= padding.left
        && svg_x <= vb_width - padding.right
        && svg_y >= padding.top
        && svg_y <= vb_height - padding.bottom
    {
        // Show and position vertical line
        show_element(v_line);
        v_line.set_attribute("x1", &svg_x.to_string())?;
        v_line.set_attribute("y1", &padding.top.to_string())?;
        v_line.set_attribute("x2", &svg_x.to_string())?;
        v_line.set_attribute("y2", &(vb_height - padding.bottom).to_string())?;

        // Show and position horizontal line
        show_element(h_line);
        h_line.set_attribute("x1", &padding.left.to_string())?;
        h_line.set_attribute("y1", &svg_y.to_string())?;
        h_line.set_attribute("x2", &(vb_width - padding.right).to_string())?;
        h_line.set_attribute("y2", &svg_y.to_string())?;

        let _ = on_move.call1(
            &JsValue::NULL,
            &serde_wasm_bindgen::to_value(&CrosshairCallbackData {
                x: svg_x,
                y: svg_y,
                visible: true,
            })?,
        );
    } else {
        hide_element(v_line);
        hide_element(h_line);
        let _ = on_move.call1(
            &JsValue::NULL,
            &serde_wasm_bindgen::to_value(&CrosshairCallbackData {
                x: 0.0,
                y: 0.0,
                visible: false,
            })?,
        );
    }

    Ok(())
}

fn create_crosshair_line(document: &Document) -> Result<Element, JsValue> {
    let line = document.create_element_ns(Some("http://www.w3.org/2000/svg"), "line")?;
    line.set_attribute("stroke", "currentColor")?;
    line.set_attribute("stroke-width", "1")?;
    line.set_attribute("stroke-dasharray", "4,4")?;
    line.set_attribute("class", "text-muted-foreground/50")?;
    hide_element(&line);
    Ok(line)
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // tooltips
// ═══════════════════════════════════════════════════════════════════════════════

/// Show tooltip at position.
#[wasm_bindgen]
pub fn line_show_tooltip(container_id: &str, x: f64, y: f64, content: &str) -> Result<(), JsValue> {
    let document = get_document()?;
    let tooltip_id = format!("{}-tooltip", container_id);

    let tooltip = match document.get_element_by_id(&tooltip_id) {
        Some(el) => el,
        None => {
            let el = document.create_element("div")?;
            el.set_id(&tooltip_id);
            el.set_attribute(
                "class",
                "absolute z-50 px-3 py-2 text-sm bg-popover text-popover-foreground rounded-lg shadow-lg border pointer-events-none",
            )?;
            document
                .body()
                .ok_or("No document body")?
                .append_child(&el)?;
            el
        }
    };

    tooltip.set_inner_html(content);

    if let Ok(html_el) = tooltip.clone().dyn_into::<HtmlElement>() {
        let rect = html_el.get_bounding_client_rect();
        let mut left = x - rect.width() / 2.0;
        let mut top = y - rect.height() - 10.0;

        // Keep in viewport
        if left < 10.0 {
            left = 10.0;
        }
        if top < 10.0 {
            top = y + 10.0;
        }

        let style = html_el.style();
        style.set_property("left", &format!("{}px", left))?;
        style.set_property("top", &format!("{}px", top))?;
        style.set_property("opacity", "1")?;
        style.set_property("visibility", "visible")?;
        style.set_property("transform", "translateY(0)")?;
        style.set_property("transition", "opacity 150ms, transform 150ms")?;
    }

    Ok(())
}

/// Hide tooltip.
#[wasm_bindgen]
pub fn line_hide_tooltip(container_id: &str) -> Result<(), JsValue> {
    let document = get_document()?;
    let tooltip_id = format!("{}-tooltip", container_id);

    if let Some(tooltip) = document.get_element_by_id(&tooltip_id) {
        if let Ok(html_el) = tooltip.dyn_into::<HtmlElement>() {
            let style = html_el.style();
            style.set_property("opacity", "0")?;
            style.set_property("visibility", "hidden")?;
            style.set_property("transform", "translateY(4px)")?;
        }
    }

    Ok(())
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // dot highlight
// ═══════════════════════════════════════════════════════════════════════════════

/// Highlight a data point dot.
#[wasm_bindgen]
pub fn line_highlight_dot(container_id: &str, index: u32) -> Result<(), JsValue> {
    let document = get_document()?;
    let container = get_element_by_id(&document, container_id)?;
    let dots = container.query_selector_all("circle")?;

    for i in 0..dots.length() {
        if i == index {
            if let Some(node) = dots.get(i) {
                if let Ok(circle) = node.dyn_into::<Element>() {
                    if let Some(r_str) = circle.get_attribute("r") {
                        if let Ok(r) = r_str.parse::<f64>() {
                            circle.set_attribute("r", &(r * 1.5).to_string())?;
                        }
                    }
                    let style = circle.dyn_ref::<HtmlElement>().map(|el| el.style());
                    if let Some(style) = style {
                        style.set_property("filter", "drop-shadow(0 0 4px currentColor)")?;
                    }
                }
            }
        }
    }

    Ok(())
}

/// Clear all dot highlights.
#[wasm_bindgen]
pub fn line_clear_dot_highlights(container_id: &str, original_radius: f64) -> Result<(), JsValue> {
    let document = get_document()?;
    let container = get_element_by_id(&document, container_id)?;
    let dots = container.query_selector_all("circle")?;

    for i in 0..dots.length() {
        if let Some(node) = dots.get(i) {
            if let Ok(circle) = node.dyn_into::<Element>() {
                circle.set_attribute("r", &original_radius.to_string())?;
                let style = circle.dyn_ref::<HtmlElement>().map(|el| el.style());
                if let Some(style) = style {
                    style.set_property("filter", "")?;
                }
            }
        }
    }

    Ok(())
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // path utilities
// ═══════════════════════════════════════════════════════════════════════════════

/// Get total length of an SVG path.
#[wasm_bindgen]
pub fn line_get_path_length(path_id: &str) -> f64 {
    let document = match get_document() {
        Ok(d) => d,
        Err(_) => return 0.0,
    };

    document
        .get_element_by_id(path_id)
        .and_then(|el| el.dyn_into::<SvgPathElement>().ok())
        .map(|path| path.get_total_length() as f64)
        .unwrap_or(0.0)
}

/// Get point at length along path.
#[wasm_bindgen]
pub fn line_get_point_at_length(path_id: &str, length: f64) -> TooltipPosition {
    let document = match get_document() {
        Ok(d) => d,
        Err(_) => return TooltipPosition::hidden(),
    };

    document
        .get_element_by_id(path_id)
        .and_then(|el| el.dyn_into::<SvgPathElement>().ok())
        .and_then(|path| {
            path.get_point_at_length(length as f32)
                .ok()
                .map(|point| TooltipPosition::new(point.x() as f64, point.y() as f64, true))
        })
        .unwrap_or_else(TooltipPosition::hidden)
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // helpers
// ═══════════════════════════════════════════════════════════════════════════════

fn get_document() -> Result<Document, JsValue> {
    window()
        .ok_or_else(|| JsValue::from_str("No window"))?
        .document()
        .ok_or_else(|| JsValue::from_str("No document"))
}

fn get_element_by_id(document: &Document, id: &str) -> Result<Element, JsValue> {
    document
        .get_element_by_id(id)
        .ok_or_else(|| JsValue::from_str(&format!("Element '{}' not found", id)))
}

fn get_svg_element(container: &Element) -> Result<SvgsvgElement, JsValue> {
    container
        .query_selector("svg")?
        .ok_or_else(|| JsValue::from_str("No SVG element found"))?
        .dyn_into::<SvgsvgElement>()
        .map_err(|_| JsValue::from_str("Element is not an SVG"))
}

fn hide_element(element: &Element) {
    if let Ok(html) = element.clone().dyn_into::<HtmlElement>() {
        let _ = html.style().set_property("display", "none");
    } else {
        let _ = element.set_attribute("style", "display: none");
    }
}

fn show_element(element: &Element) {
    if let Ok(html) = element.clone().dyn_into::<HtmlElement>() {
        let _ = html.style().set_property("display", "");
    } else {
        let _ = element.set_attribute("style", "");
    }
}
