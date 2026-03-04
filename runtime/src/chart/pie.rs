//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                          // hydrogen // runtime // chart // pie
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! # Pie Chart
//!
//! SVG pie/donut chart animations and interactions.
//!
//! Replaces: `DEPRECATED_JS_REFERENCE/Hydrogen_Chart_PieChart.js` (358 lines)
//!
//! ## Features
//!
//! - Slice reveal animations (scale, rotate)
//! - Explode slice on click
//! - Hover highlighting
//! - Tooltips
//! - Angle calculation from mouse position
//!
//! ## State Machine
//!
//! ```text
//! PieChartState:
//!   Idle → (MouseEnter slice) → SliceHovered(index)
//!   SliceHovered → (MouseLeave) → Idle
//!   SliceHovered → (Click) → SliceExploded(index)
//!   SliceExploded → (Click same) → Idle
//!   SliceExploded → (Click other) → SliceExploded(new_index)
//!   Idle → (Animate) → Animating
//!   Animating → (AnimationComplete) → Idle
//! ```
//!
//! ## Integration
//!
//! - Uses spring physics for explode animation
//! - Coordinates with PureScript pie chart rendering

use wasm_bindgen::closure::Closure;
use wasm_bindgen::prelude::*;
use wasm_bindgen::JsCast;
use web_sys::{window, Document, Element, HtmlElement, SvgsvgElement};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                             // slice animation
// ═══════════════════════════════════════════════════════════════════════════════

/// Animate pie slices appearing with scale effect.
#[wasm_bindgen]
pub fn pie_animate_slices(container_id: &str, duration_ms: f64) -> Result<(), JsValue> {
    let document = get_document()?;
    let container = get_element_by_id(&document, container_id)?;
    let slices = container.query_selector_all(".pie-slice path")?;

    for i in 0..slices.length() {
        if let Some(node) = slices.get(i) {
            if let Ok(path) = node.dyn_into::<Element>() {
                let style = get_style(&path)?;
                style.set_property("transform-origin", "center")?;
                style.set_property("transform", "scale(0)")?;
                style.set_property("opacity", "0")?;

                let delay = i * 80;
                let transition = format!(
                    "transform {}ms cubic-bezier(0.34, 1.56, 0.64, 1), opacity {}ms ease-out",
                    duration_ms,
                    duration_ms * 0.5
                );

                // Schedule animation start
                let path_clone = path.clone();
                let closure = Closure::once(move || {
                    if let Ok(style) = get_style(&path_clone) {
                        let _ = style.set_property("transition", &transition);
                        let _ = style.set_property("transform", "scale(1)");
                        let _ = style.set_property("opacity", "1");
                    }
                });

                window()
                    .ok_or("No window")?
                    .set_timeout_with_callback_and_timeout_and_arguments_0(
                        closure.as_ref().unchecked_ref(),
                        delay as i32,
                    )?;
                closure.forget();
            }
        }
    }

    Ok(())
}

/// Animate slices with rotation effect.
#[wasm_bindgen]
pub fn pie_animate_rotate(container_id: &str, duration_ms: f64) -> Result<(), JsValue> {
    let document = get_document()?;
    let container = get_element_by_id(&document, container_id)?;

    if let Some(chart_group) = container.query_selector("g")? {
        let style = get_style(&chart_group)?;
        style.set_property("transform-origin", "center")?;
        style.set_property("transform", "rotate(-180deg) scale(0.8)")?;
        style.set_property("opacity", "0")?;

        // Use requestAnimationFrame for smooth start
        let chart_group_clone = chart_group.clone();
        let closure = Closure::once(move || {
            if let Ok(style) = get_style(&chart_group_clone) {
                let transition = format!(
                    "transform {}ms cubic-bezier(0.34, 1.56, 0.64, 1), opacity {}ms ease-out",
                    duration_ms,
                    duration_ms * 0.5
                );
                let _ = style.set_property("transition", &transition);
                let _ = style.set_property("transform", "rotate(0deg) scale(1)");
                let _ = style.set_property("opacity", "1");
            }
        });

        window()
            .ok_or("No window")?
            .request_animation_frame(closure.as_ref().unchecked_ref())?;
        closure.forget();
    }

    Ok(())
}

/// Reset slice animation.
#[wasm_bindgen]
pub fn pie_reset_slices(container_id: &str) -> Result<(), JsValue> {
    let document = get_document()?;
    let container = get_element_by_id(&document, container_id)?;
    let slices = container.query_selector_all(".pie-slice path")?;

    for i in 0..slices.length() {
        if let Some(node) = slices.get(i) {
            if let Ok(path) = node.dyn_into::<Element>() {
                let style = get_style(&path)?;
                style.set_property("transition", "none")?;
                style.set_property("transform", "scale(0)")?;
                style.set_property("opacity", "0")?;
            }
        }
    }

    Ok(())
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // explode effect
// ═══════════════════════════════════════════════════════════════════════════════

/// Explode a slice outward from center.
#[wasm_bindgen]
pub fn pie_explode_slice(container_id: &str, index: u32, distance: f64) -> Result<(), JsValue> {
    let document = get_document()?;
    let container = get_element_by_id(&document, container_id)?;
    let svg = get_svg_element(&container)?;
    let slices = container.query_selector_all(".pie-slice")?;

    let viewbox = svg
        .view_box()
        .base_val()
        .ok_or_else(|| JsValue::from_str("No viewBox on SVG"))?;
    let center_x = viewbox.width() as f64 / 2.0;
    let center_y = viewbox.height() as f64 / 2.0;

    for i in 0..slices.length() {
        if i == index {
            if let Some(slice) = slices.get(i) {
                if let Some(slice_el) = slice.dyn_ref::<Element>() {
                    if let Some(path) = slice_el.query_selector("path")? {
                        // Get slice center from bounding box
                        if let Ok(svg_path) = path.clone().dyn_into::<web_sys::SvgGraphicsElement>()
                        {
                            if let Ok(bbox) = svg_path.get_b_box() {
                                let slice_cx = bbox.x() as f64 + bbox.width() as f64 / 2.0;
                                let slice_cy = bbox.y() as f64 + bbox.height() as f64 / 2.0;

                                // Direction from center to slice center
                                let dx = slice_cx - center_x;
                                let dy = slice_cy - center_y;
                                let length = (dx * dx + dy * dy).sqrt();

                                if length > 0.0 {
                                    let translate_x = (dx / length) * distance;
                                    let translate_y = (dy / length) * distance;

                                    let style = get_style(&path)?;
                                    style.set_property("transition", "transform 200ms ease-out")?;
                                    style.set_property(
                                        "transform",
                                        &format!("translate({}px, {}px)", translate_x, translate_y),
                                    )?;
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    Ok(())
}

/// Reset all exploded slices.
#[wasm_bindgen]
pub fn pie_reset_explode(container_id: &str) -> Result<(), JsValue> {
    let document = get_document()?;
    let container = get_element_by_id(&document, container_id)?;
    let paths = container.query_selector_all(".pie-slice path")?;

    for i in 0..paths.length() {
        if let Some(node) = paths.get(i) {
            if let Ok(path) = node.dyn_into::<Element>() {
                let style = get_style(&path)?;
                style.set_property("transition", "transform 200ms ease-out")?;
                style.set_property("transform", "translate(0, 0)")?;
            }
        }
    }

    Ok(())
}

/// Handle for explode-on-click behavior.
#[wasm_bindgen]
pub struct PieExplodeHandle {
    _closure: Closure<dyn Fn(web_sys::MouseEvent)>,
}

/// Initialize click-to-explode behavior.
#[wasm_bindgen]
pub fn pie_init_explode_on_click(
    container_id: &str,
    distance: f64,
    on_click: js_sys::Function,
) -> Result<PieExplodeHandle, JsValue> {
    let document = get_document()?;
    let container = get_element_by_id(&document, container_id)?;

    let container_id_owned = container_id.to_string();
    let exploded_index = std::cell::RefCell::new(-1i32);

    let closure = Closure::new(move |event: web_sys::MouseEvent| {
        let target = match event.target() {
            Some(t) => t,
            None => return,
        };

        let element = match target.dyn_into::<Element>() {
            Ok(e) => e,
            Err(_) => return,
        };

        let slice = element.closest(".pie-slice").ok().flatten();

        match slice {
            Some(slice_el) => {
                let index = slice_el
                    .get_attribute("data-index")
                    .and_then(|s| s.parse::<i32>().ok())
                    .unwrap_or(-1);

                let mut current = exploded_index.borrow_mut();

                if index == *current {
                    // Click same slice - collapse
                    let _ = pie_reset_explode(&container_id_owned);
                    *current = -1;
                    let _ = on_click.call1(&JsValue::NULL, &JsValue::from(-1));
                } else {
                    // Click new slice - explode it
                    let _ = pie_reset_explode(&container_id_owned);
                    if index >= 0 {
                        let _ = pie_explode_slice(&container_id_owned, index as u32, distance);
                    }
                    *current = index;
                    let _ = on_click.call1(&JsValue::NULL, &JsValue::from(index));
                }
            }
            None => {
                // Click outside - reset all
                let _ = pie_reset_explode(&container_id_owned);
                *exploded_index.borrow_mut() = -1;
                let _ = on_click.call1(&JsValue::NULL, &JsValue::from(-1));
            }
        }
    });

    container.add_event_listener_with_callback("click", closure.as_ref().unchecked_ref())?;

    Ok(PieExplodeHandle { _closure: closure })
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // tooltips
// ═══════════════════════════════════════════════════════════════════════════════

/// Pie slice data for tooltips.
#[wasm_bindgen]
#[derive(Clone)]
pub struct PieSliceData {
    label: String,
    value: f64,
    percentage: f64,
}

#[wasm_bindgen]
impl PieSliceData {
    #[wasm_bindgen(constructor)]
    pub fn new(label: &str, value: f64, percentage: f64) -> Self {
        PieSliceData {
            label: label.to_string(),
            value,
            percentage,
        }
    }
}

/// Handle for tooltip behavior.
#[wasm_bindgen]
pub struct PieTooltipHandle {
    _mousemove_closure: Closure<dyn Fn(web_sys::MouseEvent)>,
    _mouseleave_closure: Closure<dyn Fn(web_sys::Event)>,
}

/// Initialize tooltips for pie chart.
#[wasm_bindgen]
pub fn pie_init_tooltips(
    container_id: &str,
    data: Vec<PieSliceData>,
) -> Result<PieTooltipHandle, JsValue> {
    let document = get_document()?;
    let container = get_element_by_id(&document, container_id)?;

    let container_id_owned = container_id.to_string();
    let data_clone = data.clone();

    let mousemove_closure = Closure::new(move |event: web_sys::MouseEvent| {
        let target = match event.target() {
            Some(t) => t,
            None => return,
        };

        let element = match target.dyn_into::<Element>() {
            Ok(e) => e,
            Err(_) => return,
        };

        let slice = element.closest(".pie-slice").ok().flatten();

        if let Some(slice_el) = slice {
            if let Some(index) = slice_el
                .get_attribute("data-index")
                .and_then(|s| s.parse::<usize>().ok())
            {
                if index < data_clone.len() {
                    let item = &data_clone[index];
                    let content = format!(
                        "<div class=\"font-medium\">{}</div><div class=\"text-muted-foreground\">{} ({:.1}%)</div>",
                        item.label, item.value, item.percentage
                    );
                    let _ = show_pie_tooltip(
                        &container_id_owned,
                        event.client_x() as f64 + 10.0,
                        event.client_y() as f64 + 10.0,
                        &content,
                    );
                }
            }
        } else {
            let _ = hide_pie_tooltip(&container_id_owned);
        }
    });

    let container_id_leave = container_id.to_string();
    let mouseleave_closure = Closure::new(move |_event: web_sys::Event| {
        let _ = hide_pie_tooltip(&container_id_leave);
    });

    container.add_event_listener_with_callback(
        "mousemove",
        mousemove_closure.as_ref().unchecked_ref(),
    )?;
    container.add_event_listener_with_callback(
        "mouseleave",
        mouseleave_closure.as_ref().unchecked_ref(),
    )?;

    Ok(PieTooltipHandle {
        _mousemove_closure: mousemove_closure,
        _mouseleave_closure: mouseleave_closure,
    })
}

fn show_pie_tooltip(container_id: &str, x: f64, y: f64, content: &str) -> Result<(), JsValue> {
    let document = get_document()?;
    let tooltip_id = format!("{}-tooltip", container_id);

    let tooltip = match document.get_element_by_id(&tooltip_id) {
        Some(el) => el,
        None => {
            let el = document.create_element("div")?;
            el.set_id(&tooltip_id);
            el.set_attribute(
                "class",
                "fixed z-50 px-3 py-2 text-sm bg-popover text-popover-foreground rounded-lg shadow-lg border pointer-events-none opacity-0 transition-opacity",
            )?;
            document.body().ok_or("No body")?.append_child(&el)?;
            el
        }
    };

    tooltip.set_inner_html(content);

    if let Ok(html_el) = tooltip.dyn_into::<HtmlElement>() {
        let style = html_el.style();
        style.set_property("left", &format!("{}px", x))?;
        style.set_property("top", &format!("{}px", y))?;
        style.set_property("opacity", "1")?;
    }

    Ok(())
}

fn hide_pie_tooltip(container_id: &str) -> Result<(), JsValue> {
    let document = get_document()?;
    let tooltip_id = format!("{}-tooltip", container_id);

    if let Some(tooltip) = document.get_element_by_id(&tooltip_id) {
        if let Ok(html_el) = tooltip.dyn_into::<HtmlElement>() {
            html_el.style().set_property("opacity", "0")?;
        }
    }

    Ok(())
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // hover effects
// ═══════════════════════════════════════════════════════════════════════════════

/// Highlight a slice on hover.
#[wasm_bindgen]
pub fn pie_highlight_slice(container_id: &str, index: u32) -> Result<(), JsValue> {
    let document = get_document()?;
    let container = get_element_by_id(&document, container_id)?;
    let slices = container.query_selector_all(".pie-slice path")?;

    for i in 0..slices.length() {
        if let Some(node) = slices.get(i) {
            if let Ok(path) = node.dyn_into::<Element>() {
                let style = get_style(&path)?;
                if i == index {
                    style.set_property(
                        "filter",
                        "brightness(1.1) drop-shadow(0 2px 4px rgba(0,0,0,0.2))",
                    )?;
                    style.set_property("transform", "scale(1.02)")?;
                } else {
                    style.set_property("opacity", "0.6")?;
                }
            }
        }
    }

    Ok(())
}

/// Clear all slice highlights.
#[wasm_bindgen]
pub fn pie_clear_highlights(container_id: &str) -> Result<(), JsValue> {
    let document = get_document()?;
    let container = get_element_by_id(&document, container_id)?;
    let slices = container.query_selector_all(".pie-slice path")?;

    for i in 0..slices.length() {
        if let Some(node) = slices.get(i) {
            if let Ok(path) = node.dyn_into::<Element>() {
                let style = get_style(&path)?;
                style.set_property("filter", "")?;
                style.set_property("transform", "")?;
                style.set_property("opacity", "")?;
            }
        }
    }

    Ok(())
}

/// Handle for hover effects.
#[wasm_bindgen]
pub struct PieHoverHandle {
    _mouseenter_closure: Closure<dyn Fn(web_sys::MouseEvent)>,
    _mouseleave_closure: Closure<dyn Fn(web_sys::Event)>,
}

/// Initialize hover effects.
#[wasm_bindgen]
pub fn pie_init_hover_effects(container_id: &str) -> Result<PieHoverHandle, JsValue> {
    let document = get_document()?;
    let container = get_element_by_id(&document, container_id)?;

    let container_id_owned = container_id.to_string();

    let mouseenter_closure = Closure::new(move |event: web_sys::MouseEvent| {
        let target = match event.target() {
            Some(t) => t,
            None => return,
        };

        let element = match target.dyn_into::<Element>() {
            Ok(e) => e,
            Err(_) => return,
        };

        if let Some(slice) = element.closest(".pie-slice").ok().flatten() {
            if let Some(index) = slice
                .get_attribute("data-index")
                .and_then(|s| s.parse::<u32>().ok())
            {
                let _ = pie_highlight_slice(&container_id_owned, index);
            }
        }
    });

    let container_id_leave = container_id.to_string();
    let mouseleave_closure = Closure::new(move |_event: web_sys::Event| {
        let _ = pie_clear_highlights(&container_id_leave);
    });

    // Use capture phase for mouseenter
    let options = web_sys::AddEventListenerOptions::new();
    options.set_capture(true);

    container.add_event_listener_with_callback_and_add_event_listener_options(
        "mouseenter",
        mouseenter_closure.as_ref().unchecked_ref(),
        &options,
    )?;
    container.add_event_listener_with_callback(
        "mouseleave",
        mouseleave_closure.as_ref().unchecked_ref(),
    )?;

    Ok(PieHoverHandle {
        _mouseenter_closure: mouseenter_closure,
        _mouseleave_closure: mouseleave_closure,
    })
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // utilities
// ═══════════════════════════════════════════════════════════════════════════════

/// Calculate slice angle from mouse position (radians).
#[wasm_bindgen]
pub fn pie_get_angle_from_mouse(container_id: &str, mouse_x: f64, mouse_y: f64) -> f64 {
    let document = match get_document() {
        Ok(d) => d,
        Err(_) => return 0.0,
    };

    let container = match get_element_by_id(&document, container_id) {
        Ok(c) => c,
        Err(_) => return 0.0,
    };

    let svg = match get_svg_element(&container) {
        Ok(s) => s,
        Err(_) => return 0.0,
    };

    let rect = svg.get_bounding_client_rect();
    let center_x = rect.left() + rect.width() / 2.0;
    let center_y = rect.top() + rect.height() / 2.0;

    (mouse_y - center_y).atan2(mouse_x - center_x)
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

fn get_style(element: &Element) -> Result<web_sys::CssStyleDeclaration, JsValue> {
    element
        .dyn_ref::<HtmlElement>()
        .map(|el| el.style())
        .or_else(|| {
            element
                .dyn_ref::<web_sys::SvgElement>()
                .map(|el| el.style())
        })
        .ok_or_else(|| JsValue::from_str("Cannot get style"))
}
