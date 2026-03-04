//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                        // hydrogen // runtime // intersection
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! Intersection Observer API. Replaces Hydrogen_Util_Intersection.js

use js_sys::Array;
use wasm_bindgen::closure::Closure;
use wasm_bindgen::prelude::*;
use wasm_bindgen::JsCast;
use web_sys::{Element, IntersectionObserver, IntersectionObserverEntry, IntersectionObserverInit};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // entry data
// ═══════════════════════════════════════════════════════════════════════════════

/// Intersection entry data (mirrors the JS structure).
#[wasm_bindgen]
pub struct IntersectionEntry {
    pub is_intersecting: bool,
    pub intersection_ratio: f64,
    pub bounding_top: f64,
    pub bounding_right: f64,
    pub bounding_bottom: f64,
    pub bounding_left: f64,
    pub bounding_width: f64,
    pub bounding_height: f64,
    pub time: f64,
}

impl From<&IntersectionObserverEntry> for IntersectionEntry {
    fn from(entry: &IntersectionObserverEntry) -> Self {
        let rect = entry.bounding_client_rect();
        IntersectionEntry {
            is_intersecting: entry.is_intersecting(),
            intersection_ratio: entry.intersection_ratio(),
            bounding_top: rect.top(),
            bounding_right: rect.right(),
            bounding_bottom: rect.bottom(),
            bounding_left: rect.left(),
            bounding_width: rect.width(),
            bounding_height: rect.height(),
            time: entry.time(),
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // observer
// ═══════════════════════════════════════════════════════════════════════════════

/// Handle for an intersection observer. Drop to disconnect.
#[wasm_bindgen]
pub struct IntersectionHandle {
    observer: IntersectionObserver,
    element: Element,
    _closure: Closure<dyn Fn(Array, IntersectionObserver)>,
}

#[wasm_bindgen]
impl IntersectionHandle {
    /// Disconnect the observer.
    #[wasm_bindgen]
    pub fn disconnect(&self) {
        self.observer.unobserve(&self.element);
        self.observer.disconnect();
    }
}

/// Observe an element for intersection changes.
#[wasm_bindgen]
pub fn intersection_observe(
    element: &Element,
    threshold: f64,
    root_margin: &str,
    callback: js_sys::Function,
) -> Result<IntersectionHandle, JsValue> {
    let element_clone = element.clone();
    let callback_clone = callback.clone();

    let closure = Closure::new(move |entries: Array, _observer: IntersectionObserver| {
        for i in 0..entries.length() {
            if let Some(entry) = entries.get(i).dyn_ref::<IntersectionObserverEntry>() {
                let data = IntersectionEntry::from(entry);
                if callback_clone
                    .call1(&JsValue::NULL, &entry_to_js(&data))
                    .is_err()
                {
                    web_sys::console::warn_1(&"Intersection callback failed".into());
                }
            }
        }
    });

    let mut init = IntersectionObserverInit::new();
    init.set_root_margin(root_margin);

    let threshold_array = Array::new();
    threshold_array.push(&JsValue::from_f64(threshold));
    init.set_threshold(&threshold_array);

    let observer = IntersectionObserver::new_with_options(closure.as_ref().unchecked_ref(), &init)?;

    observer.observe(element);

    Ok(IntersectionHandle {
        observer,
        element: element.clone(),
        _closure: closure,
    })
}

/// Observe an element once (disconnect after first intersection).
#[wasm_bindgen]
pub fn intersection_observe_once(
    element: &Element,
    threshold: f64,
    root_margin: &str,
    callback: js_sys::Function,
) -> Result<IntersectionHandle, JsValue> {
    let callback_clone = callback.clone();
    let element_for_closure = element.clone();

    let closure = Closure::new(move |entries: Array, observer: IntersectionObserver| {
        for i in 0..entries.length() {
            if let Some(entry) = entries.get(i).dyn_ref::<IntersectionObserverEntry>() {
                if entry.is_intersecting() {
                    let data = IntersectionEntry::from(entry);
                    if callback_clone
                        .call1(&JsValue::NULL, &entry_to_js(&data))
                        .is_err()
                    {
                        web_sys::console::warn_1(&"Intersection once callback failed".into());
                    }
                    observer.unobserve(&element_for_closure);
                    observer.disconnect();
                    break;
                }
            }
        }
    });

    let mut init = IntersectionObserverInit::new();
    init.set_root_margin(root_margin);

    let threshold_array = Array::new();
    threshold_array.push(&JsValue::from_f64(threshold));
    init.set_threshold(&threshold_array);

    let observer = IntersectionObserver::new_with_options(closure.as_ref().unchecked_ref(), &init)?;

    observer.observe(element);

    Ok(IntersectionHandle {
        observer,
        element: element.clone(),
        _closure: closure,
    })
}

/// Helper to set a property on a JS object, logging on failure.
fn set_property(obj: &js_sys::Object, key: &str, value: &JsValue) {
    if js_sys::Reflect::set(obj, &key.into(), value).is_err() {
        web_sys::console::warn_1(&format!("Failed to set property: {}", key).into());
    }
}

fn entry_to_js(entry: &IntersectionEntry) -> JsValue {
    let obj = js_sys::Object::new();
    set_property(&obj, "isIntersecting", &entry.is_intersecting.into());
    set_property(&obj, "intersectionRatio", &entry.intersection_ratio.into());
    set_property(&obj, "time", &entry.time.into());

    let rect = js_sys::Object::new();
    set_property(&rect, "top", &entry.bounding_top.into());
    set_property(&rect, "right", &entry.bounding_right.into());
    set_property(&rect, "bottom", &entry.bounding_bottom.into());
    set_property(&rect, "left", &entry.bounding_left.into());
    set_property(&rect, "width", &entry.bounding_width.into());
    set_property(&rect, "height", &entry.bounding_height.into());
    set_property(&obj, "boundingClientRect", &rect.into());

    obj.into()
}
