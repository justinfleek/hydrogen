//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                                // hydrogen // runtime // sse
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! Server-Sent Events API. Replaces Hydrogen_Realtime_SSE.js

use wasm_bindgen::closure::Closure;
use wasm_bindgen::prelude::*;
use wasm_bindgen::JsCast;
use web_sys::{Event, EventSource, EventSourceInit, MessageEvent};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // eventsource
// ═══════════════════════════════════════════════════════════════════════════════

/// Create a new EventSource connection.
#[wasm_bindgen]
pub fn sse_new(url: &str, with_credentials: bool) -> Result<EventSource, JsValue> {
    let init = EventSourceInit::new();
    init.set_with_credentials(with_credentials);
    EventSource::new_with_event_source_init_dict(url, &init)
}

/// Close the EventSource connection.
#[wasm_bindgen]
pub fn sse_close(source: &EventSource) {
    source.close();
}

/// Get ready state (0=CONNECTING, 1=OPEN, 2=CLOSED).
#[wasm_bindgen]
pub fn sse_ready_state(source: &EventSource) -> u16 {
    source.ready_state()
}

/// Get the URL.
#[wasm_bindgen]
pub fn sse_url(source: &EventSource) -> String {
    source.url()
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // event handlers
// ═══════════════════════════════════════════════════════════════════════════════

/// Set onopen handler.
#[wasm_bindgen]
pub fn sse_on_open(source: &EventSource, callback: js_sys::Function) -> Closure<dyn Fn(Event)> {
    let closure = Closure::new(move |_event: Event| {
        if callback.call0(&JsValue::NULL).is_err() {
            web_sys::console::warn_1(&"SSE onopen callback failed".into());
        }
    });
    source.set_onopen(Some(closure.as_ref().unchecked_ref()));
    closure
}

/// Set onmessage handler (for unnamed events).
#[wasm_bindgen]
pub fn sse_on_message(
    source: &EventSource,
    callback: js_sys::Function,
) -> Closure<dyn Fn(MessageEvent)> {
    let closure = Closure::new(move |event: MessageEvent| {
        let data = event.data();
        if callback.call1(&JsValue::NULL, &data).is_err() {
            web_sys::console::warn_1(&"SSE onmessage callback failed".into());
        }
    });
    source.set_onmessage(Some(closure.as_ref().unchecked_ref()));
    closure
}

/// Set onerror handler.
#[wasm_bindgen]
pub fn sse_on_error(source: &EventSource, callback: js_sys::Function) -> Closure<dyn Fn(Event)> {
    let closure = Closure::new(move |_event: Event| {
        if callback
            .call1(&JsValue::NULL, &JsValue::from_str("EventSource error"))
            .is_err()
        {
            web_sys::console::warn_1(&"SSE onerror callback failed".into());
        }
    });
    source.set_onerror(Some(closure.as_ref().unchecked_ref()));
    closure
}

/// Add event listener for named events.
#[wasm_bindgen]
pub fn sse_add_event_listener(
    source: &EventSource,
    event_type: &str,
    callback: js_sys::Function,
) -> Result<Closure<dyn Fn(MessageEvent)>, JsValue> {
    let closure = Closure::new(move |event: MessageEvent| {
        let data = event.data();
        if callback.call1(&JsValue::NULL, &data).is_err() {
            web_sys::console::warn_1(&"SSE named event callback failed".into());
        }
    });

    source.add_event_listener_with_callback(event_type, closure.as_ref().unchecked_ref())?;

    Ok(closure)
}
