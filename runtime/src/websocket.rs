//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                           // hydrogen // runtime // websocket
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! WebSocket API. Replaces Hydrogen_Realtime_WebSocket.js

use wasm_bindgen::closure::Closure;
use wasm_bindgen::prelude::*;
use wasm_bindgen::JsCast;
use web_sys::{CloseEvent, ErrorEvent, Event, MessageEvent, WebSocket};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // websocket
// ═══════════════════════════════════════════════════════════════════════════════

/// Create a new WebSocket connection.
#[wasm_bindgen]
pub fn ws_new(url: &str, protocols: Vec<String>) -> Result<WebSocket, JsValue> {
    let protocols_array = js_sys::Array::new();
    for p in protocols {
        protocols_array.push(&JsValue::from_str(&p));
    }

    if protocols_array.length() > 0 {
        WebSocket::new_with_str_sequence(url, &protocols_array)
    } else {
        WebSocket::new(url)
    }
}

/// Create a new WebSocket with a single protocol.
#[wasm_bindgen]
pub fn ws_new_with_protocol(url: &str, protocol: &str) -> Result<WebSocket, JsValue> {
    WebSocket::new_with_str(url, protocol)
}

/// Send a text message.
#[wasm_bindgen]
pub fn ws_send(ws: &WebSocket, data: &str) -> Result<(), JsValue> {
    ws.send_with_str(data)
}

/// Send binary data.
#[wasm_bindgen]
pub fn ws_send_binary(ws: &WebSocket, data: &[u8]) -> Result<(), JsValue> {
    ws.send_with_u8_array(data)
}

/// Close the connection.
#[wasm_bindgen]
pub fn ws_close(ws: &WebSocket) -> Result<(), JsValue> {
    ws.close()
}

/// Close with code and reason.
#[wasm_bindgen]
pub fn ws_close_with_code(ws: &WebSocket, code: u16, reason: &str) -> Result<(), JsValue> {
    ws.close_with_code_and_reason(code, reason)
}

/// Get ready state (0=CONNECTING, 1=OPEN, 2=CLOSING, 3=CLOSED).
#[wasm_bindgen]
pub fn ws_ready_state(ws: &WebSocket) -> u16 {
    ws.ready_state()
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // event handlers
// ═══════════════════════════════════════════════════════════════════════════════

/// Handle for WebSocket event listeners. Drop to remove listeners.
#[wasm_bindgen]
pub struct WsEventHandle {
    _on_open: Option<Closure<dyn Fn(Event)>>,
    _on_close: Option<Closure<dyn Fn(CloseEvent)>>,
    _on_error: Option<Closure<dyn Fn(ErrorEvent)>>,
    _on_message: Option<Closure<dyn Fn(MessageEvent)>>,
}

/// Set onopen handler.
#[wasm_bindgen]
pub fn ws_on_open(ws: &WebSocket, callback: js_sys::Function) -> Closure<dyn Fn(Event)> {
    let closure = Closure::new(move |_event: Event| {
        if callback.call0(&JsValue::NULL).is_err() {
            web_sys::console::warn_1(&"WebSocket onopen callback failed".into());
        }
    });
    ws.set_onopen(Some(closure.as_ref().unchecked_ref()));
    closure
}

/// Set onclose handler.
#[wasm_bindgen]
pub fn ws_on_close(ws: &WebSocket, callback: js_sys::Function) -> Closure<dyn Fn(CloseEvent)> {
    let closure = Closure::new(move |event: CloseEvent| {
        let code = event.code();
        let reason = event.reason();
        if callback
            .call2(
                &JsValue::NULL,
                &JsValue::from_f64(code as f64),
                &JsValue::from_str(&reason),
            )
            .is_err()
        {
            web_sys::console::warn_1(&"WebSocket onclose callback failed".into());
        }
    });
    ws.set_onclose(Some(closure.as_ref().unchecked_ref()));
    closure
}

/// Set onerror handler.
#[wasm_bindgen]
pub fn ws_on_error(ws: &WebSocket, callback: js_sys::Function) -> Closure<dyn Fn(ErrorEvent)> {
    let closure = Closure::new(move |event: ErrorEvent| {
        let message = event.message();
        if callback
            .call1(&JsValue::NULL, &JsValue::from_str(&message))
            .is_err()
        {
            web_sys::console::warn_1(&"WebSocket onerror callback failed".into());
        }
    });
    ws.set_onerror(Some(closure.as_ref().unchecked_ref()));
    closure
}

/// Set onmessage handler.
#[wasm_bindgen]
pub fn ws_on_message(ws: &WebSocket, callback: js_sys::Function) -> Closure<dyn Fn(MessageEvent)> {
    let closure = Closure::new(move |event: MessageEvent| {
        let data = event.data();
        if callback.call1(&JsValue::NULL, &data).is_err() {
            web_sys::console::warn_1(&"WebSocket onmessage callback failed".into());
        }
    });
    ws.set_onmessage(Some(closure.as_ref().unchecked_ref()));
    closure
}
