//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                              // hydrogen // runtime // router
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! Browser History API. Replaces Hydrogen_Router.js

use wasm_bindgen::closure::Closure;
use wasm_bindgen::prelude::*;
use wasm_bindgen::JsCast;
use web_sys::{window, CustomEvent, CustomEventInit, Event, HtmlAnchorElement, MouseEvent, Url};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // location
// ═══════════════════════════════════════════════════════════════════════════════

/// Get the current pathname.
#[wasm_bindgen]
pub fn router_get_pathname() -> String {
    window()
        .and_then(|w| w.location().pathname().ok())
        .unwrap_or_default()
}

/// Get the current hostname.
#[wasm_bindgen]
pub fn router_get_hostname() -> String {
    window()
        .and_then(|w| w.location().hostname().ok())
        .unwrap_or_default()
}

/// Get the current origin.
#[wasm_bindgen]
pub fn router_get_origin() -> String {
    window()
        .and_then(|w| w.location().origin().ok())
        .unwrap_or_default()
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // navigation
// ═══════════════════════════════════════════════════════════════════════════════

/// Push a new state to history.
#[wasm_bindgen]
pub fn router_push_state(path: &str) -> Result<(), JsValue> {
    let win = window().ok_or_else(|| JsValue::from_str("No window"))?;
    let history = win.history()?;

    history.push_state_with_url(&JsValue::NULL, "", Some(path))?;

    // Dispatch custom event for route change
    let mut init = CustomEventInit::new();
    init.set_detail(&JsValue::from_str(path));
    let event = CustomEvent::new_with_event_init_dict("hydrogen:routechange", &init)?;
    win.dispatch_event(&event)?;

    Ok(())
}

/// Replace the current state in history.
#[wasm_bindgen]
pub fn router_replace_state(path: &str) -> Result<(), JsValue> {
    let win = window().ok_or_else(|| JsValue::from_str("No window"))?;
    let history = win.history()?;

    history.replace_state_with_url(&JsValue::NULL, "", Some(path))?;

    Ok(())
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // listeners
// ═══════════════════════════════════════════════════════════════════════════════

/// Handle for route change listener. Drop to unsubscribe.
#[wasm_bindgen]
pub struct RouteChangeHandle {
    _popstate_closure: Closure<dyn Fn(Event)>,
    _custom_closure: Closure<dyn Fn(CustomEvent)>,
}

/// Subscribe to route changes (both popstate and programmatic).
#[wasm_bindgen]
pub fn router_on_route_change(callback: js_sys::Function) -> Result<RouteChangeHandle, JsValue> {
    let win = window().ok_or_else(|| JsValue::from_str("No window"))?;

    let callback_clone = callback.clone();
    let popstate_closure = Closure::new(move |_event: Event| {
        if let Some(pathname) = window().and_then(|w| w.location().pathname().ok()) {
            if callback_clone
                .call1(&JsValue::NULL, &JsValue::from_str(&pathname))
                .is_err()
            {
                web_sys::console::warn_1(&"Route change callback failed (popstate)".into());
            }
        }
    });

    let custom_closure = Closure::new(move |event: CustomEvent| {
        if let Some(detail) = event.detail().as_string() {
            if callback
                .call1(&JsValue::NULL, &JsValue::from_str(&detail))
                .is_err()
            {
                web_sys::console::warn_1(&"Route change callback failed (custom event)".into());
            }
        }
    });

    win.add_event_listener_with_callback("popstate", popstate_closure.as_ref().unchecked_ref())?;
    win.add_event_listener_with_callback(
        "hydrogen:routechange",
        custom_closure.as_ref().unchecked_ref(),
    )?;

    Ok(RouteChangeHandle {
        _popstate_closure: popstate_closure,
        _custom_closure: custom_closure,
    })
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // link intercept
// ═══════════════════════════════════════════════════════════════════════════════

/// Handle for link interceptor. Drop to stop intercepting.
#[wasm_bindgen]
pub struct LinkInterceptHandle {
    _closure: Closure<dyn Fn(MouseEvent)>,
}

/// Intercept all internal link clicks for SPA navigation.
#[wasm_bindgen]
pub fn router_intercept_links(callback: js_sys::Function) -> Result<LinkInterceptHandle, JsValue> {
    let win = window().ok_or_else(|| JsValue::from_str("No window"))?;
    let document = win
        .document()
        .ok_or_else(|| JsValue::from_str("No document"))?;
    let origin = win.location().origin()?;

    let closure = Closure::new(move |event: MouseEvent| {
        // Find closest anchor element
        let target = match event.target() {
            Some(t) => t,
            None => return,
        };

        let element = match target.dyn_into::<web_sys::Element>() {
            Ok(e) => e,
            Err(_) => return,
        };

        let anchor = match element.closest("a") {
            Ok(Some(a)) => a,
            _ => return,
        };

        let anchor = match anchor.dyn_into::<HtmlAnchorElement>() {
            Ok(a) => a,
            Err(_) => return,
        };

        let href = anchor.get_attribute("href").unwrap_or_default();
        if href.is_empty() {
            return;
        }

        // Skip _blank and download
        if anchor.target() == "_blank" || anchor.has_attribute("download") {
            return;
        }

        // Handle external links
        if href.starts_with("http://") || href.starts_with("https://") || href.starts_with("//") {
            if let Ok(url) = Url::new_with_base(&href, &origin) {
                if url.origin() != origin {
                    return; // External link
                }
                // Same origin full URL
                event.prevent_default();
                let path = format!("{}{}{}", url.pathname(), url.search(), url.hash());
                if router_push_state(&path).is_err() {
                    web_sys::console::warn_1(&"Failed to push state for same-origin link".into());
                }
                if callback
                    .call1(&JsValue::NULL, &JsValue::from_str(&url.pathname()))
                    .is_err()
                {
                    web_sys::console::warn_1(&"Link intercept callback failed".into());
                }
            }
            return;
        }

        // Internal links starting with /
        if href.starts_with('/') && !href.starts_with("//") {
            event.prevent_default();
            if router_push_state(&href).is_err() {
                web_sys::console::warn_1(&"Failed to push state for internal link".into());
            }
            if callback
                .call1(&JsValue::NULL, &JsValue::from_str(&href))
                .is_err()
            {
                web_sys::console::warn_1(&"Link intercept callback failed".into());
            }
        }
    });

    document.add_event_listener_with_callback("click", closure.as_ref().unchecked_ref())?;

    Ok(LinkInterceptHandle { _closure: closure })
}
