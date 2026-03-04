//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                             // hydrogen // runtime // storage
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! LocalStorage API. Replaces Hydrogen_Util_LocalStorage.js

use wasm_bindgen::closure::Closure;
use wasm_bindgen::prelude::*;
use web_sys::{window, Storage, StorageEvent};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // get storage
// ═══════════════════════════════════════════════════════════════════════════════

fn get_local_storage() -> Option<Storage> {
    window()?.local_storage().ok()?
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // basic ops
// ═══════════════════════════════════════════════════════════════════════════════

/// Get an item from localStorage. Returns empty string if not found or error.
#[wasm_bindgen]
pub fn storage_get_item(key: &str) -> Option<String> {
    get_local_storage()?.get_item(key).ok()?
}

/// Set an item in localStorage.
#[wasm_bindgen]
pub fn storage_set_item(key: &str, value: &str) -> Result<(), JsValue> {
    get_local_storage()
        .ok_or_else(|| JsValue::from_str("No localStorage"))?
        .set_item(key, value)
        .map_err(|e| JsValue::from_str(&format!("setItem failed: {:?}", e)))
}

/// Remove an item from localStorage.
#[wasm_bindgen]
pub fn storage_remove_item(key: &str) -> Result<(), JsValue> {
    get_local_storage()
        .ok_or_else(|| JsValue::from_str("No localStorage"))?
        .remove_item(key)
        .map_err(|e| JsValue::from_str(&format!("removeItem failed: {:?}", e)))
}

/// Clear all items from localStorage.
#[wasm_bindgen]
pub fn storage_clear() -> Result<(), JsValue> {
    get_local_storage()
        .ok_or_else(|| JsValue::from_str("No localStorage"))?
        .clear()
        .map_err(|e| JsValue::from_str(&format!("clear failed: {:?}", e)))
}

/// Get all keys from localStorage.
#[wasm_bindgen]
pub fn storage_keys() -> Vec<String> {
    let storage = match get_local_storage() {
        Some(s) => s,
        None => return Vec::new(),
    };

    let len = storage.length().unwrap_or(0);
    let mut keys = Vec::with_capacity(len as usize);

    for i in 0..len {
        if let Ok(Some(key)) = storage.key(i) {
            keys.push(key);
        }
    }

    keys
}

/// Get the number of items in localStorage.
#[wasm_bindgen]
pub fn storage_length() -> u32 {
    get_local_storage()
        .and_then(|s| s.length().ok())
        .unwrap_or(0)
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // change events
// ═══════════════════════════════════════════════════════════════════════════════

/// Handle for a storage change listener. Drop to unsubscribe.
#[wasm_bindgen]
pub struct StorageChangeHandle {
    closure: Closure<dyn Fn(StorageEvent)>,
}

impl Drop for StorageChangeHandle {
    fn drop(&mut self) {
        if let Some(win) = window() {
            // Remove the event listener when the handle is dropped
            let _ = win.remove_event_listener_with_callback(
                "storage",
                self.closure.as_ref().unchecked_ref(),
            );
        }
    }
}

/// Subscribe to storage changes for a specific key.
/// Returns a handle that unsubscribes when dropped.
#[wasm_bindgen]
pub fn storage_on_change(
    key: String,
    callback: js_sys::Function,
) -> Result<StorageChangeHandle, JsValue> {
    let win = window().ok_or_else(|| JsValue::from_str("No window"))?;

    let closure = Closure::new(move |event: StorageEvent| {
        let event_key = event.key();
        if event_key.as_ref() == Some(&key) || event_key.is_none() {
            let new_value = event.new_value().unwrap_or_default();
            if callback
                .call1(&JsValue::NULL, &JsValue::from_str(&new_value))
                .is_err()
            {
                web_sys::console::warn_1(&"Storage change callback failed".into());
            }
        }
    });

    win.add_event_listener_with_callback("storage", closure.as_ref().unchecked_ref())
        .map_err(|e| JsValue::from_str(&format!("addEventListener failed: {:?}", e)))?;

    Ok(StorageChangeHandle { closure })
}

/// Subscribe to all storage changes.
#[wasm_bindgen]
pub fn storage_on_any_change(callback: js_sys::Function) -> Result<StorageChangeHandle, JsValue> {
    let win = window().ok_or_else(|| JsValue::from_str("No window"))?;

    let closure = Closure::new(move |event: StorageEvent| {
        if let Some(key) = event.key() {
            let new_value = event.new_value().unwrap_or_default();
            if callback
                .call2(
                    &JsValue::NULL,
                    &JsValue::from_str(&key),
                    &JsValue::from_str(&new_value),
                )
                .is_err()
            {
                web_sys::console::warn_1(&"Storage any-change callback failed".into());
            }
        }
    });

    win.add_event_listener_with_callback("storage", closure.as_ref().unchecked_ref())
        .map_err(|e| JsValue::from_str(&format!("addEventListener failed: {:?}", e)))?;

    Ok(StorageChangeHandle { closure })
}
