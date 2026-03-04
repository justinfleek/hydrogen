//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                              // hydrogen // runtime // events
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! # Event System
//!
//! Pure Rust typed event bus. **Zero JavaScript.**
//!
//! Uses u64 type identifiers for compile-time type safety. Events are
//! discriminated by type ID, enabling safe dispatch without JavaScript Symbols.
//!
//! ## Architecture
//!
//! ```text
//! Publisher → EventBus → Subscribers
//!           (typed by u64 discriminant)
//! ```
//!
//! Subscribers are stored in a HashMap keyed by type ID. Each type ID
//! maps to a Vec of subscriber handles.

use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use wasm_bindgen::prelude::*;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // type registry
// ═══════════════════════════════════════════════════════════════════════════════

static TYPE_ID_COUNTER: AtomicU64 = AtomicU64::new(1);

/// Generate a unique type ID for an event type.
/// This replaces JavaScript Symbols for runtime type safety.
#[wasm_bindgen]
pub fn event_generate_type_id() -> u64 {
    TYPE_ID_COUNTER.fetch_add(1, Ordering::SeqCst)
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // wrapped events
// ═══════════════════════════════════════════════════════════════════════════════

/// A wrapped event with type identifier and payload.
#[wasm_bindgen]
pub struct WrappedEvent {
    type_id: u64,
    payload: JsValue,
}

#[wasm_bindgen]
impl WrappedEvent {
    /// Create a new wrapped event.
    #[wasm_bindgen(constructor)]
    pub fn new(type_id: u64, payload: JsValue) -> WrappedEvent {
        WrappedEvent { type_id, payload }
    }

    /// Get the type ID.
    #[wasm_bindgen(getter)]
    pub fn type_id(&self) -> u64 {
        self.type_id
    }

    /// Get the payload.
    #[wasm_bindgen(getter)]
    pub fn payload(&self) -> JsValue {
        self.payload.clone()
    }

    /// Check if this event matches the expected type.
    #[wasm_bindgen]
    pub fn matches(&self, expected_type_id: u64) -> bool {
        self.type_id == expected_type_id
    }

    /// Unwrap the event if it matches the expected type.
    /// Returns the payload if match, undefined otherwise.
    #[wasm_bindgen]
    pub fn unwrap_if_matches(&self, expected_type_id: u64) -> JsValue {
        if self.type_id == expected_type_id {
            self.payload.clone()
        } else {
            JsValue::UNDEFINED
        }
    }
}

/// Wrap an event with a type identifier.
#[wasm_bindgen]
pub fn event_wrap(type_id: u64, payload: JsValue) -> WrappedEvent {
    WrappedEvent::new(type_id, payload)
}

/// Unwrap an event if it matches the expected type.
#[wasm_bindgen]
pub fn event_unwrap(wrapped: &WrappedEvent, expected_type_id: u64) -> JsValue {
    wrapped.unwrap_if_matches(expected_type_id)
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // logging
// ═══════════════════════════════════════════════════════════════════════════════

/// Log an event to console for debugging.
#[wasm_bindgen]
pub fn event_log(bus_name: Option<String>, event: &JsValue) {
    let prefix = bus_name
        .map(|n| format!("[{}]", n))
        .unwrap_or_else(|| "[EventBus]".to_string());

    web_sys::console::log_2(&JsValue::from_str(&format!("{} Event:", prefix)), event);
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // event bus
// ═══════════════════════════════════════════════════════════════════════════════

/// Unique identifier for a subscription.
pub type SubscriptionId = u64;

static SUBSCRIPTION_ID_COUNTER: AtomicU64 = AtomicU64::new(1);

/// Generate a unique subscription ID.
fn next_subscription_id() -> SubscriptionId {
    SUBSCRIPTION_ID_COUNTER.fetch_add(1, Ordering::SeqCst)
}

/// A subscription entry in the event bus.
#[derive(Clone)]
struct Subscription {
    /// Unique subscription identifier.
    id: SubscriptionId,
    /// Callback to invoke when event fires.
    callback: js_sys::Function,
}

/// Pure Rust event bus with typed channels.
///
/// Events are discriminated by u64 type IDs. Subscribers register
/// for specific type IDs and receive only matching events.
pub struct EventBus {
    /// Subscribers indexed by event type ID.
    subscribers: HashMap<u64, Vec<Subscription>>,
    /// Optional name for debugging.
    name: Option<String>,
}

impl EventBus {
    /// Create a new event bus.
    pub fn new(name: Option<String>) -> Self {
        EventBus {
            subscribers: HashMap::new(),
            name,
        }
    }

    /// Subscribe to events of a specific type.
    ///
    /// Returns a subscription ID that can be used to unsubscribe.
    pub fn subscribe(&mut self, type_id: u64, callback: js_sys::Function) -> SubscriptionId {
        let id = next_subscription_id();
        let subscription = Subscription { id, callback };

        self.subscribers
            .entry(type_id)
            .or_insert_with(Vec::new)
            .push(subscription);

        id
    }

    /// Unsubscribe using a subscription ID.
    ///
    /// Returns true if the subscription was found and removed.
    pub fn unsubscribe(&mut self, subscription_id: SubscriptionId) -> bool {
        for subs in self.subscribers.values_mut() {
            if let Some(pos) = subs.iter().position(|s| s.id == subscription_id) {
                subs.remove(pos);
                return true;
            }
        }
        false
    }

    /// Publish an event to all subscribers of its type.
    ///
    /// Returns the number of subscribers notified.
    pub fn publish(&self, event: &WrappedEvent) -> usize {
        let type_id = event.type_id();

        if let Some(subs) = self.subscribers.get(&type_id) {
            let payload = event.payload();
            let mut count = 0;

            for sub in subs {
                // Call the subscriber callback with the payload
                let this = JsValue::NULL;
                if sub.callback.call1(&this, &payload).is_ok() {
                    count += 1;
                }
            }

            count
        } else {
            0
        }
    }

    /// Get the number of subscribers for a type.
    pub fn subscriber_count(&self, type_id: u64) -> usize {
        self.subscribers.get(&type_id).map_or(0, |v| v.len())
    }

    /// Get the total number of subscriptions.
    pub fn total_subscriptions(&self) -> usize {
        self.subscribers.values().map(|v| v.len()).sum()
    }

    /// Clear all subscriptions for a type.
    pub fn clear_type(&mut self, type_id: u64) {
        self.subscribers.remove(&type_id);
    }

    /// Clear all subscriptions.
    pub fn clear_all(&mut self) {
        self.subscribers.clear();
    }

    /// Get the bus name (for debugging).
    pub fn name(&self) -> Option<&str> {
        self.name.as_deref()
    }
}

impl Default for EventBus {
    fn default() -> Self {
        Self::new(None)
    }
}
