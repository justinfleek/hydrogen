//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                           // hydrogen // runtime // debounce
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! Debounce and throttle utilities. Replaces Hydrogen_Util_Debounce.js

use gloo_timers::callback::Timeout;
use std::cell::RefCell;
use std::rc::Rc;
use wasm_bindgen::prelude::*;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // debounce
// ═══════════════════════════════════════════════════════════════════════════════

/// Debounced function state.
#[wasm_bindgen]
pub struct Debouncer {
    wait_ms: u32,
    leading: bool,
    trailing: bool,
    callback: js_sys::Function,
    timer: Rc<RefCell<Option<Timeout>>>,
    last_args: Rc<RefCell<Option<JsValue>>>,
    last_invoke_time: Rc<RefCell<f64>>,
}

#[wasm_bindgen]
impl Debouncer {
    /// Create a new debouncer.
    #[wasm_bindgen(constructor)]
    pub fn new(
        wait_ms: u32,
        leading: bool,
        trailing: bool,
        callback: js_sys::Function,
    ) -> Debouncer {
        Debouncer {
            wait_ms,
            leading,
            trailing,
            callback,
            timer: Rc::new(RefCell::new(None)),
            last_args: Rc::new(RefCell::new(None)),
            last_invoke_time: Rc::new(RefCell::new(0.0)),
        }
    }

    /// Call the debounced function.
    #[wasm_bindgen]
    pub fn call(&self, args: JsValue) {
        let now = js_sys::Date::now();
        let time_since_last = now - *self.last_invoke_time.borrow();

        *self.last_args.borrow_mut() = Some(args.clone());

        let should_invoke =
            time_since_last >= self.wait_ms as f64 || *self.last_invoke_time.borrow() == 0.0;

        // Cancel existing timer
        if let Some(timer) = self.timer.borrow_mut().take() {
            drop(timer);
        }

        if should_invoke && self.leading {
            self.invoke();
        }

        // Set new timer for trailing edge
        if self.trailing {
            let callback = self.callback.clone();
            let last_args = Rc::clone(&self.last_args);
            let last_invoke_time = Rc::clone(&self.last_invoke_time);
            let timer_ref = Rc::clone(&self.timer);

            let timeout = Timeout::new(self.wait_ms, move || {
                if let Some(args) = last_args.borrow_mut().take() {
                    *last_invoke_time.borrow_mut() = js_sys::Date::now();
                    if callback.call1(&JsValue::NULL, &args).is_err() {
                        web_sys::console::warn_1(&"Debounce callback failed".into());
                    }
                }
                *timer_ref.borrow_mut() = None;
            });

            *self.timer.borrow_mut() = Some(timeout);
        }
    }

    /// Cancel pending invocation.
    #[wasm_bindgen]
    pub fn cancel(&self) {
        if let Some(timer) = self.timer.borrow_mut().take() {
            drop(timer);
        }
        *self.last_args.borrow_mut() = None;
        *self.last_invoke_time.borrow_mut() = 0.0;
    }

    /// Flush: invoke immediately if pending.
    #[wasm_bindgen]
    pub fn flush(&self) {
        if self.last_args.borrow().is_some() {
            if let Some(timer) = self.timer.borrow_mut().take() {
                drop(timer);
            }
            self.invoke();
        }
    }

    fn invoke(&self) {
        if let Some(args) = self.last_args.borrow_mut().take() {
            *self.last_invoke_time.borrow_mut() = js_sys::Date::now();
            if self.callback.call1(&JsValue::NULL, &args).is_err() {
                web_sys::console::warn_1(&"Debounce invoke callback failed".into());
            }
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // throttle
// ═══════════════════════════════════════════════════════════════════════════════

/// Throttled function state.
#[wasm_bindgen]
pub struct Throttler {
    wait_ms: u32,
    leading: bool,
    trailing: bool,
    callback: js_sys::Function,
    timer: Rc<RefCell<Option<Timeout>>>,
    last_args: Rc<RefCell<Option<JsValue>>>,
    last_invoke_time: Rc<RefCell<f64>>,
}

#[wasm_bindgen]
impl Throttler {
    /// Create a new throttler.
    #[wasm_bindgen(constructor)]
    pub fn new(
        wait_ms: u32,
        leading: bool,
        trailing: bool,
        callback: js_sys::Function,
    ) -> Throttler {
        Throttler {
            wait_ms,
            leading,
            trailing,
            callback,
            timer: Rc::new(RefCell::new(None)),
            last_args: Rc::new(RefCell::new(None)),
            last_invoke_time: Rc::new(RefCell::new(0.0)),
        }
    }

    /// Call the throttled function.
    #[wasm_bindgen]
    pub fn call(&self, args: JsValue) {
        let now = js_sys::Date::now();
        let elapsed = now - *self.last_invoke_time.borrow();

        *self.last_args.borrow_mut() = Some(args);

        if elapsed >= self.wait_ms as f64 {
            if self.leading {
                self.invoke();
            }
            self.start_timer();
        } else if self.timer.borrow().is_none() {
            self.start_timer();
        }
    }

    /// Cancel pending invocation.
    #[wasm_bindgen]
    pub fn cancel(&self) {
        if let Some(timer) = self.timer.borrow_mut().take() {
            drop(timer);
        }
        *self.last_args.borrow_mut() = None;
        *self.last_invoke_time.borrow_mut() = 0.0;
    }

    /// Flush: invoke immediately if pending.
    #[wasm_bindgen]
    pub fn flush(&self) {
        if self.last_args.borrow().is_some() {
            self.invoke();
        }
    }

    fn invoke(&self) {
        if let Some(args) = self.last_args.borrow_mut().take() {
            *self.last_invoke_time.borrow_mut() = js_sys::Date::now();
            if self.callback.call1(&JsValue::NULL, &args).is_err() {
                web_sys::console::warn_1(&"Throttle invoke callback failed".into());
            }
        }
    }

    fn start_timer(&self) {
        if self.timer.borrow().is_some() {
            return;
        }

        let callback = self.callback.clone();
        let last_args = Rc::clone(&self.last_args);
        let last_invoke_time = Rc::clone(&self.last_invoke_time);
        let timer_ref = Rc::clone(&self.timer);
        let trailing = self.trailing;
        let wait_ms = self.wait_ms;

        let this_timer_ref = Rc::clone(&self.timer);

        let timeout = Timeout::new(wait_ms, move || {
            *timer_ref.borrow_mut() = None;
            if trailing {
                if let Some(args) = last_args.borrow_mut().take() {
                    *last_invoke_time.borrow_mut() = js_sys::Date::now();
                    if callback.call1(&JsValue::NULL, &args).is_err() {
                        web_sys::console::warn_1(&"Throttle trailing callback failed".into());
                    }
                }
            }
        });

        *this_timer_ref.borrow_mut() = Some(timeout);
    }
}
