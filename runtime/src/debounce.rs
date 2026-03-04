//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                           // hydrogen // runtime // debounce
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! Debounce and throttle utilities. Replaces Hydrogen_Util_Debounce.js

use gloo_timers::callback::Timeout;
use std::cell::RefCell;
use std::rc::Rc;
use wasm_bindgen::closure::Closure;
use wasm_bindgen::prelude::*;
use wasm_bindgen::JsCast;

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

// ═══════════════════════════════════════════════════════════════════════════════
//                                                    // purescript ffi wrappers
// ═══════════════════════════════════════════════════════════════════════════════

/// Create a debounced function matching PureScript FFI signature.
///
/// Returns a JS object with { call, cancel, flush } methods.
///
/// PureScript signature:
/// ```purescript
/// foreign import debounceImpl
///   :: forall a. Number -> Boolean -> Boolean -> (a -> Effect Unit)
///   -> Effect { call :: a -> Effect Unit, cancel :: Effect Unit, flush :: Effect Unit }
/// ```
#[wasm_bindgen(js_name = "debounceImpl")]
pub fn debounce_impl(
    wait_ms: f64,
    leading: bool,
    trailing: bool,
    callback: js_sys::Function,
) -> JsValue {
    let debouncer = Debouncer::new(wait_ms as u32, leading, trailing, callback);
    let debouncer = Rc::new(RefCell::new(debouncer));

    let obj = js_sys::Object::new();

    // call method
    let debouncer_call = Rc::clone(&debouncer);
    let call_fn = Closure::wrap(Box::new(move |args: JsValue| {
        debouncer_call.borrow().call(args);
    }) as Box<dyn Fn(JsValue)>);
    js_sys::Reflect::set(&obj, &"call".into(), call_fn.as_ref().unchecked_ref())
        .unwrap_or_default();
    call_fn.forget();

    // cancel method
    let debouncer_cancel = Rc::clone(&debouncer);
    let cancel_fn = Closure::wrap(Box::new(move || {
        debouncer_cancel.borrow().cancel();
    }) as Box<dyn Fn()>);
    js_sys::Reflect::set(&obj, &"cancel".into(), cancel_fn.as_ref().unchecked_ref())
        .unwrap_or_default();
    cancel_fn.forget();

    // flush method
    let debouncer_flush = Rc::clone(&debouncer);
    let flush_fn = Closure::wrap(Box::new(move || {
        debouncer_flush.borrow().flush();
    }) as Box<dyn Fn()>);
    js_sys::Reflect::set(&obj, &"flush".into(), flush_fn.as_ref().unchecked_ref())
        .unwrap_or_default();
    flush_fn.forget();

    obj.into()
}

/// Create a throttled function matching PureScript FFI signature.
///
/// Returns a JS object with { call, cancel, flush } methods.
///
/// PureScript signature:
/// ```purescript
/// foreign import throttleImpl
///   :: forall a. Number -> Boolean -> Boolean -> (a -> Effect Unit)
///   -> Effect { call :: a -> Effect Unit, cancel :: Effect Unit, flush :: Effect Unit }
/// ```
#[wasm_bindgen(js_name = "throttleImpl")]
pub fn throttle_impl(
    wait_ms: f64,
    leading: bool,
    trailing: bool,
    callback: js_sys::Function,
) -> JsValue {
    let throttler = Throttler::new(wait_ms as u32, leading, trailing, callback);
    let throttler = Rc::new(RefCell::new(throttler));

    let obj = js_sys::Object::new();

    // call method
    let throttler_call = Rc::clone(&throttler);
    let call_fn = Closure::wrap(Box::new(move |args: JsValue| {
        throttler_call.borrow().call(args);
    }) as Box<dyn Fn(JsValue)>);
    js_sys::Reflect::set(&obj, &"call".into(), call_fn.as_ref().unchecked_ref())
        .unwrap_or_default();
    call_fn.forget();

    // cancel method
    let throttler_cancel = Rc::clone(&throttler);
    let cancel_fn = Closure::wrap(Box::new(move || {
        throttler_cancel.borrow().cancel();
    }) as Box<dyn Fn()>);
    js_sys::Reflect::set(&obj, &"cancel".into(), cancel_fn.as_ref().unchecked_ref())
        .unwrap_or_default();
    cancel_fn.forget();

    // flush method
    let throttler_flush = Rc::clone(&throttler);
    let flush_fn = Closure::wrap(Box::new(move || {
        throttler_flush.borrow().flush();
    }) as Box<dyn Fn()>);
    js_sys::Reflect::set(&obj, &"flush".into(), flush_fn.as_ref().unchecked_ref())
        .unwrap_or_default();
    flush_fn.forget();

    obj.into()
}
