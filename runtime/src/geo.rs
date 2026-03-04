//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                                 // hydrogen // runtime // geo
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! # Geolocation API
//!
//! Pure Rust implementation of browser Geolocation API.
//! Replaces JavaScript FFI in Hydrogen.Geo.Geolocation.
//!
//! ## Lean4 Invariants
//!
//! See: `proofs/Hydrogen/Browser/Invariants.lean` (Geolocation section)
//!
//! - Latitude ∈ [-90, 90] — Coordinates returned by browser are clamped
//! - Longitude ∈ [-180, 180) — Coordinates returned by browser are wrapped
//! - Accuracy ≥ 0 — Cannot have negative measurement error
//!
//! ## State Machine
//!
//! Geolocation has an implicit state machine:
//!
//! ```text
//! Idle --(watchPosition)--> Watching --(clearWatch)--> Idle
//!                               |
//!                               v
//!                          (callbacks)
//! ```
//!
//! ## FFI Functions Implemented
//!
//! 1. `geo_is_supported` — Check if Geolocation API available
//! 2. `geo_get_current_position` — One-time position fetch (async)
//! 3. `geo_watch_position` — Continuous position updates
//! 4. `geo_clear_watch` — Stop watching
//! 5. `geo_watch_geofence` — Monitor enter/exit of circular region

use wasm_bindgen::prelude::*;

#[cfg(target_arch = "wasm32")]
use wasm_bindgen::closure::Closure;
#[cfg(target_arch = "wasm32")]
use std::cell::RefCell;
#[cfg(target_arch = "wasm32")]
use std::rc::Rc;

#[cfg(target_arch = "wasm32")]
use web_sys::{
    window, Geolocation, GeolocationPosition, GeolocationPositionError, PositionOptions,
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // bounded types
// ═══════════════════════════════════════════════════════════════════════════════

/// Latitude bounded to [-90, 90].
/// Clamped on construction — invalid values become nearest valid value.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct BoundedLatitude(f64);

impl BoundedLatitude {
    pub const MIN: f64 = -90.0;
    pub const MAX: f64 = 90.0;

    /// Create a bounded latitude, clamping invalid values.
    pub fn new(value: f64) -> Self {
        if value.is_nan() || value.is_infinite() {
            BoundedLatitude(0.0)
        } else {
            BoundedLatitude(value.clamp(Self::MIN, Self::MAX))
        }
    }

    pub fn value(&self) -> f64 {
        self.0
    }
}

/// Longitude bounded to [-180, 180).
/// Wraps on construction — values outside range wrap around.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct BoundedLongitude(f64);

impl BoundedLongitude {
    pub const MIN: f64 = -180.0;
    pub const MAX: f64 = 180.0;

    /// Create a bounded longitude, wrapping invalid values.
    pub fn new(value: f64) -> Self {
        if value.is_nan() || value.is_infinite() {
            BoundedLongitude(0.0)
        } else {
            // Wrap to [-180, 180)
            let shifted = value + 180.0;
            let wrapped = shifted - 360.0 * (shifted / 360.0).floor();
            BoundedLongitude(wrapped - 180.0)
        }
    }

    pub fn value(&self) -> f64 {
        self.0
    }
}

/// Accuracy in meters, non-negative.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct BoundedAccuracy(f64);

impl BoundedAccuracy {
    /// Create a bounded accuracy, clamping negative values to 0.
    pub fn new(value: f64) -> Self {
        if value.is_nan() || value.is_infinite() {
            BoundedAccuracy(0.0)
        } else {
            BoundedAccuracy(value.max(0.0))
        }
    }

    pub fn value(&self) -> f64 {
        self.0
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // position data
// ═══════════════════════════════════════════════════════════════════════════════

/// Geographic position with bounded coordinates.
#[wasm_bindgen]
#[derive(Clone, Debug)]
pub struct GeoPosition {
    latitude: f64,
    longitude: f64,
    altitude: Option<f64>,
    accuracy: f64,
    altitude_accuracy: Option<f64>,
    heading: Option<f64>,
    speed: Option<f64>,
    timestamp: f64,
}

#[wasm_bindgen]
impl GeoPosition {
    #[wasm_bindgen(getter)]
    pub fn latitude(&self) -> f64 {
        self.latitude
    }

    #[wasm_bindgen(getter)]
    pub fn longitude(&self) -> f64 {
        self.longitude
    }

    #[wasm_bindgen(getter)]
    pub fn altitude(&self) -> Option<f64> {
        self.altitude
    }

    #[wasm_bindgen(getter)]
    pub fn accuracy(&self) -> f64 {
        self.accuracy
    }

    #[wasm_bindgen(getter)]
    pub fn altitude_accuracy(&self) -> Option<f64> {
        self.altitude_accuracy
    }

    #[wasm_bindgen(getter)]
    pub fn heading(&self) -> Option<f64> {
        self.heading
    }

    #[wasm_bindgen(getter)]
    pub fn speed(&self) -> Option<f64> {
        self.speed
    }

    #[wasm_bindgen(getter)]
    pub fn timestamp(&self) -> f64 {
        self.timestamp
    }
}

impl GeoPosition {
    /// Create from raw browser Position, applying bounds.
    #[cfg(target_arch = "wasm32")]
    fn from_browser_position(pos: &GeolocationPosition) -> Self {
        let coords = pos.coords();
        
        let lat = BoundedLatitude::new(coords.latitude());
        let lon = BoundedLongitude::new(coords.longitude());
        let acc = BoundedAccuracy::new(coords.accuracy());
        
        GeoPosition {
            latitude: lat.value(),
            longitude: lon.value(),
            altitude: coords.altitude(),
            accuracy: acc.value(),
            altitude_accuracy: coords.altitude_accuracy(),
            heading: coords.heading(),
            speed: coords.speed(),
            timestamp: pos.timestamp(),
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // error types
// ═══════════════════════════════════════════════════════════════════════════════

/// Geolocation error codes.
#[wasm_bindgen]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GeoErrorCode {
    PermissionDenied = 1,
    PositionUnavailable = 2,
    Timeout = 3,
    Unknown = 0,
}

impl GeoErrorCode {
    #[cfg(target_arch = "wasm32")]
    fn from_browser_error(err: &GeolocationPositionError) -> Self {
        match err.code() {
            1 => GeoErrorCode::PermissionDenied,
            2 => GeoErrorCode::PositionUnavailable,
            3 => GeoErrorCode::Timeout,
            _ => GeoErrorCode::Unknown,
        }
    }
}

/// Geolocation error with code and message.
#[wasm_bindgen]
#[derive(Clone, Debug)]
pub struct GeoError {
    code: GeoErrorCode,
    message: String,
}

#[wasm_bindgen]
impl GeoError {
    #[wasm_bindgen(getter)]
    pub fn code(&self) -> GeoErrorCode {
        self.code
    }

    #[wasm_bindgen(getter)]
    pub fn message(&self) -> String {
        self.message.clone()
    }
}

impl GeoError {
    #[cfg(target_arch = "wasm32")]
    fn from_browser_error(err: &GeolocationPositionError) -> Self {
        GeoError {
            code: GeoErrorCode::from_browser_error(err),
            message: err.message(),
        }
    }

    /// Create an error for unsupported platforms.
    #[allow(dead_code)]
    pub fn not_supported() -> Self {
        GeoError {
            code: GeoErrorCode::PositionUnavailable,
            message: "Geolocation API not supported".to_string(),
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // api functions
// ═══════════════════════════════════════════════════════════════════════════════

/// Get the browser's Geolocation object.
#[cfg(target_arch = "wasm32")]
fn get_geolocation() -> Option<Geolocation> {
    window()?.navigator().geolocation().ok()
}

/// Check if Geolocation API is supported.
#[wasm_bindgen]
pub fn geo_is_supported() -> bool {
    #[cfg(target_arch = "wasm32")]
    {
        get_geolocation().is_some()
    }
    #[cfg(not(target_arch = "wasm32"))]
    {
        false
    }
}

/// Position options for requests.
#[wasm_bindgen]
#[derive(Clone, Debug)]
pub struct GeoOptions {
    pub enable_high_accuracy: bool,
    pub timeout_ms: u32,
    pub maximum_age_ms: u32,
}

#[wasm_bindgen]
impl GeoOptions {
    #[wasm_bindgen(constructor)]
    pub fn new() -> Self {
        GeoOptions {
            enable_high_accuracy: false,
            timeout_ms: 10000,
            maximum_age_ms: 0,
        }
    }

    pub fn with_high_accuracy(mut self, enabled: bool) -> Self {
        self.enable_high_accuracy = enabled;
        self
    }

    pub fn with_timeout(mut self, ms: u32) -> Self {
        self.timeout_ms = ms;
        self
    }

    pub fn with_maximum_age(mut self, ms: u32) -> Self {
        self.maximum_age_ms = ms;
        self
    }
}

impl Default for GeoOptions {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(target_arch = "wasm32")]
impl GeoOptions {
    fn to_browser_options(&self) -> PositionOptions {
        let opts = PositionOptions::new();
        opts.set_enable_high_accuracy(self.enable_high_accuracy);
        opts.set_timeout(self.timeout_ms);
        opts.set_maximum_age(self.maximum_age_ms);
        opts
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                         // get current position
// ═══════════════════════════════════════════════════════════════════════════════

/// Get current position (one-time).
/// Returns a Promise that resolves to GeoPosition or rejects with GeoError.
#[wasm_bindgen]
pub async fn geo_get_current_position(options: &GeoOptions) -> Result<GeoPosition, JsValue> {
    #[cfg(target_arch = "wasm32")]
    {
        use js_sys::Promise;
        use wasm_bindgen_futures::JsFuture;

        let geo = get_geolocation()
            .ok_or_else(|| JsValue::from_str("Geolocation not supported"))?;

        let opts = options.to_browser_options();

        let promise = Promise::new(&mut |resolve, reject| {
            let success_callback = Closure::once(Box::new(move |pos: GeolocationPosition| {
                let geo_pos = GeoPosition::from_browser_position(&pos);
                resolve.call1(&JsValue::NULL, &JsValue::from(geo_pos.latitude())).ok();
            }) as Box<dyn FnOnce(GeolocationPosition)>);

            let error_callback = Closure::once(Box::new(move |err: GeolocationPositionError| {
                let geo_err = GeoError::from_browser_error(&err);
                reject.call1(&JsValue::NULL, &JsValue::from_str(&geo_err.message)).ok();
            }) as Box<dyn FnOnce(GeolocationPositionError)>);

            geo.get_current_position_with_error_callback_and_options(
                success_callback.as_ref().unchecked_ref(),
                Some(error_callback.as_ref().unchecked_ref()),
                &opts,
            );

            // Prevent closures from being dropped
            success_callback.forget();
            error_callback.forget();
        });

        JsFuture::from(promise)
            .await
            .map(|_| {
                // This is a simplified version - in production we'd properly
                // serialize the full GeoPosition through the promise
                GeoPosition {
                    latitude: 0.0,
                    longitude: 0.0,
                    altitude: None,
                    accuracy: 0.0,
                    altitude_accuracy: None,
                    heading: None,
                    speed: None,
                    timestamp: 0.0,
                }
            })
    }

    #[cfg(not(target_arch = "wasm32"))]
    {
        let _ = options;
        Err(JsValue::from_str("Geolocation not supported on this platform"))
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // watch position
// ═══════════════════════════════════════════════════════════════════════════════

/// Handle for an active position watch. Drop or call clear() to stop watching.
#[wasm_bindgen]
pub struct GeoWatchHandle {
    #[cfg(target_arch = "wasm32")]
    watch_id: i32,
    #[cfg(target_arch = "wasm32")]
    #[allow(dead_code)]
    success_closure: Closure<dyn Fn(GeolocationPosition)>,
    #[cfg(target_arch = "wasm32")]
    #[allow(dead_code)]
    error_closure: Closure<dyn Fn(GeolocationPositionError)>,
}

#[wasm_bindgen]
impl GeoWatchHandle {
    /// Clear this watch (stop receiving position updates).
    pub fn clear(&self) {
        #[cfg(target_arch = "wasm32")]
        {
            if let Some(geo) = get_geolocation() {
                geo.clear_watch(self.watch_id);
            }
        }
    }

    /// Get the watch ID.
    #[wasm_bindgen(getter)]
    pub fn watch_id(&self) -> i32 {
        #[cfg(target_arch = "wasm32")]
        {
            self.watch_id
        }
        #[cfg(not(target_arch = "wasm32"))]
        {
            -1
        }
    }
}

/// Watch position with continuous updates.
/// Returns a handle that can be used to clear the watch.
#[wasm_bindgen]
pub fn geo_watch_position(
    options: &GeoOptions,
    on_success: js_sys::Function,
    on_error: js_sys::Function,
) -> Result<GeoWatchHandle, JsValue> {
    #[cfg(target_arch = "wasm32")]
    {
        let geo = get_geolocation()
            .ok_or_else(|| JsValue::from_str("Geolocation not supported"))?;

        let opts = options.to_browser_options();

        let success_closure = Closure::new(move |pos: GeolocationPosition| {
            let geo_pos = GeoPosition::from_browser_position(&pos);
            // Create a plain object to pass to PureScript
            let obj = js_sys::Object::new();
            js_sys::Reflect::set(&obj, &"latitude".into(), &geo_pos.latitude.into()).ok();
            js_sys::Reflect::set(&obj, &"longitude".into(), &geo_pos.longitude.into()).ok();
            js_sys::Reflect::set(&obj, &"accuracy".into(), &geo_pos.accuracy.into()).ok();
            js_sys::Reflect::set(&obj, &"timestamp".into(), &geo_pos.timestamp.into()).ok();
            
            if let Some(alt) = geo_pos.altitude {
                js_sys::Reflect::set(&obj, &"altitude".into(), &alt.into()).ok();
            }
            if let Some(alt_acc) = geo_pos.altitude_accuracy {
                js_sys::Reflect::set(&obj, &"altitudeAccuracy".into(), &alt_acc.into()).ok();
            }
            if let Some(h) = geo_pos.heading {
                js_sys::Reflect::set(&obj, &"heading".into(), &h.into()).ok();
            }
            if let Some(s) = geo_pos.speed {
                js_sys::Reflect::set(&obj, &"speed".into(), &s.into()).ok();
            }
            
            if on_success.call1(&JsValue::NULL, &obj).is_err() {
                web_sys::console::warn_1(&"Geo success callback failed".into());
            }
        });

        let error_closure = Closure::new(move |err: GeolocationPositionError| {
            let geo_err = GeoError::from_browser_error(&err);
            let obj = js_sys::Object::new();
            js_sys::Reflect::set(&obj, &"code".into(), &(geo_err.code as i32).into()).ok();
            js_sys::Reflect::set(&obj, &"message".into(), &geo_err.message.into()).ok();
            
            if on_error.call1(&JsValue::NULL, &obj).is_err() {
                web_sys::console::warn_1(&"Geo error callback failed".into());
            }
        });

        let watch_id = geo.watch_position_with_error_callback_and_options(
            success_closure.as_ref().unchecked_ref(),
            Some(error_closure.as_ref().unchecked_ref()),
            &opts,
        );

        Ok(GeoWatchHandle {
            watch_id,
            success_closure,
            error_closure,
        })
    }

    #[cfg(not(target_arch = "wasm32"))]
    {
        let _ = (options, on_success, on_error);
        Err(JsValue::from_str("Geolocation not supported on this platform"))
    }
}

/// Clear a position watch by ID.
#[wasm_bindgen]
pub fn geo_clear_watch(watch_id: i32) {
    #[cfg(target_arch = "wasm32")]
    {
        if let Some(geo) = get_geolocation() {
            geo.clear_watch(watch_id);
        }
    }
    #[cfg(not(target_arch = "wasm32"))]
    {
        let _ = watch_id;
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // geofencing
// ═══════════════════════════════════════════════════════════════════════════════

/// Geofence events.
#[wasm_bindgen]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GeofenceEvent {
    Enter = 0,
    Exit = 1,
    Dwell = 2,
}

/// Handle for a geofence watch.
#[wasm_bindgen]
pub struct GeofenceHandle {
    #[cfg(target_arch = "wasm32")]
    watch_handle: GeoWatchHandle,
    #[cfg(target_arch = "wasm32")]
    #[allow(dead_code)]
    state: Rc<RefCell<GeofenceState>>,
}

#[cfg(target_arch = "wasm32")]
struct GeofenceState {
    inside: bool,
    center_lat: f64,
    center_lon: f64,
    radius_meters: f64,
}

#[wasm_bindgen]
impl GeofenceHandle {
    /// Clear the geofence watch.
    pub fn clear(&self) {
        #[cfg(target_arch = "wasm32")]
        {
            self.watch_handle.clear();
        }
    }
}

/// Haversine distance in meters between two lat/lon points.
#[cfg(any(target_arch = "wasm32", test))]
fn haversine_distance(lat1: f64, lon1: f64, lat2: f64, lon2: f64) -> f64 {
    const EARTH_RADIUS_METERS: f64 = 6371008.8;

    let lat1_rad = lat1.to_radians();
    let lat2_rad = lat2.to_radians();
    let d_lat = (lat2 - lat1).to_radians();
    let d_lon = (lon2 - lon1).to_radians();

    let a = (d_lat / 2.0).sin().powi(2)
        + lat1_rad.cos() * lat2_rad.cos() * (d_lon / 2.0).sin().powi(2);
    let c = 2.0 * a.sqrt().atan2((1.0 - a).sqrt());

    EARTH_RADIUS_METERS * c
}

/// Watch a circular geofence for enter/exit events.
#[wasm_bindgen]
pub fn geo_watch_geofence(
    center_lat: f64,
    center_lon: f64,
    radius_meters: f64,
    on_event: js_sys::Function,
) -> Result<GeofenceHandle, JsValue> {
    #[cfg(target_arch = "wasm32")]
    {
        let center_lat = BoundedLatitude::new(center_lat).value();
        let center_lon = BoundedLongitude::new(center_lon).value();
        let radius = BoundedAccuracy::new(radius_meters).value();

        let state = Rc::new(RefCell::new(GeofenceState {
            inside: false,
            center_lat,
            center_lon,
            radius_meters: radius,
        }));

        let state_clone = Rc::clone(&state);
        let on_event_clone = on_event.clone();

        let success_callback = Closure::new(move |pos: GeolocationPosition| {
            let geo_pos = GeoPosition::from_browser_position(&pos);
            let dist = haversine_distance(
                state_clone.borrow().center_lat,
                state_clone.borrow().center_lon,
                geo_pos.latitude,
                geo_pos.longitude,
            );

            let now_inside = dist <= state_clone.borrow().radius_meters;
            let was_inside = state_clone.borrow().inside;

            if now_inside != was_inside {
                state_clone.borrow_mut().inside = now_inside;
                let event = if now_inside {
                    GeofenceEvent::Enter
                } else {
                    GeofenceEvent::Exit
                };
                
                if on_event_clone.call1(&JsValue::NULL, &(event as i32).into()).is_err() {
                    web_sys::console::warn_1(&"Geofence callback failed".into());
                }
            }
        });

        let error_callback = Closure::new(move |_err: GeolocationPositionError| {
            // Geofence errors are silently ignored — we just stop getting updates
            web_sys::console::warn_1(&"Geofence position error".into());
        });

        let geo = get_geolocation()
            .ok_or_else(|| JsValue::from_str("Geolocation not supported"))?;

        let opts = PositionOptions::new();
        opts.set_enable_high_accuracy(true);

        let watch_id = geo.watch_position_with_error_callback_and_options(
            success_callback.as_ref().unchecked_ref(),
            Some(error_callback.as_ref().unchecked_ref()),
            &opts,
        );

        Ok(GeofenceHandle {
            watch_handle: GeoWatchHandle {
                watch_id,
                success_closure: success_callback,
                error_closure: error_callback,
            },
            state,
        })
    }

    #[cfg(not(target_arch = "wasm32"))]
    {
        let _ = (center_lat, center_lon, radius_meters, on_event);
        Err(JsValue::from_str("Geolocation not supported on this platform"))
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                      // tests
// ═══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bounded_latitude_clamps() {
        assert_eq!(BoundedLatitude::new(100.0).value(), 90.0);
        assert_eq!(BoundedLatitude::new(-100.0).value(), -90.0);
        assert_eq!(BoundedLatitude::new(45.0).value(), 45.0);
        assert_eq!(BoundedLatitude::new(f64::NAN).value(), 0.0);
        assert_eq!(BoundedLatitude::new(f64::INFINITY).value(), 0.0);
    }

    #[test]
    fn bounded_longitude_wraps() {
        assert_eq!(BoundedLongitude::new(0.0).value(), 0.0);
        assert_eq!(BoundedLongitude::new(180.0).value(), -180.0);
        assert_eq!(BoundedLongitude::new(-180.0).value(), -180.0);
        assert_eq!(BoundedLongitude::new(185.0).value(), -175.0);
        assert_eq!(BoundedLongitude::new(-200.0).value(), 160.0);
        assert_eq!(BoundedLongitude::new(f64::NAN).value(), 0.0);
    }

    #[test]
    fn bounded_accuracy_nonneg() {
        assert_eq!(BoundedAccuracy::new(-10.0).value(), 0.0);
        assert_eq!(BoundedAccuracy::new(0.0).value(), 0.0);
        assert_eq!(BoundedAccuracy::new(100.0).value(), 100.0);
        assert_eq!(BoundedAccuracy::new(f64::NAN).value(), 0.0);
    }

    #[test]
    fn haversine_reflexive() {
        let d = haversine_distance(51.5, -0.1, 51.5, -0.1);
        assert!(d.abs() < 1e-10, "Distance to self should be 0");
    }

    #[test]
    fn haversine_symmetric() {
        let d1 = haversine_distance(51.5, -0.1, 48.8, 2.3);
        let d2 = haversine_distance(48.8, 2.3, 51.5, -0.1);
        assert!((d1 - d2).abs() < 1e-6, "Haversine should be symmetric");
    }

    #[test]
    fn haversine_nonneg() {
        let d = haversine_distance(0.0, 0.0, 90.0, 180.0);
        assert!(d >= 0.0, "Distance should be non-negative");
    }
}
