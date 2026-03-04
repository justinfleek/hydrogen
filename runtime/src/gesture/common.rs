//! Common types for gesture recognition.
//!
//! Provides foundational types used across all gesture modules:
//! - Handle: Generational handle for resource management
//! - Point/Point3D: 2D and 3D coordinates
//! - HandleTable: Sparse storage with ABA protection

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // generational handle
// ═══════════════════════════════════════════════════════════════════════════════

/// Generational handle - prevents ABA problems in async callback dispatch.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Handle {
    pub index: u32,
    pub generation: u32,
}

impl Handle {
    pub const INVALID: Handle = Handle {
        index: u32::MAX,
        generation: 0,
    };

    pub fn is_valid(&self) -> bool {
        self.index != u32::MAX
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // point types
// ═══════════════════════════════════════════════════════════════════════════════

/// A 2D point with f64 coordinates.
#[derive(Clone, Copy, Debug, Default)]
pub struct Point {
    pub x: f64,
    pub y: f64,
}

impl Point {
    pub fn new(x: f64, y: f64) -> Self {
        Point { x, y }
    }

    pub fn distance_to(&self, other: &Point) -> f64 {
        let dx = other.x - self.x;
        let dy = other.y - self.y;
        (dx * dx + dy * dy).sqrt()
    }

    pub fn sub(&self, other: &Point) -> Point {
        Point {
            x: self.x - other.x,
            y: self.y - other.y,
        }
    }

    pub fn add(&self, other: &Point) -> Point {
        Point {
            x: self.x + other.x,
            y: self.y + other.y,
        }
    }
}

/// A 3D point for VR/spatial gestures.
#[derive(Clone, Copy, Debug, Default)]
pub struct Point3D {
    pub x: f64,
    pub y: f64,
    pub z: f64,
}

impl Point3D {
    pub fn new(x: f64, y: f64, z: f64) -> Self {
        Point3D { x, y, z }
    }

    pub fn distance_to(&self, other: &Point3D) -> f64 {
        let dx = other.x - self.x;
        let dy = other.y - self.y;
        let dz = other.z - self.z;
        (dx * dx + dy * dy + dz * dz).sqrt()
    }

    pub fn magnitude(&self) -> f64 {
        (self.x * self.x + self.y * self.y + self.z * self.z).sqrt()
    }

    pub fn normalized(&self) -> Point3D {
        let mag = self.magnitude();
        if mag > 0.0 {
            Point3D {
                x: self.x / mag,
                y: self.y / mag,
                z: self.z / mag,
            }
        } else {
            Point3D::default()
        }
    }

    pub fn dot(&self, other: &Point3D) -> f64 {
        self.x * other.x + self.y * other.y + self.z * other.z
    }

    pub fn cross(&self, other: &Point3D) -> Point3D {
        Point3D {
            x: self.y * other.z - self.z * other.y,
            y: self.z * other.x - self.x * other.z,
            z: self.x * other.y - self.y * other.x,
        }
    }
}

/// A timestamped 2D point for velocity tracking.
#[derive(Clone, Copy, Debug)]
pub struct TimestampedPoint {
    pub point: Point,
    pub time_ms: f64,
}

/// A timestamped 3D point for VR velocity tracking.
#[derive(Clone, Copy, Debug)]
pub struct TimestampedPoint3D {
    pub point: Point3D,
    pub time_ms: f64,
}

/// Two-finger gesture data (center, distance, angle).
#[derive(Clone, Copy, Debug)]
pub struct TwoFingerData {
    pub center: Point,
    pub distance: f64,
    pub angle_degrees: f64,
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // handle table
// ═══════════════════════════════════════════════════════════════════════════════

struct HandleEntry<T> {
    value: T,
    generation: u32,
    alive: bool,
}

/// Sparse storage with generational indices. O(1) operations with ABA protection.
pub struct HandleTable<T> {
    entries: Vec<HandleEntry<T>>,
    free_list: Vec<u32>,
}

impl<T> HandleTable<T> {
    pub fn new() -> Self {
        HandleTable {
            entries: Vec::new(),
            free_list: Vec::new(),
        }
    }

    pub fn insert(&mut self, value: T) -> Handle {
        if let Some(index) = self.free_list.pop() {
            let entry = &mut self.entries[index as usize];
            entry.value = value;
            entry.alive = true;
            Handle {
                index,
                generation: entry.generation,
            }
        } else {
            let index = self.entries.len() as u32;
            self.entries.push(HandleEntry {
                value,
                generation: 0,
                alive: true,
            });
            Handle {
                index,
                generation: 0,
            }
        }
    }

    pub fn remove(&mut self, handle: Handle) -> Option<T>
    where
        T: Default,
    {
        if !self.is_valid(handle) {
            return None;
        }
        let entry = &mut self.entries[handle.index as usize];
        entry.alive = false;
        entry.generation = entry.generation.wrapping_add(1);
        self.free_list.push(handle.index);
        Some(std::mem::take(&mut entry.value))
    }

    pub fn is_valid(&self, handle: Handle) -> bool {
        let index = handle.index as usize;
        index < self.entries.len()
            && self.entries[index].alive
            && self.entries[index].generation == handle.generation
    }

    pub fn get(&self, handle: Handle) -> Option<&T> {
        if self.is_valid(handle) {
            Some(&self.entries[handle.index as usize].value)
        } else {
            None
        }
    }

    pub fn get_mut(&mut self, handle: Handle) -> Option<&mut T> {
        if self.is_valid(handle) {
            Some(&mut self.entries[handle.index as usize].value)
        } else {
            None
        }
    }
}

impl<T> Default for HandleTable<T> {
    fn default() -> Self {
        Self::new()
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // utility functions
// ═══════════════════════════════════════════════════════════════════════════════

/// Compute velocity from a series of timestamped points.
pub fn compute_velocity(samples: &[TimestampedPoint]) -> Point {
    if samples.len() < 2 {
        return Point::default();
    }
    let first = &samples[0];
    let last = &samples[samples.len() - 1];
    let dt_seconds = (last.time_ms - first.time_ms) / 1000.0;
    if dt_seconds <= 0.0 {
        return Point::default();
    }
    Point {
        x: (last.point.x - first.point.x) / dt_seconds,
        y: (last.point.y - first.point.y) / dt_seconds,
    }
}

/// Compute 3D velocity from timestamped points.
pub fn compute_velocity_3d(samples: &[TimestampedPoint3D]) -> Point3D {
    if samples.len() < 2 {
        return Point3D::default();
    }
    let first = &samples[0];
    let last = &samples[samples.len() - 1];
    let dt_seconds = (last.time_ms - first.time_ms) / 1000.0;
    if dt_seconds <= 0.0 {
        return Point3D::default();
    }
    Point3D {
        x: (last.point.x - first.point.x) / dt_seconds,
        y: (last.point.y - first.point.y) / dt_seconds,
        z: (last.point.z - first.point.z) / dt_seconds,
    }
}

/// Normalize an angle to [-180, 180].
pub fn normalize_angle(mut angle: f64) -> f64 {
    while angle > 180.0 {
        angle -= 360.0;
    }
    while angle < -180.0 {
        angle += 360.0;
    }
    angle
}

/// Clamp a value to a range.
pub fn clamp(value: f64, min: f64, max: f64) -> f64 {
    if value < min {
        min
    } else if value > max {
        max
    } else {
        value
    }
}

/// Swipe direction (used by multiple modules).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SwipeDirection {
    Up,
    Down,
    Left,
    Right,
}

/// Detect swipe direction from delta.
pub fn detect_swipe_direction(dx: f64, dy: f64) -> SwipeDirection {
    if dx.abs() > dy.abs() {
        if dx > 0.0 {
            SwipeDirection::Right
        } else {
            SwipeDirection::Left
        }
    } else if dy > 0.0 {
        SwipeDirection::Down
    } else {
        SwipeDirection::Up
    }
}

/// Axis for locking gestures.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Axis {
    X,
    Y,
}

/// 3D axis.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Axis3D {
    X,
    Y,
    Z,
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                           // haptic feedback
// ═══════════════════════════════════════════════════════════════════════════════

/// Haptic feedback pattern to emit with gesture actions.
#[derive(Clone, Debug)]
pub struct HapticFeedback {
    /// Vibration intensity (0.0 - 1.0, bounded).
    pub intensity: f64,
    /// Duration in milliseconds.
    pub duration_ms: u32,
    /// Pattern type.
    pub pattern: HapticPattern,
}

impl HapticFeedback {
    pub fn tap() -> Self {
        HapticFeedback {
            intensity: 0.5,
            duration_ms: 10,
            pattern: HapticPattern::Tap,
        }
    }
    pub fn light_tap() -> Self {
        HapticFeedback {
            intensity: 0.2,
            duration_ms: 5,
            pattern: HapticPattern::Tap,
        }
    }
    pub fn heavy_tap() -> Self {
        HapticFeedback {
            intensity: 0.8,
            duration_ms: 15,
            pattern: HapticPattern::Tap,
        }
    }
    pub fn success() -> Self {
        HapticFeedback {
            intensity: 0.6,
            duration_ms: 100,
            pattern: HapticPattern::Success,
        }
    }
    pub fn error() -> Self {
        HapticFeedback {
            intensity: 0.7,
            duration_ms: 200,
            pattern: HapticPattern::Error,
        }
    }
    pub fn hold(intensity: f64) -> Self {
        HapticFeedback {
            intensity: clamp(intensity, 0.0, 1.0),
            duration_ms: 0,
            pattern: HapticPattern::Hold,
        }
    }
}

/// Type of haptic pattern.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum HapticPattern {
    /// Short click/tap.
    Tap,
    /// Sustained vibration (duration_ms = 0 means until stopped).
    Hold,
    /// Building intensity over duration.
    Ramp,
    /// Achievement/confirmation pattern.
    Success,
    /// Rejection/error pattern.
    Error,
    /// Subtle continuous texture feedback.
    Texture,
    /// Selection tick (like scrolling through a picker).
    SelectionTick,
    /// Impact based on velocity/force.
    Impact { force: f64 },
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // elevation
// ═══════════════════════════════════════════════════════════════════════════════

/// Elevation level for z-depth aware gestures.
#[derive(Clone, Copy, Debug, Default)]
pub struct Elevation {
    /// Z-depth layer (0 = base, higher = closer to user).
    pub level: u32,
    /// Whether this elevation casts a shadow.
    pub casts_shadow: bool,
    /// Inertia multiplier (higher elevation = heavier feel).
    pub inertia_factor: f64,
}

impl Elevation {
    pub fn base() -> Self {
        Elevation {
            level: 0,
            casts_shadow: false,
            inertia_factor: 1.0,
        }
    }
    pub fn raised() -> Self {
        Elevation {
            level: 1,
            casts_shadow: true,
            inertia_factor: 1.1,
        }
    }
    pub fn floating() -> Self {
        Elevation {
            level: 2,
            casts_shadow: true,
            inertia_factor: 1.2,
        }
    }
    pub fn modal() -> Self {
        Elevation {
            level: 3,
            casts_shadow: true,
            inertia_factor: 1.3,
        }
    }
}

/// Target element for a gesture with elevation awareness.
#[derive(Clone, Debug)]
pub struct GestureTarget {
    pub handle: Handle,
    pub elevation: Elevation,
    pub hit_point: Point,
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // quaternion
// ═════════════════════════════════════════════════════════════════════���═════════

/// Quaternion for 3D rotations (VR/XR).
#[derive(Clone, Copy, Debug)]
pub struct Quaternion {
    pub x: f64,
    pub y: f64,
    pub z: f64,
    pub w: f64,
}

impl Default for Quaternion {
    fn default() -> Self {
        Quaternion {
            x: 0.0,
            y: 0.0,
            z: 0.0,
            w: 1.0,
        } // Identity
    }
}

impl Quaternion {
    pub fn identity() -> Self {
        Quaternion::default()
    }

    pub fn from_euler(pitch: f64, yaw: f64, roll: f64) -> Self {
        let (sp, cp) = (pitch * 0.5).sin_cos();
        let (sy, cy) = (yaw * 0.5).sin_cos();
        let (sr, cr) = (roll * 0.5).sin_cos();
        Quaternion {
            x: sr * cp * cy - cr * sp * sy,
            y: cr * sp * cy + sr * cp * sy,
            z: cr * cp * sy - sr * sp * cy,
            w: cr * cp * cy + sr * sp * sy,
        }
    }

    pub fn magnitude(&self) -> f64 {
        (self.x * self.x + self.y * self.y + self.z * self.z + self.w * self.w).sqrt()
    }

    pub fn normalized(&self) -> Quaternion {
        let mag = self.magnitude();
        if mag > 0.0 {
            Quaternion {
                x: self.x / mag,
                y: self.y / mag,
                z: self.z / mag,
                w: self.w / mag,
            }
        } else {
            Quaternion::identity()
        }
    }
}
