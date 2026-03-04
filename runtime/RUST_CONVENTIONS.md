# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#                                              // hydrogen // rust // conventions
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## Purpose

This document defines how to write Rust code for the Hydrogen runtime. It ensures
consistency across compactions and prevents future AI sessions from recreating
incorrect patterns.

**Read this BEFORE writing any Rust code.**

## Core Architecture: libevring State Machine Pattern

All event handling follows the pattern from `straylight-software/libevring`:

```
step :: State -> Event -> (State, [Action])
```

Where:
- **State** = Explicit sum types (Rust enums) representing all possible states
- **Event** = What happened (input from browser/device/user)
- **Action** = What to do (output to PureScript/haptics/renderer)
- **step** = Pure function, no side effects, deterministic

### Example from libevring (Haskell):

```haskell
data Event = Event
  { eventHandle   :: !Handle
  , eventType     :: !OperationType
  , eventResult   :: !Int64
  , eventData     :: !ByteString
  , eventUserData :: !Word64
  }

data Operation = Operation
  { opHandle   :: !Handle
  , opType     :: !OperationType
  , opUserData :: !Word64
  , opParams   :: !OperationParams
  }
```

### Translated to Rust:

```rust
/// Input event (what happened)
pub enum GestureInput {
    PointerDown { position: Point, time_ms: f64, pointer_id: i32 },
    PointerMove { position: Point, time_ms: f64, pointer_id: i32 },
    PointerUp { position: Point, time_ms: f64, pointer_id: i32 },
    // ...
}

/// Output action (what to do)
pub enum PanAction {
    Start(PanStateData),
    Move(PanStateData),
    End(PanStateData),
}

/// Pure state machine step
pub fn pan_step(state: PanState, input: &GestureInput, config: &PanConfig) -> PanStepResult {
    match (&state, input) {
        // Pattern match on (current_state, input_event)
        // Return (new_state, [actions])
    }
}
```

## Generational Handles

From libevring's `handle.h` - prevents use-after-free in async contexts:

```rust
pub struct Handle {
    pub index: u32,
    pub generation: u32,
}

impl Handle {
    pub const INVALID: Handle = Handle { index: u32::MAX, generation: 0 };
}
```

When a resource is freed and its slot reused, the generation increments,
invalidating any stale handles that might still exist in closures.

## FORBIDDEN PATTERNS

### ❌ NEVER use `let _ =` to ignore Results

```rust
// FORBIDDEN - hides errors
let _ = element.set_attribute("class", "foo");

// CORRECT - propagate error
element.set_attribute("class", "foo")?;

// CORRECT - explicit handling if you truly don't care
if element.set_attribute("class", "foo").is_err() {
    log::warn!("Failed to set class attribute");
}
```

### ❌ NEVER use JavaScript anywhere

```rust
// FORBIDDEN
#[wasm_bindgen(inline_js = "export function foo() { ... }")]

// CORRECT - use web-sys
use web_sys::Element;
element.set_attribute("class", "foo")?;
```

### ❌ NEVER use unwrap/expect in production code

```rust
// FORBIDDEN
let element = document.get_element_by_id("foo").unwrap();

// CORRECT
let element = document
    .get_element_by_id("foo")
    .ok_or_else(|| JsValue::from_str("Element 'foo' not found"))?;
```

## Required Integration Points

### 1. Haptic Feedback

Every gesture action should include haptic descriptor:

```rust
pub struct HapticPattern {
    /// Vibration intensity (0.0 - 1.0)
    pub intensity: f64,
    /// Duration in milliseconds
    pub duration_ms: u32,
    /// Pattern type
    pub pattern: HapticType,
}

pub enum HapticType {
    Tap,           // Short click
    Hold,          // Sustained vibration
    Ramp,          // Building intensity
    Success,       // Achievement pattern
    Error,         // Rejection pattern
    Texture,       // Subtle continuous feedback
}

pub enum PanAction {
    Start { data: PanStateData, haptic: HapticPattern },
    Move { data: PanStateData, haptic: Option<HapticPattern> },
    End { data: PanStateData, haptic: HapticPattern },
}
```

### 2. Elevation/Z-Depth

Gestures operate on elements with elevation:

```rust
pub struct GestureTarget {
    /// Element handle
    pub handle: Handle,
    /// Z-depth (elevation layer)
    pub elevation: u32,
    /// Whether gesture should "feel" heavier at higher elevation
    pub elevation_affects_inertia: bool,
}
```

### 3. 3D/Spatial (VR/XR)

For VR gestures, use Point3D and quaternions:

```rust
pub struct Point3D {
    pub x: f64,
    pub y: f64,
    pub z: f64,
}

pub struct Quaternion {
    pub x: f64,
    pub y: f64,
    pub z: f64,
    pub w: f64,
}

pub struct HandPose {
    pub position: Point3D,
    pub rotation: Quaternion,
    pub fingers: [FingerPose; 5],
}
```

### 4. Lean4 Proof Integration

Bounded types should have Lean4 proofs. Example structure:

```
runtime/
  src/
    gesture/
      mod.rs
      common.rs
      touch.rs
      ...
  proofs/
    Gesture/
      Bounds.lean      -- Proves all values stay in bounds
      Invariants.lean  -- Proves state machine invariants
```

Rust types with bounds:

```rust
/// Scale factor, proven bounded in Lean4
/// See: proofs/Gesture/Bounds.lean#PinchScale
pub struct BoundedScale {
    value: f64,  // Invariant: 0.1 <= value <= 10.0
}

impl BoundedScale {
    pub fn new(value: f64) -> Self {
        BoundedScale {
            value: value.clamp(0.1, 10.0)
        }
    }
}
```

## File Size Limit

**500 lines maximum per file.**

If a module grows beyond 500 lines, split it:

```
gesture/
  mod.rs          -- Re-exports only (~30 lines)
  common.rs       -- Shared types (~300 lines)
  touch.rs        -- Pan, Pinch, Rotate (~400 lines)
  motion.rs       -- Shake, Tilt, Flip (~300 lines)
  sequence.rs     -- Konami, Spiral, Rhythm (~400 lines)
  vr.rs           -- Hand tracking, gaze (~400 lines)
  shape.rs        -- Shape recognition (~300 lines)
```

## Module Structure Template

```rust
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                                    // hydrogen // [module] // wasm
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! # [Module Name]
//!
//! [Brief description of what this module does]
//!
//! ## State Machine
//!
//! ```text
//! step :: State -> Event -> (State, [Action])
//! ```
//!
//! ## Integration
//!
//! - Haptics: [How this module uses haptic feedback]
//! - Elevation: [How this module interacts with z-depth]
//! - Lean4: [Path to proofs, if any]

use crate::gesture::common::{Point, Handle, ...};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // [section name]
// ═══════════════════════════════════════════════════════════════════════════════

// ... code ...
```

## Testing

All state machines must have property tests:

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pan_idle_to_active() {
        let state = PanState::Idle;
        let input = GestureInput::PointerDown { 
            position: Point::new(100.0, 100.0),
            time_ms: 0.0,
            pointer_id: 0,
        };
        let result = pan_step(state, &input, &PanConfig::default());
        
        assert!(matches!(result.state, PanState::Active { .. }));
    }

    // Property: state machine never panics
    // Property: actions are only emitted on state transitions
    // Property: velocity is always finite (no NaN/Infinity)
}
```

## Reference Repositories

- `straylight-software/libevring` - Event ring pattern (Haskell + C++)
- `straylight-software/weapon-server-hs` - Production event handling
- `straylight-software/straylight-llm` - Gateway patterns

## Checklist Before Committing

- [ ] No `let _ =` patterns
- [ ] No JavaScript anywhere
- [ ] No `unwrap()` or `expect()` in non-test code
- [ ] All Results propagated with `?` or explicitly handled
- [ ] File under 500 lines
- [ ] Follows state machine pattern
- [ ] Haptic integration points defined
- [ ] Elevation awareness where applicable
- [ ] Straylight header comment style

────────────────────────────────────────────────────────────────────────────────
                                                              — Opus 4.5 // 2026
────────────────────────────────────────────────────────────────────────────────
