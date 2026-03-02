━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                               // 09 // gestural
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Gestural Pillar

Complete vocabulary for input handling across all modalities.

────────────────────────────────────────────────────────────────────────────────
                                                                      // overview
────────────────────────────────────────────────────────────────────────────────

## Implementation Status

- **Location**: `src/Hydrogen/Schema/Gestural/`
- **Files**: 31 PureScript modules
- **Lines**: ~10,971 total
- **Coverage**: 100% of specification

## Architecture

The Gestural pillar captures input as pure data across modalities:

- **Pointer** — Mouse, touch, stylus coordinates and state
- **Keyboard** — Keys, shortcuts, modifiers, navigation
- **Gesture** — Multi-touch: tap, swipe, pinch, rotate, pan, long-press
- **Focus** — Focus management and keyboard navigation
- **Hover** — Hover state and effects
- **Timing** — Input timing thresholds


────────────────────────────────────────────────────────────────────────────────
                                                                      // pointer
────────────────────────────────────────────────────────────────────────────────

## Pointer Types

Models the W3C Pointer Events specification with bounded types.

### MouseButton (Enum)

| Variant | W3C Index | Description |
|---------|-----------|-------------|
| `MouseLeft` | 0 | Main button (usually left click) |
| `MouseMiddle` | 1 | Auxiliary button (wheel/middle) |
| `MouseRight` | 2 | Secondary button (right click) |
| `MouseBack` | 3 | Fourth button (browser back) |
| `MouseForward` | 4 | Fifth button (browser forward) |

**Predicates:**
- `isPrimaryButton` — Left button (main action)
- `isSecondaryButton` — Right button (context menu)
- `isAuxiliaryButton` — Middle button

### PointerType (Enum)

| Variant | String | Description |
|---------|--------|-------------|
| `PointerMouse` | "mouse" | Mouse or trackpad |
| `PointerTouch` | "touch" | Finger touch |
| `PointerPen` | "pen" | Stylus or pen |
| `PointerUnknown` | — | Unknown device |

### Pressure (Atom)

```
Bounds: [0.0, 1.0], clamps
```

| Preset | Value | Description |
|--------|-------|-------------|
| `noPressure` | 0.0 | Hovering or not supported |
| `fullPressure` | 1.0 | Maximum pressure |

Mouse reports 0.5 when pressed, 0.0 otherwise.

### TiltX / TiltY (Atoms)

```
Bounds: [-90.0, 90.0] degrees, clamps
```

| Value | Meaning |
|-------|---------|
| 0 | Perpendicular to surface |
| Negative X | Tilted left |
| Positive X | Tilted right |
| Negative Y | Tilted toward user |
| Positive Y | Tilted away from user |

### Twist (Atom)

```
Bounds: [0.0, 360.0) degrees, wraps
```

Pen rotation around its axis (barrel rotation).

### PointerPosition (Molecule)

| Field | Description |
|-------|-------------|
| `clientX/Y` | Relative to viewport |
| `pageX/Y` | Relative to document (includes scroll) |
| `screenX/Y` | Relative to physical display |
| `offsetX/Y` | Relative to target element |

### PointerSize (Molecule)

| Field | Description |
|-------|-------------|
| `width` | Contact width in CSS pixels |
| `height` | Contact height in CSS pixels |

`pointPointer` preset: 1x1 (typical mouse).

### PointerState (Compound)

Complete pointer state combining all attributes:

| Field | Type | Description |
|-------|------|-------------|
| `pointerId` | Int | Unique pointer identifier |
| `pointerType` | PointerType | Device type |
| `position` | PointerPosition | All coordinates |
| `pressure` | Pressure | Applied force |
| `tiltX` | TiltX | Pen tilt X |
| `tiltY` | TiltY | Pen tilt Y |
| `twist` | Twist | Pen rotation |
| `size` | PointerSize | Contact area |
| `isPrimary` | Boolean | Primary in multi-touch |
| `buttons` | Int | Pressed buttons bitmask |
| `timestamp` | Maybe Number | Event time (ms) |

**Constructors:**
- `mousePointerState` — For mouse input
- `touchPointerState` — For touch input with pressure/size
- `penPointerState` — For pen with tilt/twist

────────────────────────────────────────────────────────────────────────────────
                                                                     // keyboard
────────────────────────────────────────────────────────────────────────────────

## Keyboard Types

Based on W3C UI Events KeyboardEvent specification.

### KeyCode (Atom)

Physical key code independent of keyboard layout (KeyboardEvent.code).

**Navigation Keys:**
`keyEnter`, `keyEscape`, `keyBackspace`, `keyTab`, `keySpace`, `keyDelete`,
`keyHome`, `keyEnd`, `keyPageUp`, `keyPageDown`, `keyInsert`

**Arrow Keys:**
`keyArrowUp`, `keyArrowDown`, `keyArrowLeft`, `keyArrowRight`

**Function Keys:**
`keyF1` through `keyF12`

**Letter Keys:**
`keyA` through `keyZ` (for vim/emacs commands)

**Number Keys:**
`key0` through `key9`

**Special Keys:**
`keyBracketLeft`, `keyBracketRight`, `keySemicolon`, `keyQuote`,
`keyBackquote`, `keySlash`, `keyBackslash`, `keyComma`, `keyPeriod`,
`keyMinus`, `keyEqual`

### ModifierState (Molecule)

| Field | Type | Description |
|-------|------|-------------|
| `ctrl` | Boolean | Control key |
| `alt` | Boolean | Alt/Option key |
| `shift` | Boolean | Shift key |
| `meta` | Boolean | Meta/Command/Win key |
| `capsLock` | Boolean | Caps Lock state |
| `numLock` | Boolean | Num Lock state |

**Presets:**
- `noModifiers` — All false
- `ctrlOnly`, `altOnly`, `shiftOnly`, `metaOnly`

**Queries:**
- `hasCtrlOrCmd` — Ctrl or Meta (platform-agnostic)
- `hasAnyModifier` — Any of Ctrl/Alt/Shift/Meta
- `onlyShift`, `onlyCtrl`, `onlyAlt`, `onlyMeta`
- `ctrlShift`, `altShift`, `ctrlAlt`, `ctrlAltShift`
- `hasPlatformModifier` — Primary modifier for platform

### Shortcut (Molecule)

Keyboard shortcut definition for matching events.

| Field | Type | Description |
|-------|------|-------------|
| `code` | KeyCode | Required key |
| `ctrl` | Boolean | Requires Ctrl |
| `alt` | Boolean | Requires Alt |
| `shift` | Boolean | Requires Shift |
| `meta` | Boolean | Requires Meta |

**Constructors:**
- `simpleShortcut` — Just a key, no modifiers
- `ctrlShortcut` — Ctrl+Key
- `ctrlShiftShortcut` — Ctrl+Shift+Key
- `altShortcut`, `altShiftShortcut`
- `metaShortcut`, `metaShiftShortcut`

**Common Shortcuts:**

| Shortcut | Keys | Action |
|----------|------|--------|
| `shortcutCopy` | Ctrl+C | Copy |
| `shortcutCut` | Ctrl+X | Cut |
| `shortcutPaste` | Ctrl+V | Paste |
| `shortcutUndo` | Ctrl+Z | Undo |
| `shortcutRedo` | Ctrl+Shift+Z | Redo |
| `shortcutRedoY` | Ctrl+Y | Redo (Windows) |
| `shortcutSelectAll` | Ctrl+A | Select All |
| `shortcutSave` | Ctrl+S | Save |
| `shortcutFind` | Ctrl+F | Find |
| `shortcutClose` | Ctrl+W | Close |
| `shortcutNew` | Ctrl+N | New |
| `shortcutOpen` | Ctrl+O | Open |

**Matching:**
- `matchesShortcut` — Exact modifier match
- `matchesShortcutLoose` — Ctrl/Meta interchangeable (cross-platform)

────────────────────────────────────────────────────────────────────────────────
                                                                      // gesture
────────────────────────────────────────────────────────────────────────────────

## Gesture Types

Multi-touch gesture recognition based on UIKit/Android state machine.

### GesturePhase (Enum)

| Variant | Description |
|---------|-------------|
| `Possible` | Evaluating, not yet recognized |
| `Began` | Gesture recognized and started |
| `Changed` | Gesture in progress, state updated |
| `Ended` | Gesture completed normally |
| `Cancelled` | Gesture interrupted externally |
| `Failed` | Touches did not match gesture |

**Predicates:**
- `isActive` — Began or Changed
- `isTerminal` — Ended, Cancelled, or Failed

### TapCount (Atom)

```
Bounds: [1, 3], clamps
```

| Preset | Value | Use Case |
|--------|-------|----------|
| `singleTap` | 1 | Standard selection |
| `doubleTap` | 2 | Zoom, select word |
| `tripleTap` | 3 | Select paragraph |

### TapState (Compound)

| Field | Type | Description |
|-------|------|-------------|
| `phase` | GesturePhase | Recognition phase |
| `count` | TapCount | Number of taps |
| `x` / `y` | Number | Tap position |
| `timestamp` | Number | Time of tap (ms) |
| `interval` | Number | Time between taps |

### SwipeDirection (Enum)

| Variant | Description |
|---------|-------------|
| `SwipeUp` | Upward swipe |
| `SwipeDown` | Downward swipe |
| `SwipeLeft` | Leftward swipe |
| `SwipeRight` | Rightward swipe |

**Helpers:**
- `isSwipeHorizontal`, `isSwipeVertical`
- `oppositeSwipe`
- `swipeDirectionFromDelta dx dy`

### SwipeVelocityThreshold (Atom)

```
Bounds: [0.1, 5.0] px/ms, clamps
Default: 0.5 px/ms (500 px/s)
```

### SwipeState (Compound)

| Field | Type | Description |
|-------|------|-------------|
| `phase` | GesturePhase | Recognition phase |
| `direction` | SwipeDirection | Detected direction |
| `startX/Y` | Number | Start position |
| `endX/Y` | Number | End position |
| `velocityX/Y` | Number | Velocity (px/ms) |
| `distance` | Number | Total distance |
| `duration` | Number | Duration (ms) |

### PinchConfig (Molecule)

| Field | Default | Description |
|-------|---------|-------------|
| `minScale` | 0.25 | Minimum scale (25%) |
| `maxScale` | 10.0 | Maximum scale (1000%) |
| `velocityThreshold` | 10.0 | Min velocity (px/s) |
| `distanceThreshold` | 5.0 | Min distance change (px) |

### PinchGesture (Compound)

| Field | Type | Description |
|-------|------|-------------|
| `phase` | GesturePhase | Recognition phase |
| `scale` | Number | Current scale (1.0 = no change) |
| `initialScale` | Number | Scale when started |
| `centerX/Y` | Number | Center between fingers |
| `initialDistance` | Number | Initial finger distance |
| `currentDistance` | Number | Current finger distance |
| `velocity` | Number | Scale velocity (scale/s) |

**Operations:**
- `beginPinch x1 y1 x2 y2 currentScale`
- `updatePinch x1 y1 x2 y2 dt`
- `endPinch`, `cancelPinch`
- `clampScale`, `scaleProgress`

### RotateGesture (Compound)

Two-finger rotation gesture tracking rotation angle and velocity.

### PanGesture (Compound)

Continuous dragging gesture with position, velocity, and inertia.

### LongPressGesture (Compound)

Press-and-hold gesture with configurable duration threshold.

────────────────────────────────────────────────────────────────────────────────
                                                                       // timing
────────────────────────────────────────────────────────────────────────────────

## Timing Types

Temporal atoms for gesture recognition and multi-click detection.

### ClickCount (Atom)

```
Bounds: [1, 10], clamps
```

| Preset | Value | Use Case |
|--------|-------|----------|
| `singleClick` | 1 | Standard action |
| `doubleClick` | 2 | Select word, zoom |
| `tripleClick` | 3 | Select paragraph |

**Operations:**
- `incrementClick` — Add one to count
- `resetClickCount` — Back to 1

### HoldDuration (Atom)

```
Bounds: [0, 5000] ms, clamps
```

| Preset | Value | Use Case |
|--------|-------|----------|
| `zeroHold` | 0 | Instant release |
| `shortHold` | 300ms | Preview, tooltip |
| `longHold` | 500ms | Context menu, drag |

**Operations:**
- `addHoldTime delta` — Accumulate hold
- `isLongHold` — > 500ms?

### TapInterval (Atom)

```
Bounds: [0, 1000] ms, clamps
```

Maximum time between taps for multi-tap detection.

| Preset | Value | Audience |
|--------|-------|----------|
| `fastTapInterval` | 200ms | Power users |
| `defaultTapInterval` | 300ms | Most users |
| `slowTapInterval` | 500ms | Accessibility |

### TimingState (Molecule)

Complete timing state for composite gesture detection.

| Field | Type | Description |
|-------|------|-------------|
| `clicks` | ClickCount | Current consecutive clicks |
| `holdStart` | Maybe Number | When hold began |
| `holdDuration` | HoldDuration | Accumulated hold time |
| `lastClickTime` | Maybe Number | Last click timestamp |
| `tapInterval` | TapInterval | Multi-tap threshold |
| `currentTime` | Number | Current timestamp |

**Operations:**
- `recordClick timestamp` — Record click, update count
- `recordHoldStart timestamp` — Begin hold tracking
- `recordHoldEnd timestamp` — End hold, calculate duration
- `updateHold timestamp` — Update during hold
- `isMultiClick` — 2+ clicks?
- `isHolding` — Currently held?

────────────────────────────────────────────────────────────────────────────────
                                                                   // philosophy
────────────────────────────────────────────────────────────────────────────────

## Design Philosophy

### Input as Pure Data

Every input event is captured as pure data — no callbacks, no imperative event
handlers. An AI agent can reason about gestures algebraically:

```purescript
-- Gesture recognition is a pure function
recognizeSwipe :: Array PointerState -> Maybe SwipeState

-- Shortcut matching is deterministic
matchesShortcut :: Shortcut -> KeyEvent -> Boolean
```

### Cross-Platform Abstraction

The Gestural pillar abstracts over platform differences:

- **Mouse vs Touch vs Pen** — Unified through `PointerType`
- **Ctrl vs Cmd** — `hasCtrlOrCmd` handles both
- **Double-tap vs Double-click** — Same `ClickCount` / `TapCount`

### Bounded Timing

All timing atoms have explicit bounds to prevent edge cases:

| Atom | Min | Max | Behavior |
|------|-----|-----|----------|
| Pressure | 0.0 | 1.0 | clamps |
| TiltX/Y | -90° | 90° | clamps |
| Twist | 0° | 360° | wraps |
| ClickCount | 1 | 10 | clamps |
| HoldDuration | 0 | 5000ms | clamps |
| TapInterval | 0 | 1000ms | clamps |

### Gesture State Machine

All gestures follow the UIKit/Android state machine model:

```
Possible → Began → Changed → Ended
                ↘         ↗
                 Cancelled
                ↗
             Failed
```

This ensures consistent behavior across gesture types and platforms.

### Accessibility First

Timing presets include accessibility variants:

- `slowTapInterval` (500ms) for users who need more time
- `shortHold` (300ms) before context actions
- Clear separation between tap, hold, and drag

────────────────────────────────────────────────────────────────────────────────
                                                                 // source files
────────────────────────────────────────────────────────────────────────────────

## Source Files

```
src/Hydrogen/Schema/Gestural/           (31 files, ~10,971 lines)
├── Pointer.purs                        (PointerState, MouseButton, Pressure)
├── Keyboard.purs                       (leader module)
├── Keyboard/
│   ├── Keys.purs                       (KeyCode, all key constants)
│   ├── Modifiers.purs                  (ModifierState, Ctrl/Alt/Shift/Meta)
│   ├── Shortcut.purs                   (Shortcut matching)
│   ├── Event.purs                      (KeyEvent)
│   ├── State.purs                      (KeyboardState)
│   └── Navigation.purs                 (Arrow/Tab navigation)
├── Gesture.purs                        (leader module)
├── Gesture/
│   ├── Phase.purs                      (GesturePhase state machine)
│   ├── Tap.purs                        (TapCount, TapState)
│   ├── Swipe.purs                      (SwipeDirection, SwipeState)
│   ├── Pinch.purs                      (PinchConfig, PinchGesture)
│   ├── Rotate.purs                     (RotateGesture)
│   ├── Pan.purs                        (PanGesture)
│   └── LongPress.purs                  (LongPressGesture)
├── Focus.purs                          (FocusState, focus management)
├── Hover.purs                          (HoverState)
├── Timing.purs                         (ClickCount, HoldDuration, TapInterval)
└── ContextMenu.purs                    (ContextMenuState)
```

────────────────────────────────────────────────────────────────────────────────
                                                                   // references
────────────────────────────────────────────────────────────────────────────────

## References

- **W3C Pointer Events** — https://www.w3.org/TR/pointerevents3/
- **W3C UI Events** — https://www.w3.org/TR/uievents/
- **Apple UIKit Gesture Recognizers** — UIGestureRecognizer state machine
- **Android Gesture Detection** — GestureDetector, ScaleGestureDetector
