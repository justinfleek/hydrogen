━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                               // 37 // element
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Element Pillar

Core UI element primitives — the STACKED compound architecture for interactive
components that compose atoms from every pillar.

────────────────────────────────────────────────────────────────────────────────
                                                                    // overview
────────────────────────────────────────────────────────────────────────────────

## Implementation

- **Location**: `src/Hydrogen/Schema/Element/`
- **Files**: 5 modules
- **Lines**: 557 total
- **Key features**: STACKED compound pattern, four-pillar composition,
  accessibility-first semantics, deterministic identity

## Purpose

Element provides the STACKED compound architecture for building UI components.
Every interactive element (buttons, inputs, cards) is composed from atoms
belonging to four orthogonal pillars:

1. **Geometry** — Spatial layout, dimensions, padding, corner radii
2. **Appearance** — Visual surface: fill, border, shadow, opacity
3. **Behavior** — Interaction response: haptic, audio, timing
4. **Semantics** — Purpose, identity, accessibility

This separation enables agents to compose any variant of any component by
selecting appropriate atoms from each pillar. A "primary button" and a
"ghost button" differ only in their Appearance atoms — same Geometry,
same Behavior, same Semantics.

## The STACKED Pattern

Unlike traditional UI frameworks where components are monolithic,
Hydrogen elements are **STACKED** — composed from independent layers:

```purescript
type Button =
  { geometry :: ButtonGeometry       -- WHERE (space)
  , appearance :: ButtonAppearance   -- HOW (surface)
  , behavior :: ButtonBehavior       -- WHEN (interaction)
  , semantics :: ButtonSemantics     -- WHY (purpose)
  }
```

**Why this matters at billion-agent scale:**

- Agents can modify ONE layer without touching others
- Design tokens map cleanly to specific layers
- Accessibility lives in Semantics, never tangled with visuals
- State changes update Appearance/Behavior, not Geometry

────────────────────────────────────────────────────────────────────────────────
                                                        // button // compound
────────────────────────────────────────────────────────────────────────────────

## Button

The foundational interactive compound — a bounded region of space-time
where AI communicates intent, state, and need.

### Type Definition

```purescript
type Button =
  { geometry :: ButtonGeometry
  , appearance :: ButtonAppearance
  , behavior :: ButtonBehavior
  , semantics :: ButtonSemantics
  }
```

### Constructor

```purescript
button
  :: ButtonGeometry
  -> ButtonAppearance
  -> ButtonBehavior
  -> ButtonSemantics
  -> Button
```

### Default Preset

**`defaultButton`** — Blue fill, 8px corners, light haptic, "Button" label.

```purescript
defaultButton :: Button
defaultButton =
  { geometry: defaultGeometry
  , appearance: defaultAppearance
  , behavior: defaultBehavior
  , semantics: defaultSemantics "Button"
  }
```

### Usage Example

```purescript
myButton = button
  { geometry: defaultGeometry
  , appearance: defaultAppearance
  , behavior: defaultBehavior
  , semantics: actionSemantics "Click me"
  }
```

────────────────────────────────────────────────────────────────────────────────
                                                       // geometry // molecule
────────────────────────────────────────────────────────────────────────────────

## ButtonGeometry

Spatial atoms for button layout and shape — WHERE the button exists in space.

### Type Definition

```purescript
type ButtonGeometry =
  { -- Dimensions
    width :: Maybe Number           -- Explicit width (Nothing = auto)
  , height :: Maybe Number          -- Explicit height (Nothing = auto)
  , minWidth :: Maybe Number        -- Minimum width constraint
  , maxWidth :: Maybe Number        -- Maximum width constraint
  , minHeight :: Maybe Number       -- Minimum height constraint
  , maxHeight :: Maybe Number       -- Maximum height constraint
    -- Spacing
  , paddingTop :: Number            -- Top padding (px)
  , paddingRight :: Number          -- Right padding (px)
  , paddingBottom :: Number         -- Bottom padding (px)
  , paddingLeft :: Number           -- Left padding (px)
  , gap :: Number                   -- Gap between icon and label (px)
    -- Shape
  , cornerRadii :: CornerRadii      -- Per-corner radius
  }
```

### Atoms

| Name | Type | Default | Notes |
|------|------|---------|-------|
| `width` | Maybe Number | Nothing | Auto-sizes to content |
| `height` | Maybe Number | Nothing | Auto-sizes to content |
| `minWidth` | Maybe Number | Nothing | No minimum |
| `maxWidth` | Maybe Number | Nothing | No maximum |
| `minHeight` | Maybe Number | Just 36.0 | Touch target minimum |
| `maxHeight` | Maybe Number | Nothing | No maximum |
| `paddingTop` | Number | 8.0 | Vertical internal spacing |
| `paddingRight` | Number | 12.0 | Horizontal internal spacing |
| `paddingBottom` | Number | 8.0 | Vertical internal spacing |
| `paddingLeft` | Number | 12.0 | Horizontal internal spacing |
| `gap` | Number | 8.0 | Icon-to-label spacing |
| `cornerRadii` | CornerRadii | uniform 8.0 | Rounded corners |

### Constructor

```purescript
mkGeometry
  :: Maybe Number          -- Width
  -> Maybe Number          -- Height
  -> Number                -- Padding X (horizontal)
  -> Number                -- Padding Y (vertical)
  -> Number                -- Corner radius (uniform)
  -> ButtonGeometry
```

### Preset

**`defaultGeometry`** — Auto-sized with 12px horizontal, 8px vertical padding, 
8px uniform corner radius, 36px minimum height for touch targets.

### Accessors

| Function | Returns | Description |
|----------|---------|-------------|
| `geoWidth` | Maybe Number | Explicit width |
| `geoHeight` | Maybe Number | Explicit height |
| `geoPadding` | Spacing.Padding | Padding as Spacing type |
| `geoCornerRadii` | CornerRadii | Per-corner radii |

### External Dependencies

- **Hydrogen.Schema.Geometry.CornerRadii** — Per-corner radius values
- **Hydrogen.Schema.Geometry.Spacing** — Padding abstraction

────────────────────────────────────────────────────────────────────────────────
                                                      // appearance // molecule
────────────────────────────────────────────────────────────────────────────────

## ButtonAppearance

Visual atoms for button surface and elevation — HOW the button looks.

### Type Definition

```purescript
type ButtonAppearance =
  { -- Surface
    fill :: Fill                    -- Background fill
  , opacity :: Number               -- Overall opacity (0-1)
    -- Border
  , borderWidth :: Number           -- Border width (0 = no border)
  , borderColor :: Maybe RGB        -- Border color (Nothing = transparent)
    -- Elevation
  , shadow :: LayeredShadow         -- Shadow layers
  }
```

### Atoms

| Name | Type | Default | Bounds | Notes |
|------|------|---------|--------|-------|
| `fill` | Fill | Solid Blue 500 | — | Background fill type |
| `opacity` | Number | 1.0 | 0.0–1.0 | Overall element opacity |
| `borderWidth` | Number | 0.0 | ≥0.0 | Border stroke width |
| `borderColor` | Maybe RGB | Nothing | — | Border color |
| `shadow` | LayeredShadow | noShadow | — | Elevation shadow |

### Default Fill Color

```purescript
rgb 59 130 246  -- Blue 500 (Tailwind)
```

### Preset

**`defaultAppearance`** — Solid blue fill, no border, no shadow, full opacity.

```purescript
defaultAppearance :: ButtonAppearance
defaultAppearance =
  { fill: fillSolid (rgb 59 130 246)  -- Blue 500
  , opacity: 1.0
  , borderWidth: 0.0
  , borderColor: Nothing
  , shadow: noShadow
  }
```

### Accessors

| Function | Returns | Description |
|----------|---------|-------------|
| `appFill` | Fill | Background fill |
| `appShadow` | LayeredShadow | Shadow configuration |
| `appBorderWidth` | Number | Border thickness |
| `appBorderColor` | Maybe RGB | Border color |
| `appOpacity` | Number | Element opacity |

### External Dependencies

- **Hydrogen.Schema.Surface.Fill** — Fill types (solid, gradient, noise, pattern)
- **Hydrogen.Schema.Elevation.Shadow** — Layered shadow system
- **Hydrogen.Schema.Color.RGB** — RGB color space

### Variant Patterns

| Variant | Fill | Border | Shadow |
|---------|------|--------|--------|
| Primary | Solid brand color | None | sm |
| Secondary | Solid gray 100 | None | None |
| Ghost | None (transparent) | 1px brand | None |
| Outline | None | 1px current | None |
| Elevated | Solid white | None | lg |

────────────────────────────────────────────────────────────────────────────────
                                                       // behavior // molecule
────────────────────────────────────────────────────────────────────────────────

## ButtonBehavior

Interaction atoms for button response — WHEN and HOW the button responds.

### Type Definition

```purescript
type ButtonBehavior =
  { -- Haptic
    hapticOnPress :: Maybe ImpactFeedback    -- Vibration on press
  , hapticOnRelease :: Maybe ImpactFeedback  -- Vibration on release
    -- Audio
  , audioOnClick :: Maybe AudioCue           -- Sound on click
    -- Timing
  , longPressThresholdMs :: Number           -- Long press threshold (ms)
  , debounceMs :: Number                     -- Click debounce (ms)
  }
```

### Atoms

| Name | Type | Default | Notes |
|------|------|---------|-------|
| `hapticOnPress` | Maybe ImpactFeedback | Just ImpactLight | Vibration on touch |
| `hapticOnRelease` | Maybe ImpactFeedback | Nothing | Vibration on release |
| `audioOnClick` | Maybe AudioCue | Nothing | Sound feedback |
| `longPressThresholdMs` | Number | 500.0 | Long press detection |
| `debounceMs` | Number | 0.0 | Rapid-click prevention |

### Preset

**`defaultBehavior`** — Light haptic on press, no audio, 500ms long press threshold.

```purescript
defaultBehavior :: ButtonBehavior
defaultBehavior =
  { hapticOnPress: Just ImpactLight
  , hapticOnRelease: Nothing
  , audioOnClick: Nothing
  , longPressThresholdMs: 500.0
  , debounceMs: 0.0
  }
```

### Accessors

| Function | Returns | Description |
|----------|---------|-------------|
| `behHapticPress` | Maybe ImpactFeedback | Press haptic |
| `behHapticRelease` | Maybe ImpactFeedback | Release haptic |
| `behAudioClick` | Maybe AudioCue | Click sound |
| `behLongPressMs` | Number | Long press threshold |

### External Dependencies

- **Hydrogen.Schema.Haptic.Feedback** — Haptic feedback types
- **Hydrogen.Schema.Haptic.Event** — Audio cue types

### ImpactFeedback Enum

| Constructor | Description |
|-------------|-------------|
| `ImpactLight` | Subtle tap sensation |
| `ImpactMedium` | Standard click feedback |
| `ImpactHeavy` | Strong, deliberate feedback |
| `ImpactRigid` | Sharp, precise sensation |
| `ImpactSoft` | Gentle, cushioned feedback |

### Timing Constants

| Constant | Value | Usage |
|----------|-------|-------|
| Long Press | 500ms | Context menu trigger |
| Double Tap | 300ms | Double-click window |
| Debounce | 0ms | No default debounce |

────────────────────────────────────────────────────────────────────────────────
                                                      // semantics // molecule
────────────────────────────────────────────────────────────────────────────────

## ButtonSemantics

Purpose, identity, and accessibility atoms — WHY the button exists.

### Type Definition

```purescript
type ButtonSemantics =
  { -- Purpose
    purpose :: ButtonPurpose         -- Semantic purpose
  , label :: String                  -- Visible or ARIA label
    -- State
  , toggleState :: Maybe ToggleState -- For toggle buttons
  , popupType :: Maybe PopupType     -- For menu/dialog triggers
    -- Flags
  , disabled :: Boolean              -- Is button disabled?
  , loading :: Boolean               -- Is button in loading state?
    -- Accessibility
  , ariaDescribedBy :: Maybe String  -- ID of describing element
  , ariaControls :: Maybe String     -- ID of controlled element
  }
```

### Atoms

| Name | Type | Default | Notes |
|------|------|---------|-------|
| `purpose` | ButtonPurpose | ActionButton | Semantic role |
| `label` | String | (required) | Accessible name |
| `toggleState` | Maybe ToggleState | Nothing | Toggle on/off state |
| `popupType` | Maybe PopupType | Nothing | Popup trigger type |
| `disabled` | Boolean | false | Disabled state |
| `loading` | Boolean | false | Loading state |
| `ariaDescribedBy` | Maybe String | Nothing | Description reference |
| `ariaControls` | Maybe String | Nothing | Controlled element ID |

### ButtonPurpose Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `ActionButton` | `"action"` | General purpose action |
| `FormSubmit` | `"submit"` | Form submission |
| `ToggleControl` | `"toggle"` | On/off toggle |
| `MenuTrigger` | `"menu"` | Opens dropdown menu |
| `DialogTrigger` | `"dialog"` | Opens modal dialog |
| `MediaControl` | `"media"` | Play/pause/seek |
| `NavigationLink` | `"navigation"` | Navigate to location |
| `DestructiveAction` | `"destructive"` | Delete/remove |
| `CreateAction` | `"create"` | Add new item |
| `ResetAction` | `"reset"` | Reset/clear form |

### ToggleState Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `Pressed` | `"pressed"` | Toggle is ON |
| `Unpressed` | `"unpressed"` | Toggle is OFF |
| `Mixed` | `"mixed"` | Indeterminate state |

### PopupType Enum

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `PopupMenu` | `"menu"` | Dropdown menu |
| `PopupListbox` | `"listbox"` | Selection list |
| `PopupTree` | `"tree"` | Tree navigation |
| `PopupGrid` | `"grid"` | Grid selection |
| `PopupDialog` | `"dialog"` | Modal dialog |

### Presets

**`defaultSemantics`** — Action button with label.

```purescript
defaultSemantics :: String -> ButtonSemantics
defaultSemantics lbl =
  { purpose: ActionButton
  , label: lbl
  , toggleState: Nothing
  , popupType: Nothing
  , disabled: false
  , loading: false
  , ariaDescribedBy: Nothing
  , ariaControls: Nothing
  }
```

**`actionSemantics`** — General purpose action button.

```purescript
actionSemantics :: String -> ButtonSemantics
actionSemantics = defaultSemantics
```

**`submitSemantics`** — Form submission button.

```purescript
submitSemantics :: String -> ButtonSemantics
submitSemantics lbl = (defaultSemantics lbl) { purpose = FormSubmit }
```

**`toggleSemantics`** — Toggle button with state.

```purescript
toggleSemantics :: String -> Boolean -> ButtonSemantics
toggleSemantics lbl isPressed = (defaultSemantics lbl)
  { purpose = ToggleControl
  , toggleState = Just (if isPressed then Pressed else Unpressed)
  }
```

### Accessors

| Function | Returns | Description |
|----------|---------|-------------|
| `semPurpose` | ButtonPurpose | Semantic purpose |
| `semLabel` | String | Accessible label |
| `semToggleState` | Maybe ToggleState | Toggle state |
| `semDisabled` | Boolean | Disabled flag |

### External Dependencies

- **Hydrogen.Schema.Reactive.ButtonSemantics** — Purpose, toggle, popup types


────────────────────────────────────────────────────────────────────────────────
                                                     // accessibility // notes
────────────────────────────────────────────────────────────────────────────────

## Accessibility Architecture

Element primitives encode accessibility at the structural level, not as an
afterthought.

### ARIA Mapping

| Semantics Field | ARIA Attribute |
|-----------------|----------------|
| `purpose` | `role` (implicit) |
| `label` | `aria-label` or visible text |
| `toggleState` | `aria-pressed` |
| `popupType` | `aria-haspopup` |
| `disabled` | `aria-disabled` |
| `loading` | `aria-busy` |
| `ariaDescribedBy` | `aria-describedby` |
| `ariaControls` | `aria-controls` |

### Why Semantics is Separate

Accessibility is **intrinsic**, not cosmetic. By isolating semantics:

1. Visual changes (Appearance) cannot break accessibility
2. Behavior changes (timing) cannot affect screen readers
3. Layout changes (Geometry) cannot obscure semantic role
4. The same semantic button can render as any visual variant

### Loading State Pattern

When `loading: true`:
- `aria-busy` is set
- Click events should be ignored (Behavior responsibility)
- Visual feedback should indicate loading (Appearance responsibility)
- The label remains stable for screen readers

────────────────────────────────────────────────────────────────────────────────
                                                       // composition // guide
────────────────────────────────────────────────────────────────────────────────

## Composing Button Variants

### Primary Button

```purescript
primaryButton :: String -> Button
primaryButton label = button
  defaultGeometry
  (defaultAppearance { fill = fillSolid brandPrimary })
  defaultBehavior
  (actionSemantics label)
```

### Ghost Button

```purescript
ghostButton :: String -> Button
ghostButton label = button
  defaultGeometry
  { fill: FillNone
  , opacity: 1.0
  , borderWidth: 1.0
  , borderColor: Just brandPrimary
  , shadow: noShadow
  }
  defaultBehavior
  (actionSemantics label)
```

### Icon Button

```purescript
iconButton :: String -> Button
iconButton ariaLabel = button
  (mkGeometry (Just 36.0) (Just 36.0) 0.0 0.0 18.0)  -- Square, circular
  defaultAppearance
  defaultBehavior
  (actionSemantics ariaLabel)
```

### Toggle Button

```purescript
toggleButton :: String -> Boolean -> Button
toggleButton label isActive = button
  defaultGeometry
  (if isActive
    then defaultAppearance { fill = fillSolid brandPrimary }
    else defaultAppearance { fill = fillSolid gray200 })
  (defaultBehavior { hapticOnPress = Just ImpactMedium })
  (toggleSemantics label isActive)
```

### Submit Button

```purescript
submitButton :: String -> Button
submitButton label = button
  defaultGeometry
  (defaultAppearance 
    { fill = fillSolid green500
    , shadow = shadowSm
    })
  defaultBehavior
  (submitSemantics label)
```

### Destructive Button

```purescript
destructiveButton :: String -> Button
destructiveButton label = button
  defaultGeometry
  (defaultAppearance { fill = fillSolid red500 })
  (defaultBehavior { hapticOnPress = Just ImpactHeavy })
  ((actionSemantics label) { purpose = DestructiveAction })
```

────────────────────────────────────────────────────────────────────────────────
                                                           // state // mapping
────────────────────────────────────────────────────────────────────────────────

## Button States

Interactive elements have states. Here's how they map to the four pillars:

### State Distribution

| State | Geometry | Appearance | Behavior | Semantics |
|-------|----------|------------|----------|-----------|
| Default | base | base | base | base |
| Hover | — | Lighter fill | — | — |
| Focus | — | Focus ring | — | — |
| Active | — | Darker fill | Haptic fires | — |
| Disabled | — | 50% opacity | No haptic | disabled: true |
| Loading | — | Spinner | No click | loading: true |

### State Does Not Live in Element

Notice: **Element has no state field**. This is intentional.

State is managed by the runtime. Element is a **snapshot** — the current
view of a component given current state. When state changes:

1. Runtime updates internal state
2. Calls `view :: State -> Element msg`
3. Gets new Element value
4. Diffs with previous Element
5. Patches the DOM

The Element type is **always** the "normal" representation. Hover, focus,
and active states are handled by:

- CSS `:hover`, `:focus`, `:active` pseudo-classes (DOM target)
- Shader uniforms (WebGL target)
- Runtime-managed state (Canvas target)

────────────────────────────────────────────────────────────────────────────────
                                                              // source // files
────────────────────────────────────────────────────────────────────────────────

```
src/Hydrogen/Schema/Element/
├── Button.purs                    # STACKED compound composition
│                                  # Re-exports all sub-modules
└── Button/
    ├── Appearance.purs            # Fill, border, shadow, opacity
    ├── Behavior.purs              # Haptic, audio, timing
    ├── Geometry.purs              # Size, padding, corners
    └── Semantics.purs             # Purpose, accessibility, state
```

5 files, 557 lines total.

### Module Export Structure

**Button.purs** is a leader module that re-exports all sub-modules:

```purescript
module Hydrogen.Schema.Element.Button
  ( -- * Button Compound Type
    Button
  , button
  , defaultButton
    -- * Re-exports from sub-modules
  , module Hydrogen.Schema.Element.Button.Geometry
  , module Hydrogen.Schema.Element.Button.Appearance
  , module Hydrogen.Schema.Element.Button.Behavior
  , module Hydrogen.Schema.Element.Button.Semantics
  ) where
```

This allows single-import access to the complete Button vocabulary.

────────────────────────────────────────────────────────────────────────────────
                                                         // future // elements
────────────────────────────────────────────────────────────────────────────────

## Planned Element Compounds

The STACKED pattern applies to all interactive elements:

| Element | Status | Notes |
|---------|--------|-------|
| Button | Complete | Foundation pattern |
| Input | Planned | Text, number, date inputs |
| Toggle | Planned | Switch, checkbox, radio |
| Select | Planned | Dropdown, combobox |
| Slider | Planned | Range input |
| Card | Planned | Container compound |
| Modal | Planned | Dialog, sheet |
| Menu | Planned | Dropdown, context menu |
| Tab | Planned | Tab bar, segmented control |
| List | Planned | List item, virtual list |

Each will follow the four-pillar STACKED architecture:
- **Geometry** — Layout and dimensions
- **Appearance** — Visual surface
- **Behavior** — Interaction response
- **Semantics** — Purpose and accessibility

────────────────────────────────────────────────────────────────────────────────
                                                       // design // philosophy
────────────────────────────────────────────────────────────────────────────────

## Why STACKED Compounds Matter

### The Problem with Traditional Components

In traditional UI frameworks, a button is a monolithic blob:

```typescript
// React — everything tangled together
<Button
  variant="primary"    // Appearance
  size="lg"           // Geometry
  onClick={...}       // Behavior
  disabled={...}      // Semantics
  leftIcon={...}      // Content (where does this go?)
/>
```

The concerns are **mixed**. Changing the size affects the variant. Adding
an icon changes the padding. Disabled state affects both visuals AND
behavior.

### The STACKED Solution

Hydrogen separates concerns orthogonally:

```purescript
-- Geometry: WHERE
-- Appearance: HOW
-- Behavior: WHEN
-- Semantics: WHY
```

These layers are **independent**. You can:

- Change Appearance without touching Geometry
- Modify Behavior without affecting Semantics
- Update Semantics without rebuilding visuals

### Benefits at Billion-Agent Scale

**Deterministic composition**: Two agents building the same button
from the same atoms get identical results.

**Incremental modification**: An agent updating hover states only
touches Appearance atoms — no risk of breaking accessibility.

**Design token mapping**: Brand colors map to Appearance. Touch targets map to
Geometry. Haptic intensity maps to Behavior. ARIA patterns map to Semantics.

**Cross-platform consistency**: The same Element renders to:
- DOM with CSS
- Canvas with manual painting
- WebGL with shaders
- Static HTML for SSG

**Caching efficiency**: Same Geometry hash means reuse layout calculation.
Same Appearance hash means reuse rendering. Independent invalidation.

### The Atomic Foundation

Button is a **compound** — composed from **molecules** (the four pillar
records), which are composed from **atoms** (primitive values with bounds).

Every Number has a valid range. Every enum has exhaustive variants. Every
Maybe has explicit handling. There are no escape hatches, no undefined
values, no "well, it depends on the browser."

This is the foundation for deterministic UI at swarm scale.

────────────────────────────────────────────────────────────────────────────────
                                                    // uuid5 // deterministic
────────────────────────────────────────────────────────────────────────────────

## Deterministic Identity

Every Element can be hashed to a UUID5 based on its content:

```purescript
-- Same atoms produce same UUID5
button1 = defaultButton
button2 = defaultButton

uuid5 button1 == uuid5 button2  -- Always true
```

### Why UUID5 Matters

- **Caching**: Identical elements share cached render results
- **Diffing**: Fast equality check before deep comparison
- **Distribution**: Elements can be referenced across network boundaries
- **Reproducibility**: Same input produces same output produces same identity

### Namespace

```
uuid5 "hydrogen.element.button" (serialize buttonData)
```

────────────────────────────────────────────────────────────────────────────────
                                                             // graded // types
────────────────────────────────────────────────────────────────────────────────

## Effect and Co-Effect Tracking

Element types can be graded to track capabilities:

### Effects (What it produces)

| Effect | Description |
|--------|-------------|
| `CanClick` | Element responds to clicks |
| `CanHover` | Element responds to hover |
| `CanFocus` | Element can receive focus |
| `CanAnimate` | Element has animations |
| `CanEmitSound` | Element produces audio |
| `Pure` | No interactive effects |

### Co-Effects (What it needs)

| Co-Effect | Description |
|-----------|-------------|
| `NeedsFont` | Requires font loading |
| `NeedsIcon` | Requires icon assets |
| `NeedsData` | Requires async data |
| `NeedsNothing` | Self-contained |

### Graded Button Type

```purescript
type ButtonG eff coeff =
  { geometry :: ButtonGeometry
  , appearance :: ButtonAppearance
  , behavior :: ButtonBehavior eff
  , semantics :: ButtonSemantics
  }

-- A clickable button that needs no external resources
defaultButton :: ButtonG CanClick NeedsNothing
```

This enables compile-time verification that:
- A purely static render has no click handlers
- A button with icons declares its asset dependencies
- An animated button is only used where animation is permitted

────────────────────────────────────────────────────────────────────────────────
                                                    // cross // pillar // atoms
────────────────────────────────────────────────────────────────────────────────

## Cross-Pillar Dependencies

Element compounds draw atoms from many pillars:

### Geometry Layer Dependencies

| Atom | Source Pillar | Module |
|------|---------------|--------|
| CornerRadii | Geometry | `Hydrogen.Schema.Geometry.CornerRadii` |
| Padding | Geometry | `Hydrogen.Schema.Geometry.Spacing` |
| SpacingValue | Dimension | `Hydrogen.Schema.Dimension.Spacing` |

### Appearance Layer Dependencies

| Atom | Source Pillar | Module |
|------|---------------|--------|
| Fill | Surface | `Hydrogen.Schema.Surface.Fill` |
| RGB | Color | `Hydrogen.Schema.Color.RGB` |
| LayeredShadow | Elevation | `Hydrogen.Schema.Elevation.Shadow` |
| Opacity | Color | `Hydrogen.Schema.Color.Opacity` |

### Behavior Layer Dependencies

| Atom | Source Pillar | Module |
|------|---------------|--------|
| ImpactFeedback | Haptic | `Hydrogen.Schema.Haptic.Feedback` |
| AudioCue | Haptic | `Hydrogen.Schema.Haptic.Event` |

### Semantics Layer Dependencies

| Atom | Source Pillar | Module |
|------|---------------|--------|
| ButtonPurpose | Reactive | `Hydrogen.Schema.Reactive.ButtonSemantics` |
| ToggleState | Reactive | `Hydrogen.Schema.Reactive.ButtonSemantics` |
| PopupType | Reactive | `Hydrogen.Schema.Reactive.ButtonSemantics` |

This demonstrates how Element is a **compound** in the atomic hierarchy —
it composes molecules from multiple pillars, which themselves compose atoms.

────────────────────────────────────────────────────────────────────────────────
                                                         // rendering // targets
────────────────────────────────────────────────────────────────────────────────

## Target-Specific Rendering

Element is pure data. Targets interpret it to reality:

### DOM Target

```purescript
-- Renders Button to:
<button
  class="btn"
  style="
    padding: 8px 12px;
    background: rgb(59, 130, 246);
    border-radius: 8px;
  "
  aria-label="Click me"
>
  Click me
</button>
```

### Canvas Target

```purescript
-- Renders Button as:
ctx.beginPath()
ctx.roundRect(x, y, width, height, 8)
ctx.fillStyle = "rgb(59, 130, 246)"
ctx.fill()
ctx.fillText("Click me", textX, textY)
```

### WebGL Target

```purescript
-- Renders Button as:
-- 1. Rounded rectangle geometry (SDF)
-- 2. Fragment shader with fill color
-- 3. Text rendered via SDF font atlas
```

### Static Target (SSG)

```purescript
-- Renders Button as HTML string:
"<button class=\"btn\" style=\"...\" aria-label=\"Click me\">Click me</button>"
```

The Element type is **target-agnostic**. The runtime chooses how to interpret.

────────────────────────────────────────────────────────────────────────────────
                                                              // type // safety
────────────────────────────────────────────────────────────────────────────────

## Type Safety Guarantees

### No Partial Functions

Every accessor returns a total result:

```purescript
geoWidth :: ButtonGeometry -> Maybe Number  -- Maybe, not partial
semToggleState :: ButtonSemantics -> Maybe ToggleState  -- Maybe, not partial
```

### No Unbounded Values

All numeric atoms have implicit or explicit bounds:

```purescript
opacity :: Number  -- Bounded 0.0 to 1.0 by convention
longPressThresholdMs :: Number  -- Positive by convention
paddingTop :: Number  -- Non-negative by convention
```

### Exhaustive Pattern Matching

All enums are complete:

```purescript
case purpose of
  ActionButton -> ...
  FormSubmit -> ...
  ToggleControl -> ...
  MenuTrigger -> ...
  DialogTrigger -> ...
  MediaControl -> ...
  NavigationLink -> ...
  DestructiveAction -> ...
  CreateAction -> ...
  ResetAction -> ...
  -- No wildcard needed — all cases covered
```

### Maybe for Optional Values

Optional atoms use Maybe, never null:

```purescript
borderColor :: Maybe RGB  -- Explicit optionality
toggleState :: Maybe ToggleState  -- Only for toggle buttons
ariaDescribedBy :: Maybe String  -- Only if description exists
```

────────────────────────────────────────────────────────────────────────────────
