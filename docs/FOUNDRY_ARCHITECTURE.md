# FOUNDRY ARCHITECTURE

**Last Updated:** 2026-03-03
**Status:** ARCHITECTURAL RESET - Previous implementation was wrong

---

## THE ONE RULE

**Foundry exists to demonstrate that Hydrogen's 38 pillars can represent ANY visual element scraped from ANY website.**

That's it. Nothing else.

---

## HYDROGEN WAS BUILT FOR THIS

Hydrogen isn't just a UI framework. It's the **target ontology** for visual representation.

The type system in Hydrogen was specifically designed so that:
1. Any visual element on any website can be decomposed into Hydrogen atoms
2. Those atoms can be recomposed into pixel-perfect replicas
3. All values are bounded, typed, and proven

`Hydrogen.Scraper.*` already exists because scraping was always part of the plan.
Foundry is just the **browser automation layer** that feeds Hydrogen's scraper types.

```
┌─────────────────┐      ┌─────────────────┐      ┌─────────────────┐
│    FOUNDRY      │      │    HYDROGEN     │      │    HYDROGEN     │
│   (Playwright)  │ ──▶  │   (Scraper.*)   │ ──▶  │   (Schema.*)    │
│                 │      │                 │      │                 │
│  Browser        │      │  Extraction     │      │  Atoms          │
│  automation     │      │  & parsing      │      │  & composition  │
└─────────────────┘      └─────────────────┘      └─────────────────┘
     10-20 sec              Raw → Typed           Bounded values
     observation            conversion            for any visual
```

**Foundry is thin. Hydrogen is everything.**

---

## UNIVERSAL PARSING

Foundry must handle ANY website. Not just marketing pages. Everything:

### E-commerce (Amazon, Shopify, etc.)
- Product cards with hover states
- Add-to-cart button animations
- Image carousels with swipe gestures
- Price formatting and strikethrough styles
- Rating stars (SVG or icon font)
- Quantity steppers (+/- buttons)
- Checkout flow state transitions

### Video Platforms (YouTube, Vimeo, etc.)
- Video player controls (play, pause, seek)
- Progress bar with scrubbing
- Volume slider interactions
- Fullscreen transitions
- Thumbnail hover previews
- Like/subscribe button states
- Comment section expand/collapse

### Audio/Music Software (Ableton, Spotify, etc.)
- **Knobs** - rotary controls with drag-to-rotate
- **Sliders** - linear faders with continuous values
- **Switches** - toggle states with transitions
- **Waveforms** - SVG or canvas visualizations
- **VU meters** - animated level indicators
- **Transport controls** - play/stop/record states
- **Spectrum analyzers** - real-time frequency displays

### Dashboards (Admin panels, Analytics, etc.)
- Data grids with sort/filter states
- Charts (line, bar, pie) - SVG/Canvas
- Tooltips on hover
- Dropdown menus
- Date pickers
- Modal dialogs with enter/exit animations
- Sidebar collapse/expand
- Tab switching

### Social Media (Twitter, Instagram, etc.)
- Like button animations (heart burst)
- Follow button state changes
- Story carousels
- Pull-to-refresh
- Infinite scroll loading states
- Emoji reactions
- Share sheet modals

### Creative Tools (Figma, Canva, etc.)
- Canvas with zoom/pan
- Selection handles
- Property panels
- Color pickers
- Layer panels with drag-to-reorder
- Tool palettes
- Contextual menus

### EVERY element becomes Hydrogen atoms:

| Visual Element | Hydrogen Mapping |
|----------------|------------------|
| Knob rotation | `Transform (Rotate angle)` + `Hydrogen.Schema.Gestural.DragDrop` |
| Slider thumb | `Transform (Translate x y)` + value binding |
| Toggle switch | `StateTransition` between on/off with `Easing` |
| Waveform | `Hydrogen.Schema.SVG.Path` or `Hydrogen.Schema.Canvas.*` |
| VU meter | `Hydrogen.Schema.Motion.KeyframeAnimation` with level data |
| Button hover | `ElementState` (rest) → `ElementState` (hover) with `Transition` |
| Modal appear | `KeyframeAnimation` with opacity + transform |
| Carousel swipe | `Hydrogen.Schema.Gestural.Gesture.Swipe` + `Transform` |
| Chart tooltip | `Hydrogen.Schema.Gestural.Hover` trigger + positioned element |
| Video progress | `Hydrogen.Schema.Temporal.Progress` + scrub gesture |

**If a human designer built it, Foundry can decompose it into Hydrogen atoms.**

### Canvas/WebGL Elements

Some elements render to `<canvas>` not DOM. Foundry handles these too:

- **Screenshot diffing** - Capture canvas before/after interaction
- **Animation frame sampling** - Record canvas at 60fps during animation
- **Lottie extraction** - Lottie renders to canvas but we extract the JSON source
- **Chart libraries** - Most emit SVG or have accessible data; fallback to visual capture
- **WebGL shaders** - Capture shader uniforms and their animated values
- **Waveform displays** - Sample the rendered output at intervals

For canvas elements, we capture:
1. The **trigger** that causes visual change
2. The **visual delta** (pixel difference or extracted data)
3. The **timing** of the change
4. Any **accessible data** the library exposes

This becomes:
- `Hydrogen.Schema.Canvas.*` - Canvas grid, bounds, physics
- `Hydrogen.Schema.Geometry.Path` - SVG path data
- `Hydrogen.Schema.Motion.*` - Animation keyframes
- `Hydrogen.Scraper.Types.SVG` - SVG element types
- `Hydrogen.Icon.*` - Icon system

---

## WHAT FOUNDRY IS

Foundry is a **behavioral observation engine**. It:

1. **Probes** a webpage for 10-20 seconds
2. **Triggers** every possible interaction (hover, click, focus, scroll)
3. **Records** every visual state change
4. **Emits** Hydrogen atoms for every observed property

### What Gets Captured

- **Colors** - Every color in every state → `Hydrogen.Schema.Color.*`
- **Gradients** - Including animated gradients → `Hydrogen.Schema.Color.Gradient`
- **Typography** - Font families, sizes, weights → `Hydrogen.Schema.Typography.*`
- **Spacing** - Margins, padding, gaps → `Hydrogen.Schema.Dimension.*`
- **Transforms** - 2D/3D transforms in all states → `Hydrogen.Schema.Geometry.Transform`
- **Motion paths** - Bezier curves elements follow → `Hydrogen.Schema.Motion.PathMotion.*`
- **Keyframe animations** - Full animation data → `Hydrogen.Schema.Motion.KeyframeAnimation.*`
- **Lottie animations** - Embedded Lottie JSON → `Hydrogen.Schema.Motion.Lottie`
- **Easing curves** - Cubic bezier, spring, step → `Hydrogen.Schema.Temporal.Easing`
- **Triggers** - What causes state changes → `Hydrogen.Schema.Gestural.Trigger`
- **Transitions** - State A → State B with timing → `Hydrogen.Schema.Motion.Transition`
- **Shadows** - Box shadows, text shadows → `Hydrogen.Schema.Elevation.*`
- **Borders** - Stroke, radius, style → `Hydrogen.Element.Core.Stroke`
- **Icons/SVG** - Vector graphics → `Hydrogen.Schema.SVG.*`
- **Images** - With color grading analysis → `Hydrogen.Schema.Image.*`

### What Does NOT Get Captured

- **Editorial content** - Mission statements, values (human-authored, not scrapable)
- **Strategy** - Brand positioning, target customers (human-authored)
- **Voice guidelines** - Writing style rules (requires human input)

---

## WHAT FOUNDRY IS NOT

### NOT a CSS Parser

Wrong:
```
parse("background: linear-gradient(90deg, #ff0000, #0000ff)")
→ GradientString "linear-gradient(90deg, #ff0000, #0000ff)"
```

Right:
```
observe(element, hover=true)
→ Gradient {
    direction: Angle 90,
    stops: [
      GradientStop (SRGBA 1.0 0.0 0.0 1.0) (Percent 0),
      GradientStop (SRGBA 0.0 0.0 1.0 1.0) (Percent 100)
    ]
  }
```

### NOT a Type Duplicator

Foundry does NOT define its own:
- Color types (use `Hydrogen.Schema.Color.*`)
- Element types (use `Hydrogen.Element.*`)
- Transform types (use `Hydrogen.Schema.Geometry.Transform`)
- Event types (use `Hydrogen.Schema.Gestural.*`)
- Animation types (use `Hydrogen.Schema.Motion.*`, `Hydrogen.Schema.Temporal.*`)

**If Hydrogen has it, Foundry imports it. Period.**

### NOT a Brand Schema Definer

The `src/Brand/` directory with Editorial, Strategy, UIElements, etc. was WRONG.
Those are authoring concerns, not scraping concerns.
They have been deleted.

---

## CORE DATA MODEL

### HYDROGEN ALREADY HAS SCRAPER TYPES

**Critical discovery:** Hydrogen already defines scraper types in `Hydrogen.Scraper.*`:

```
hydrogen/src/Hydrogen/Scraper/
├── Types.purs              -- ExtractedElement, ScrapedPage, etc.
├── Types/
│   ├── Animation.purs      -- Animation extraction
│   ├── Element.purs        -- Element extraction
│   ├── Gradient.purs       -- Gradient extraction
│   ├── Identity.purs       -- Identity extraction
│   ├── Image.purs          -- Image extraction
│   ├── Pseudo.purs         -- Pseudo-element states
│   ├── State.purs          -- InteractionState, StateDiff
│   ├── SVG.purs            -- SVG extraction
│   └── Transform.purs      -- Transform extraction
├── Extract.purs            -- Extraction logic
└── Parse.purs              -- Parsing logic
```

**Foundry does NOT need to define its own types. It imports from Hydrogen.Scraper.**

### Key Types (from Hydrogen.Scraper)

#### InteractionState
```purescript
-- Hydrogen.Scraper.Types.State
data InteractionState
  = Default
  | Hover
  | Focus
  | FocusVisible
  | FocusWithin
  | Active
  | Visited
  | Disabled
  | Checked
  | Indeterminate
```

#### StateDiff
```purescript
-- Hydrogen.Scraper.Types.State
-- Visual differences from default state (Nothing = same as default)
type StateDiff =
  { backgroundColor :: Maybe OKLCH
  , color :: Maybe OKLCH
  , borderColor :: Maybe OKLCH
  , outlineColor :: Maybe OKLCH
  , outlineWidth :: Maybe Pixel
  , outlineOffset :: Maybe Pixel
  , transform :: Maybe ExtractedTransform
  , shadow :: Maybe LayeredShadow
  , opacity :: Maybe Number
  , cursor :: Maybe String
  }
```

#### ExtractedElement
```purescript
-- Hydrogen.Scraper.Types
-- Complete extracted element with all visual properties as Schema atoms
newtype ExtractedElement = ExtractedElement
  { data :: ExtractedElementData
  , children :: Array ExtractedElement
  }
```

#### ScrapedPage
```purescript
-- Hydrogen.Scraper.Types
-- Complete scraped page
type ScrapedPage =
  { url :: String
  , domain :: String
  , elements :: ElementTree
  , ... -- other fields
  }
```

### What Foundry Adds

Foundry extends Hydrogen.Scraper with:

1. **Transition timing** - Duration and easing between states
2. **Animation capture** - Lottie JSON, CSS keyframes, scroll-linked
3. **Observation protocol** - The 10-20 second probing behavior
4. **Playwright integration** - Browser automation layer

```purescript
-- Foundry extension: Transition between states
type StateTransition =
  { from :: InteractionState
  , to :: InteractionState
  , diff :: StateDiff                         -- From Hydrogen.Scraper.Types.State
  , duration :: Millisecond                   -- Hydrogen.Schema.Temporal.Millisecond
  , easing :: Easing                          -- Hydrogen.Schema.Temporal.Easing
  , delay :: Millisecond
  }

-- Foundry extension: Continuous animations
type AnimationObservation =
  { elementId :: ElementId
  , animationType :: AnimationType
  , keyframes :: Array Keyframe               -- Hydrogen.Schema.Motion.Keyframe
  , duration :: Millisecond
  , easing :: Easing
  , iterations :: Iteration                   -- Hydrogen.Schema.Temporal.Iteration
  , direction :: Direction                    -- Hydrogen.Schema.Temporal.Direction
  , playState :: PlayState                    -- Hydrogen.Schema.Temporal.PlayState
  , trigger :: TriggerCondition               -- Hydrogen.Schema.Gestural.Trigger
  }

data AnimationType
  = CSSKeyframes
  | LottieAnimation LottieData
  | SVGAnimation
  | ScrollLinked ScrollAnimation
```

---

## SCRAPER BEHAVIOR

### Observation Protocol

```
1. LOAD page, wait for JS execution
2. SNAPSHOT initial state of all visible elements
3. For each interactive element:
   a. HOVER for 300ms → record state change
   b. CLICK → record state change
   c. FOCUS → record state change
   d. HOVER OFF → record return state
4. SCROLL through page in increments
   a. Record scroll-triggered animations
   b. Record parallax effects
   c. Record lazy-loaded content
5. WAIT 2-3 seconds for auto-playing animations
   a. Record Lottie animations (extract JSON)
   b. Record CSS keyframe animations
   c. Record SVG animations
6. EMIT PageObservation with all Hydrogen atoms
```

### Timing Budget

- **Total observation time:** 10-20 seconds per page
- **Hover duration:** 300ms (enough to trigger CSS transitions)
- **Click observation:** 500ms post-click
- **Scroll observation:** 100ms per scroll increment
- **Animation capture:** Full duration of detected animations

---

## IMPLEMENTATION STACK

### Foundry = Playwright + ZMQ

That's it. Foundry is just:

1. **Playwright** - Browser automation in TypeScript
2. **Observation protocol** - The 10-20 second probing behavior
3. **ZMQ transport** - Getting raw observations out

### Hydrogen = Everything Else

All the smart stuff lives in Hydrogen:

- `Hydrogen.Scraper.Types.*` - Extraction types (ExtractedElement, StateDiff, etc.)
- `Hydrogen.Scraper.Extract` - Raw → typed conversion
- `Hydrogen.Scraper.Parse` - Parsing logic
- `Hydrogen.Schema.*` - All the atom types (Color, Dimension, Motion, etc.)
- `Hydrogen.Element.*` - Composition back to elements

### Why Haskell?

The Haskell `foundry-*` packages exist for:
- ZMQ client (talking to Playwright server)
- Integration with COMPASS (agent platform)
- Storage adapters (DuckDB, PostgreSQL)

But the core types? They're in Hydrogen (PureScript). The Haskell packages should mirror Hydrogen.Scraper types, not define their own.

### Target Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                           FOUNDRY                                │
│  ┌─────────────────────────────────────────────────────────┐    │
│  │  TypeScript/Playwright                                   │    │
│  │  - Control browser                                       │    │
│  │  - Execute observation protocol                          │    │
│  │  - Emit raw JSON over ZMQ                                │    │
│  └─────────────────────────────────────────────────────────┘    │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼ ZMQ (JSON)
┌─────────────────────────────────────────────────────────────────┐
│                           HYDROGEN                               │
│  ┌─────────────────────────────────────────────────────────┐    │
│  │  Hydrogen.Scraper.*                                      │    │
│  │  - Parse raw JSON                                        │    │
│  │  - Convert to typed atoms                                │    │
│  │  - Validate bounds                                       │    │
│  └─────────────────────────────────────────────────────────┘    │
│  ┌─────────────────────────────────────────────────────────┐    │
│  │  Hydrogen.Schema.*                                       │    │
│  │  - Color (OKLCH, SRGBA, Gradient)                        │    │
│  │  - Motion (Keyframe, Easing, Lottie)                     │    │
│  │  - Gestural (Trigger, Hover, Focus)                      │    │
│  │  - Geometry (Transform, Path, BoundingBox)               │    │
│  │  - ... all 38 pillars                                    │    │
│  └─────────────────────────────────────────────────────────┘    │
│  ┌─────────────────────────────────────────────────────────┐    │
│  │  Hydrogen.Element.*                                      │    │
│  │  - Compose atoms back into elements                      │    │
│  │  - Render to DOM                                         │    │
│  └─────────────────────────────────────────────────────────┘    │
└─────────────────────────────────────────────────────────────────┘
```

---

## HYDROGEN PILLARS USED

The 38 pillars that Foundry maps TO (not duplicates of):

### Color (Pillar 1-6)
- `Hydrogen.Schema.Color.SRGB` - sRGB colors
- `Hydrogen.Schema.Color.OKLCH` - Perceptual color space
- `Hydrogen.Schema.Color.HSL` - HSL colors
- `Hydrogen.Schema.Color.Gradient` - Linear, radial, conic gradients
- `Hydrogen.Schema.Color.Key` - Named color keys
- `Hydrogen.Schema.Color.Contrast` - WCAG contrast

### Geometry (Pillar 7-12)
- `Hydrogen.Schema.Geometry.Transform` - 2D/3D transforms
- `Hydrogen.Schema.Geometry.BoundingBox` - Element bounds
- `Hydrogen.Schema.Geometry.Point` - 2D/3D points
- `Hydrogen.Schema.Geometry.Vector` - Direction vectors
- `Hydrogen.Schema.Geometry.Matrix` - Transform matrices
- `Hydrogen.Schema.Geometry.Path` - SVG paths

### Dimension (Pillar 13-16)
- `Hydrogen.Schema.Dimension.Pixel` - Pixel values
- `Hydrogen.Schema.Dimension.Rem` - Relative em
- `Hydrogen.Schema.Dimension.Percent` - Percentages
- `Hydrogen.Schema.Dimension.ViewportUnit` - vw, vh, etc.

### Typography (Pillar 17-20)
- `Hydrogen.Schema.Typography.FontFamily` - Font stacks
- `Hydrogen.Schema.Typography.FontWeight` - 100-900 weights
- `Hydrogen.Schema.Typography.FontStyle` - Normal, italic
- `Hydrogen.Schema.Typography.TextDecoration` - Underline, etc.

### Temporal (Pillar 21-26)
- `Hydrogen.Schema.Temporal.Millisecond` - Durations
- `Hydrogen.Schema.Temporal.Easing` - Easing functions
- `Hydrogen.Schema.Temporal.CubicBezierEasing` - Bezier curves
- `Hydrogen.Schema.Temporal.SpringConfig` - Spring physics
- `Hydrogen.Schema.Temporal.Iteration` - Animation iterations
- `Hydrogen.Schema.Temporal.Direction` - Normal, reverse, alternate

### Motion (Pillar 27-32)
- `Hydrogen.Schema.Motion.Keyframe` - Animation keyframes
- `Hydrogen.Schema.Motion.KeyframeAnimation` - Full animations
- `Hydrogen.Schema.Motion.Transition` - State transitions
- `Hydrogen.Schema.Motion.PathMotion` - Motion along paths
- `Hydrogen.Schema.Motion.Lottie` - Lottie animation data
- `Hydrogen.Schema.Motion.Easing` - Motion-specific easing

### Gestural (Pillar 33-38)
- `Hydrogen.Schema.Gestural.Trigger` - Interaction triggers
- `Hydrogen.Schema.Gestural.Hover` - Hover states
- `Hydrogen.Schema.Gestural.Focus` - Focus states
- `Hydrogen.Schema.Gestural.Keyboard` - Key events
- `Hydrogen.Schema.Gestural.Pointer` - Mouse/touch/pen
- `Hydrogen.Schema.Gestural.Scroll` - Scroll events

---

## WHAT NEEDS TO BE BUILT

### Foundry (Playwright observation engine)

- [ ] Implement full observation protocol:
  - [ ] Hover every interactive element for 300ms
  - [ ] Click elements that respond to click
  - [ ] Focus/blur form elements
  - [ ] Scroll through page in increments
  - [ ] Wait for auto-playing animations
- [ ] Capture state transitions:
  - [ ] Record before/after for each interaction
  - [ ] Extract transition duration from computed styles
  - [ ] Extract easing curves
- [ ] Extract animations:
  - [ ] Detect and extract Lottie JSON
  - [ ] Capture CSS keyframe definitions
  - [ ] Record scroll-linked animation behavior
  - [ ] Sample canvas/WebGL at intervals
- [ ] Emit JSON matching `Hydrogen.Scraper.Types` schema

### Hydrogen.Scraper (already exists, may need extension)

- [ ] Review existing `Hydrogen.Scraper.*` modules
- [ ] Add `StateTransition` type with timing data
- [ ] Add `AnimationObservation` type for continuous animations
- [ ] Add scroll-linked animation support
- [ ] Add Lottie extraction support

### Haskell packages (integration layer)

- [ ] Update `foundry-extract` to use Hydrogen.Scraper types (mirror them)
- [ ] Remove any duplicate type definitions
- [ ] ZMQ client for Playwright communication (already exists)
- [ ] Storage adapters (already exist)

### Delete / Clean Up

- [x] Delete `foundry-core/src/Foundry/Element/*` - duplicates Hydrogen.Element
- [x] Delete `foundry-core/src/Foundry/Event/*` - duplicates Hydrogen.Schema.Gestural
- [x] Delete `foundry-core/src/Foundry/Style/*` - duplicates Hydrogen.Schema.Color
- [x] Delete `foundry-core/src/Foundry/Schema/*` - duplicates Hydrogen.Schema.*
- [x] Delete `src/Brand/*` - wrong approach (authoring, not scraping)

---

## ANTI-PATTERNS TO AVOID

### DO NOT parse CSS strings
```haskell
-- WRONG
parseColor :: Text -> Maybe Color
parseColor "#ff0000" = Just (Color "#ff0000")  -- Still a string!

-- RIGHT
observeColor :: ComputedStyle -> SRGBA
observeColor style = SRGBA r g b a  -- Actual numeric values
```

### DO NOT create duplicate types
```purescript
-- WRONG (in Foundry)
data Color = RGBA Number Number Number Number

-- RIGHT (in Foundry)
import Hydrogen.Schema.Color.SRGB (SRGBA)
```

### DO NOT capture static snapshots only
```typescript
// WRONG
const styles = getComputedStyle(element);
return styles;  // Just initial state

// RIGHT
const initial = captureState(element);
await hover(element);
await wait(300);
const hovered = captureState(element);
return { initial, hovered, transition: detectTransition(initial, hovered) };
```

### DO NOT conflate scraping with authoring
```
-- WRONG: Trying to "extract" brand mission from a webpage
-- (Mission statements are human-authored, not scrapable)

-- RIGHT: Extract only what's visually observable
-- Colors, fonts, spacing, animations, interactions
```

---

## FILE STRUCTURE (Current State)

### Hydrogen (ALL scraper logic lives here)

```
hydrogen/src/Hydrogen/
├── Playwright.purs              # Browser automation bindings
├── Playwright/
│   └── Types.purs               # Browser, Page, Locator types
│
├── Scraper/                     # OBSERVATION ENGINE
│   ├── Observer.purs            # ** 10-20 second observation protocol **
│   ├── Capture.purs             # ** State capture with computed styles **
│   ├── Transition.purs          # ** Timing/easing detection **
│   ├── Animation.purs           # ** Lottie/keyframe/scroll extraction **
│   ├── Extract.purs             # URL → ScrapedPage
│   ├── Parse.purs               # Parsing logic
│   ├── Types.purs               # ExtractedElement, ScrapedPage
│   └── Types/
│       ├── State.purs           # InteractionState, StateDiff
│       ├── Animation.purs       # Animation types
│       ├── Transform.purs       # Transform extraction
│       ├── Gradient.purs        # Gradient extraction
│       ├── SVG.purs             # SVG extraction
│       └── ...
│
├── Schema/                      # All atom types (38 pillars)
│   ├── Color/
│   ├── Geometry/
│   ├── Motion/
│   ├── Temporal/
│   ├── Gestural/
│   └── ...
│
└── Element/                     # Composition back to elements
    ├── Core/
    └── Compound/
```

### Foundry (minimal - mostly docs and Haskell integration)

```
foundry/
├── haskell/                     # Integration layer only
│   ├── foundry-scraper/         # ZMQ client (if needed)
│   ├── foundry-storage/         # Persistence (DuckDB, PostgreSQL)
│   └── foundry-extract/         # Mirrors Hydrogen.Scraper types
│
├── purescript/
│   └── foundry-core/            # EMPTY - imports Hydrogen.Scraper.*
│
└── docs/
    └── FOUNDRY_ARCHITECTURE.md  # THIS FILE
```

---

## SUMMARY

1. **Hydrogen was built for this** - The type system exists to capture any visual element
2. **Foundry is just Playwright + ZMQ** - Browser automation, nothing more
3. **All types live in Hydrogen.Scraper.*** - Foundry imports, never defines
4. **Observe behavior, don't parse CSS** - Watch what happens, record the delta
5. **10-20 seconds of active probing** - Hover, click, focus, scroll everything
6. **Universal parsing** - Amazon, YouTube, Ableton, any website works
7. **Every visual becomes a Hydrogen atom** - Colors, transforms, animations, triggers

---

## FOR FUTURE AI SESSIONS

If you're an AI reading this after compaction:

1. **DO NOT create new types in Foundry** - Import from `Hydrogen.Scraper.*`
2. **DO NOT parse CSS strings** - Use computed values, observe behavior
3. **DO NOT duplicate Hydrogen modules** - If it exists in Hydrogen, use it
4. **DO NOT define "Brand schema" types** - Editorial/Strategy are human-authored, not scrapable
5. **DO understand** - Foundry = Playwright automation, Hydrogen = everything else

The previous implementation was wrong. It had:
- Duplicate Element types (deleted)
- Duplicate Event types (deleted)
- Duplicate Schema types (deleted)
- Brand authoring types (deleted)
- CSS parsing instead of observation

This document is correct. Follow it.

---

*Last Updated: 2026-03-03*
*This document is the source of truth for Foundry architecture.*

---

                                                          // straylight // 2026
