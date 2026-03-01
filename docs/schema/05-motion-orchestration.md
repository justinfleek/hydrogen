━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                 // 05 // motion // orchestration
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Animation Orchestration

Composing animations into sequences, parallels, staggers, and timelines.

────────────────────────────────────────────────────────────────────────────────
                                                                     // overview
────────────────────────────────────────────────────────────────────────────────

## Purpose

Individual animations (fade, slide, scale) are atoms. But real UI requires 
**coordinated motion**: a modal fades in while its backdrop blurs, a list 
staggers its items, a notification slides in then auto-dismisses.

This module provides two complementary systems:

**Transition** — Atomic animation primitives:
- What kind of animation (slide, fade, scale, flip)
- Duration, easing, delay
- Enter/exit pairing for components

**Orchestration** — Composition combinators:
- **Sequence**: Run animations one after another
- **Parallel**: Run animations simultaneously  
- **Stagger**: Run with incremental delays (list reveals)
- **Timeline**: Explicit timing for complex choreography

The algebraic properties matter for agent reasoning:

```
sequence [a, b, c]  ≡  a >> b >> c           -- Duration = sum
parallel [a, b, c]  ≡  a <|> b <|> c         -- Duration = max
stagger 50ms [a, b, c]  ≡  parallel          -- Each offset by interval
  [ delay 0ms a
  , delay 50ms b
  , delay 100ms c
  ]
```

**Why this matters for autonomous agents:**

When agents compose UI animations, they need:
1. Bounded enumerations for transition types (not arbitrary CSS strings)
2. Predictable duration calculations for sequencing
3. Reversible animations for enter/exit pairs
4. Time-scaling for accessibility (reduced motion preferences)

An agent building a modal can compose: `parallel [fadeBackdrop, slideContent]` 
and know the total duration equals the longest child. The type system ensures
valid composition — you cannot create an animation with undefined behavior.

## File Map

```
src/Hydrogen/Schema/Motion/
├── Transition.purs      # 326 lines — Animation primitives
└── Orchestration.purs   # 464 lines — Composition combinators
```

**Total: 2 files, ~790 lines**

────────────────────────────────────────────────────────────────────────────────
                                                                  // transitions
────────────────────────────────────────────────────────────────────────────────

## TransitionType (5 variants)

The type of visual transition — what CSS properties are animated.

| Constructor | Parameters | Animates | Description |
|-------------|------------|----------|-------------|
| `Slide` | `SlideDirection` | transform (translateX/Y) | Movement from edge |
| `Fade` | — | opacity | Transparency change |
| `Scale` | `ScaleOrigin` | transform (scale) | Size change |
| `Flip` | `FlipAxis` | transform (rotateX/Y) | 3D rotation |
| `None` | — | — | Instant, no animation |

### Predicates

```purescript
isAnimated :: TransitionType -> Boolean
  -- True for Slide, Fade, Scale, Flip
  -- False for None

isInstant :: TransitionType -> Boolean
  -- True for None only
```

## SlideDirection (4 variants)

Which edge the element slides from (enter) or to (exit).

| Constructor | String Repr | CSS Transform |
|-------------|-------------|---------------|
| `SlideFromLeft` | `"left"` | translateX(-100%) → translateX(0) |
| `SlideFromRight` | `"right"` | translateX(100%) → translateX(0) |
| `SlideFromTop` | `"top"` | translateY(-100%) → translateY(0) |
| `SlideFromBottom` | `"bottom"` | translateY(100%) → translateY(0) |

### Edge Conversion

```purescript
slideDirectionFromEdge :: Edge -> SlideDirection
  -- Left → SlideFromLeft, Right → SlideFromRight, etc.

slideDirectionToEdge :: SlideDirection -> Edge
  -- Inverse of above

reverseSlideDirection :: SlideDirection -> SlideDirection
  -- SlideFromLeft ↔ SlideFromRight
  -- SlideFromTop ↔ SlideFromBottom
```

## ScaleOrigin (2 variants)

Transform origin for scale transitions.

| Constructor | Parameters | Effect |
|-------------|------------|--------|
| `ScaleFromCenter` | — | Scale from center (default) |
| `ScaleFromEdge` | `Edge` | Scale from specific edge |

**Example:** A dropdown menu scales from `ScaleFromEdge Top` — it appears to 
grow downward from the trigger button.

## FlipAxis (2 variants)

Axis of rotation for 3D flip transitions.

| Constructor | CSS Transform | Visual |
|-------------|---------------|--------|
| `FlipHorizontal` | rotateY(180deg) | Like turning a book page |
| `FlipVertical` | rotateX(180deg) | Like flipping a card up |

## TransitionConfig

Complete transition configuration — the molecule combining type, timing, and easing.

```purescript
type TransitionConfig =
  { transitionType :: TransitionType  -- What animates
  , duration       :: Milliseconds    -- How long
  , easing         :: Easing          -- Acceleration curve
  , delay          :: Milliseconds    -- Wait before starting
  }
```

### Constructors

```purescript
transitionConfig 
  :: TransitionType -> Milliseconds -> Easing -> Milliseconds 
  -> TransitionConfig

noTransition :: TransitionConfig
  -- None, 0ms, linear, 0ms delay

slideTransition :: SlideDirection -> Milliseconds -> Easing -> TransitionConfig
  -- Creates Slide transition with 0ms delay

fadeTransition :: Milliseconds -> Easing -> TransitionConfig
  -- Creates Fade transition with 0ms delay

scaleTransition :: ScaleOrigin -> Milliseconds -> Easing -> TransitionConfig
  -- Creates Scale transition with 0ms delay
```

### Accessors

```purescript
transitionType     :: TransitionConfig -> TransitionType
transitionDuration :: TransitionConfig -> Milliseconds
transitionEasing   :: TransitionConfig -> Easing
transitionDelay    :: TransitionConfig -> Milliseconds
```

## EnterExitConfig

Paired transitions for components that appear and disappear.

```purescript
type EnterExitConfig =
  { enter :: TransitionConfig
  , exit  :: TransitionConfig
  }
```

### Constructors

```purescript
enterExitConfig :: TransitionConfig -> TransitionConfig -> EnterExitConfig
  -- Different enter and exit transitions

symmetricTransition :: TransitionConfig -> EnterExitConfig
  -- Same transition for both enter and exit
```

### Accessors

```purescript
enterConfig :: EnterExitConfig -> TransitionConfig
exitConfig  :: EnterExitConfig -> TransitionConfig
```

## Presets

Common transition configurations for immediate use.

| Preset | Type | Duration | Easing |
|--------|------|----------|--------|
| `instantTransition` | None | 0ms | linear |
| `quickFade` | Fade | 150ms | easeOut |
| `smoothSlide` | Slide (right) | 300ms | easeInOut |
| `bouncyScale` | Scale (center) | 400ms | easeOutBack |
| `gentleFade` | Fade | 250ms | easeInOut |

**Usage:**

```purescript
import Hydrogen.Schema.Motion.Transition (quickFade, smoothSlide)

-- Modal backdrop uses quick fade
backdropTransition = quickFade

-- Drawer slides in from right
drawerTransition = smoothSlide
```

────────────────────────────────────────────────────────────────────────────────
                                                                // orchestration
────────────────────────────────────────────────────────────────────────────────

## AnimationRef

Reference to an element and its animation configuration.

```purescript
type AnimationRef =
  { targetId :: String           -- DOM element identifier
  , config   :: TransitionConfig -- How to animate it
  }
```

### Constructors

```purescript
animate :: String -> TransitionConfig -> AnimationRef
  -- animate "modal-backdrop" quickFade

animateWithConfig :: { targetId :: String, config :: TransitionConfig } -> AnimationRef
  -- Explicit record constructor
```

## Orchestration ADT (6 variants)

Recursive structure for composing animations. Leaves are single animations;
branches are composition strategies.

| Constructor | Parameters | Duration Calculation |
|-------------|------------|----------------------|
| `Single` | `AnimationRef` | config.duration |
| `Sequence` | `Array Orchestration` | sum of all |
| `Parallel` | `Array Orchestration` | max of all |
| `Stagger` | `Milliseconds, Array Orchestration` | lastStart + lastDuration |
| `Delayed` | `Milliseconds, Orchestration` | delay + inner |
| `Timeline` | `Array TimelineEntry` | max(entry.time + entry.duration) |

```purescript
data Orchestration
  = Single AnimationRef
  | Sequence (Array Orchestration)
  | Parallel (Array Orchestration)
  | Stagger Milliseconds (Array Orchestration)
  | Delayed Milliseconds Orchestration
  | Timeline (Array TimelineEntry)
```

## Combinators

### sequence

Run animations one after another. Total duration = sum of all durations.

```purescript
sequence :: Array Orchestration -> Orchestration

-- Example: fade in, then slide up, then scale
sequence [fadeIn, slideUp, scaleIn]
-- fadeIn completes → slideUp starts → scaleIn starts
```

### parallel

Run animations simultaneously. Total duration = max of all durations.

```purescript
parallel :: Array Orchestration -> Orchestration

-- Example: backdrop fades while content slides
parallel [fadeBackdrop, slideContent, scaleButton]
-- All three start at t=0
```

### stagger

Run animations with incremental start delays. Creates cascading reveal effects.

```purescript
stagger :: Milliseconds -> Array Orchestration -> Orchestration

-- Example: list items appear one by one
stagger (ms 50) [item1, item2, item3, item4]
-- item1 at 0ms, item2 at 50ms, item3 at 100ms, item4 at 150ms
```

### staggerReverse

Stagger in reverse order — last item starts first. Useful for exit animations
where items should leave in reverse order of appearance.

```purescript
staggerReverse :: Milliseconds -> Array Orchestration -> Orchestration
```

### timeline

Explicit timing control. Unlike sequence/parallel/stagger, timeline gives 
complete control over when each animation starts.

```purescript
timeline :: Array TimelineEntry -> Orchestration

-- Example: precise choreography
timeline
  [ at (ms 0)   titleFade
  , at (ms 200) subtitleFade
  , at (ms 500) buttonScale
  ]
```

### delay

Add delay before an animation.

```purescript
delay :: Milliseconds -> Orchestration -> Orchestration

-- Wait 300ms, then start fadeIn
delay (ms 300) fadeIn
```

### at

Create a timeline entry at a specific time. Convenience for building timelines.

```purescript
at :: Milliseconds -> Orchestration -> TimelineEntry
```

## TimelineEntry

A point in a timeline with an associated animation.

```purescript
newtype TimelineEntry = TimelineEntry
  { time      :: Milliseconds   -- When this animation starts
  , animation :: Orchestration  -- What plays at this time
  }
```

### Constructors and Accessors

```purescript
timelineEntry :: Milliseconds -> Orchestration -> TimelineEntry

entryTime      :: TimelineEntry -> Milliseconds
entryAnimation :: TimelineEntry -> Orchestration
```

## Inspection Functions

### totalDuration

Calculate the total duration of an orchestration tree.

```purescript
totalDuration :: Orchestration -> Milliseconds
```

Duration calculations by type:

| Type | Formula |
|------|---------|
| Single | config.duration |
| Sequence | sum(children.duration) |
| Parallel | max(children.duration) |
| Stagger | (count - 1) × interval + lastChild.duration |
| Delayed | delay + inner.duration |
| Timeline | max(entry.time + entry.animation.duration) |

### animationCount

Count total number of animations in the tree.

```purescript
animationCount :: Orchestration -> Int
```

### allRefs

Get all target IDs referenced in the orchestration.

```purescript
allRefs :: Orchestration -> Array String
```

## Predicates

```purescript
isEmpty :: Orchestration -> Boolean
  -- True if orchestration has no animations

isSequential :: Orchestration -> Boolean
  -- True for Sequence constructor

isParallel :: Orchestration -> Boolean
  -- True for Parallel constructor

isStaggered :: Orchestration -> Boolean
  -- True for Stagger constructor
```

## Operations

### reverse

Reverse the order of animations. Useful for creating exit animations from 
enter animations.

```purescript
reverse :: Orchestration -> Orchestration
```

- **Single**: unchanged
- **Sequence**: reverse array, recursively reverse children
- **Parallel**: recursively reverse children (order doesn't matter)
- **Stagger**: reverse array, recursively reverse children
- **Timeline**: recalculate times so animations play in reverse order

### scale

Scale all durations by a factor.

```purescript
scale :: Number -> Orchestration -> Orchestration

-- Everything takes twice as long
scale 2.0 animation

-- Everything takes half the time (reduced motion)
scale 0.5 animation
```

### shiftBy

Shift all timing by a duration. Useful for inserting animations into 
existing timelines.

```purescript
shiftBy :: Milliseconds -> Orchestration -> Orchestration
```

### append

Append one orchestration after another. Equivalent to `sequence [a, b]`.

```purescript
append :: Orchestration -> Orchestration -> Orchestration
```

────────────────────────────────────────────────────────────────────────────────
                                                            // cross-references
────────────────────────────────────────────────────────────────────────────────

## Dependencies

**From Prelude:**
- `Eq`, `Ord`, `Show` — Standard typeclass instances

**From Hydrogen.Schema.Dimension.Temporal:**
- `Milliseconds` — Duration newtype
- `ms` — Milliseconds constructor

**From Hydrogen.Schema.Motion.Easing:**
- `Easing` — Acceleration curves
- `linear`, `easeOut`, `easeInOut`, `easeOutBack` — Preset easings

**From Hydrogen.Schema.Geometry.Position:**
- `Edge` — Top, Bottom, Left, Right for slide directions

## Related Modules

**Within Motion:**
- `Motion/Easing.purs` — Easing curves used by TransitionConfig
- `Motion/Temporal.purs` — Duration types (Milliseconds, Seconds)

**Component Consumers:**
- `Component/Carousel` — Slide transitions between items
- `Component/Modal` — Enter/exit animations
- `Component/Drawer` — Slide in/out from edge
- `Component/Toast` — Notification appear/dismiss
- `Component/Accordion` — Expand/collapse sections

## Usage Examples

### Modal Enter Animation

Backdrop fades while content slides up simultaneously:

```purescript
import Hydrogen.Schema.Motion.Orchestration as O
import Hydrogen.Schema.Motion.Transition 
  ( fadeTransition, slideTransition, SlideDirection(..) )
import Hydrogen.Schema.Motion.Easing (easeOut, easeOutBack)
import Hydrogen.Schema.Dimension.Temporal (ms)

modalEnter :: Orchestration
modalEnter = O.parallel
  [ O.Single $ O.animate "backdrop" 
      (fadeTransition (ms 200) easeOut)
  , O.Single $ O.animate "content" 
      (slideTransition SlideFromBottom (ms 300) easeOutBack)
  ]

-- Total duration: max(200, 300) = 300ms
```

### Staggered List Reveal

Items appear one by one with 50ms delays:

```purescript
listReveal :: Array String -> Orchestration
listReveal itemIds = O.stagger (ms 50) $
  map (\id -> O.Single $ O.animate id quickFade) itemIds

-- For 4 items: total duration = 3 × 50 + 150 = 300ms
```

### Complex Timeline

Precise choreography with explicit timing:

```purescript
heroAnimation :: Orchestration
heroAnimation = O.timeline
  [ O.at (ms 0) $ O.Single $ O.animate "title" 
      (fadeTransition (ms 400) easeOut)
  , O.at (ms 200) $ O.Single $ O.animate "subtitle" 
      (fadeTransition (ms 400) easeOut)
  , O.at (ms 400) $ O.parallel
      [ O.Single $ O.animate "cta-primary" bouncyScale
      , O.Single $ O.animate "cta-secondary" bouncyScale
      ]
  ]

-- title starts at 0ms
-- subtitle starts at 200ms (overlaps with title)
-- both buttons start at 400ms
```

### Creating Exit from Enter

Use `reverse` to create an exit animation:

```purescript
modalExit :: Orchestration
modalExit = O.reverse modalEnter

-- Content slides down while backdrop fades
-- Animations play in reverse order
```

### Accessibility: Reduced Motion

Scale durations for users who prefer reduced motion:

```purescript
withReducedMotion :: Boolean -> Orchestration -> Orchestration
withReducedMotion true  = O.scale 0.0  -- Instant
withReducedMotion false = identity

-- Or use a multiplier
withMotionScale :: Number -> Orchestration -> Orchestration
withMotionScale factor = O.scale factor
```

────────────────────────────────────────────────────────────────────────────────

