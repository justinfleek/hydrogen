━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                       // 05 // motion // lottie
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Vector Animation Interchange

JSON-based vector animation data and playback configuration.

────────────────────────────────────────────────────────────────────────────────
                                                                     // overview
────────────────────────────────────────────────────────────────────────────────

## Purpose

Vector animations exported from professional motion graphics tools can be 
played in web environments using JSON-based interchange formats. This module 
provides the complete type vocabulary for configuring such animations:

- **Source** — URL or inline JSON data
- **Playback** — Speed, loop, direction, autoplay
- **Segments** — Play specific frame ranges or named markers
- **Triggers** — When to start (load, hover, click, scroll, manual)
- **Rendering** — SVG, Canvas, or HTML backends

**Why this matters for autonomous agents:**

When agents add animations to interfaces, they need bounded configurations —
not arbitrary JavaScript options objects. This module provides:

1. **Bounded speed** (0.1× to 10×) — no infinite loops from speed=0
2. **Enumerated triggers** — 5 ways to start, all explicit
3. **Segment specifications** — frame ranges or marker names, validated
4. **Preset configurations** — common patterns (spinner, hover, click)

An agent building a loading state can use `loadingSpinner "/spinner.json"` and
know the configuration is correct by construction. No runtime errors from 
misconfigured loop counts or invalid speeds.

## Use Cases

| Use Case | Preset | Trigger |
|----------|--------|---------|
| Loading spinners | `loadingSpinner` | TriggerOnLoad |
| Hover effects | `hoverAnimation` | TriggerOnHover |
| Click feedback | `clickAnimation` | TriggerOnClick |
| Scroll reveals | `scrollAnimation` | TriggerOnEnter |
| Success/error | `successAnimation` | TriggerManual |

## File Map

```
src/Hydrogen/Schema/Motion/Lottie.purs    # 653 lines
```

Single comprehensive file covering all vector animation configuration.

────────────────────────────────────────────────────────────────────────────────
                                                                      // source
────────────────────────────────────────────────────────────────────────────────

## LottieSource (2 variants)

Where the animation data comes from.

| Constructor | Parameters | Description |
|-------------|------------|-------------|
| `LottieUrl` | `String` | URL to .json animation file |
| `LottieInline` | `String` | Inline JSON animation data |

```purescript
data LottieSource
  = LottieUrl String
  | LottieInline String
```

### Constructors

```purescript
lottieUrl    :: String -> LottieSource
lottieInline :: String -> LottieSource
```

**When to use each:**

- **URL**: Production — smaller bundle, cacheable, CDN-friendly
- **Inline**: Development, SSR, or when animation must work offline

────────────────────────────────────────────────────────────────────────────────
                                                                    // playback
────────────────────────────────────────────────────────────────────────────────

## PlaybackDirection (3 variants)

Animation playback direction.

| Constructor | String Repr | Description |
|-------------|-------------|-------------|
| `Forward` | `"forward"` | Play from start to end |
| `Reverse` | `"reverse"` | Play from end to start |
| `Alternate` | `"alternate"` | Ping-pong between forward and reverse |

## LoopMode (2 variants)

How many times to repeat the animation.

| Constructor | Parameters | Description |
|-------------|------------|-------------|
| `LoopInfinite` | — | Loop forever until stopped |
| `LoopCount` | `Int` | Loop n times (1 = play once) |

```purescript
data LoopMode
  = LoopInfinite
  | LoopCount Int
```

## LottiePlayback

Complete playback configuration.

```purescript
newtype LottiePlayback = LottiePlayback
  { autoplay         :: Boolean            -- Start playing on load
  , loop             :: LoopMode           -- Loop behavior
  , speed            :: Number             -- 0.1 to 10.0 (clamped)
  , direction        :: PlaybackDirection  -- Forward, Reverse, Alternate
  , delayMs          :: Number             -- Delay before starting (ms)
  , pauseOnHoverExit :: Boolean            -- Pause when mouse leaves
  , resetOnComplete  :: Boolean            -- Reset to frame 0 when done
  }
```

### Speed Bounds

Speed is clamped to **0.1 to 10.0**:
- Below 0.1 is effectively paused (use pause controls instead)
- Above 10.0 is too fast to perceive

### Constructor

```purescript
lottiePlayback
  :: { autoplay :: Boolean
     , loop :: LoopMode
     , speed :: Number
     , direction :: PlaybackDirection
     , delayMs :: Number
     , pauseOnHoverExit :: Boolean
     , resetOnComplete :: Boolean
     }
  -> LottiePlayback
```

## Playback Presets

| Preset | Autoplay | Loop | Speed | Direction | Use Case |
|--------|----------|------|-------|-----------|----------|
| `defaultPlayback` | true | infinite | 1.0× | forward | General purpose |
| `autoplayLoop` | true | infinite | 1.0× | forward | Decorative loops |
| `playOnce` | true | 1 | 1.0× | forward | One-shot animations |
| `playAlternate` | true | infinite | 1.0× | alternate | Ping-pong effects |
| `manualPlayback` | false | 1 | 1.0× | forward | Programmatic control |
| `slowMotion` | true | infinite | 0.5× | forward | Subtle effects |
| `fastPlayback` | true | infinite | 2.0× | forward | Quick feedback |

```purescript
defaultPlayback  :: LottiePlayback  -- autoplay, loop forever, 1x
autoplayLoop     :: LottiePlayback  -- same as default
playOnce         :: LottiePlayback  -- play once, reset on complete
playAlternate    :: LottiePlayback  -- ping-pong forever
manualPlayback   :: LottiePlayback  -- no autoplay, for triggers
slowMotion       :: LottiePlayback  -- 0.5x speed
fastPlayback     :: LottiePlayback  -- 2x speed
```

────────────────────────────────────────────────────────────────────────────────
                                                                    // segments
────────────────────────────────────────────────────────────────────────────────

## LottieSegment (4 variants)

Which portion of the animation to play.

| Constructor | Parameters | Description |
|-------------|------------|-------------|
| `SegmentFull` | — | Play entire animation |
| `SegmentFrames` | `Int, Int` | Play from startFrame to endFrame (inclusive) |
| `SegmentMarker` | `String` | Play segment defined by single marker |
| `SegmentMarkerRange` | `String, String` | Play from startMarker to endMarker |

```purescript
data LottieSegment
  = SegmentFull
  | SegmentFrames Int Int
  | SegmentMarker String
  | SegmentMarkerRange String String
```

### Frame Numbers

Frames are **0-indexed integers**. A typical 2-second animation at 30fps has
frames 0-59.

### Markers

Professional motion graphics tools allow naming frames with markers. Reference
markers by name rather than frame number — makes animations more maintainable
when timings change.

### Constructor

```purescript
lottieSegment :: Int -> Int -> LottieSegment
  -- Clamps negative frames to 0
  -- Swaps start/end if start > end
```

## Segment Helpers

| Function | Result | Use Case |
|----------|--------|----------|
| `fullAnimation` | `SegmentFull` | Play everything |
| `frameRange 0 30` | `SegmentFrames 0 30` | Specific frame range |
| `markerSegment "intro"` | `SegmentMarker "intro"` | Named marker |
| `markerRange "hover_start" "hover_end"` | `SegmentMarkerRange ...` | Between markers |
| `firstHalf 60` | `SegmentFrames 0 30` | First half (for hover-in) |
| `secondHalf 60` | `SegmentFrames 30 60` | Second half (for hover-out) |
| `singleFrame 15` | `SegmentFrames 15 15` | Single frame (paused state) |

```purescript
fullAnimation   :: LottieSegment
frameRange      :: Int -> Int -> LottieSegment
markerSegment   :: String -> LottieSegment
markerRange     :: String -> String -> LottieSegment
firstHalf       :: Int -> LottieSegment  -- totalFrames -> first half
secondHalf      :: Int -> LottieSegment  -- totalFrames -> second half
singleFrame     :: Int -> LottieSegment  -- frame -> single frame
```

────────────────────────────────────────────────────────────────────────────────
                                                                    // triggers
────────────────────────────────────────────────────────────────────────────────

## LottieTrigger (5 variants)

When to start playing the animation.

| Constructor | String Repr | When it Plays |
|-------------|-------------|---------------|
| `TriggerOnLoad` | `"on-load"` | Immediately when element loads |
| `TriggerOnHover` | `"on-hover"` | When mouse enters element |
| `TriggerOnClick` | `"on-click"` | When element is clicked |
| `TriggerOnEnter` | `"on-enter"` | When element enters viewport (scroll) |
| `TriggerManual` | `"manual"` | Never auto-plays — programmatic control |

```purescript
data LottieTrigger
  = TriggerOnLoad
  | TriggerOnHover
  | TriggerOnClick
  | TriggerOnEnter
  | TriggerManual
```

### Trigger Patterns

| Pattern | Trigger | Playback | Behavior |
|---------|---------|----------|----------|
| Loading spinner | OnLoad | autoplayLoop | Plays forever on load |
| Hover icon | OnHover | manualPlayback | Plays on hover, pauses on leave |
| Click feedback | OnClick | playOnce | Plays once per click |
| Scroll reveal | OnEnter | playOnce | Plays once when scrolled into view |
| Form success | Manual | playOnce | Agent triggers after validation |

────────────────────────────────────────────────────────────────────────────────
                                                                   // rendering
────────────────────────────────────────────────────────────────────────────────

## LottieRenderer (3 variants)

How to render the animation to the DOM.

| Constructor | String Repr | Trade-offs |
|-------------|-------------|------------|
| `RendererSvg` | `"svg"` | Best quality, most compatible, slower for complex animations |
| `RendererCanvas` | `"canvas"` | Better performance, no element inspection, resolution-dependent |
| `RendererHtml` | `"html"` | DOM elements, limited feature support, best accessibility |

```purescript
data LottieRenderer
  = RendererSvg
  | RendererCanvas
  | RendererHtml
```

### Choosing a Renderer

| Scenario | Recommended |
|----------|-------------|
| General use | `RendererSvg` |
| Complex animations (many shapes/masks) | `RendererCanvas` |
| Need to inspect/style elements | `RendererSvg` or `RendererHtml` |
| Performance-critical | `RendererCanvas` |
| Accessibility priority | `RendererHtml` |

────────────────────────────────────────────────────────────────────────────────
                                                                   // animation
────────────────────────────────────────────────────────────────────────────────

## LottieAnimation

Complete animation configuration — the compound type composing all settings.

```purescript
newtype LottieAnimation = LottieAnimation
  { source              :: LottieSource    -- URL or inline JSON
  , playback            :: LottiePlayback  -- Speed, loop, direction
  , segment             :: LottieSegment   -- Which frames to play
  , trigger             :: LottieTrigger   -- When to start
  , renderer            :: LottieRenderer  -- SVG, Canvas, or HTML
  , preserveAspectRatio :: String          -- SVG preserveAspectRatio attr
  , className           :: String          -- CSS class for container
  , ariaLabel           :: String          -- Accessibility label
  }
```

### preserveAspectRatio

Standard SVG values:

| Value | Behavior |
|-------|----------|
| `"xMidYMid meet"` | Center, fit within bounds (default) |
| `"xMidYMid slice"` | Center, fill and clip |
| `"xMinYMin meet"` | Top-left, fit within bounds |
| `"none"` | Stretch to fill (no aspect ratio) |

## Constructors

### Full Configuration

```purescript
lottieAnimation
  :: { source :: LottieSource
     , playback :: LottiePlayback
     , segment :: LottieSegment
     , trigger :: LottieTrigger
     , renderer :: LottieRenderer
     , preserveAspectRatio :: String
     , className :: String
     , ariaLabel :: String
     }
  -> LottieAnimation
```

### Convenience Constructors

```purescript
defaultLottie :: LottieSource -> LottieAnimation
  -- Sensible defaults: SVG, autoplay, loop, full animation

fromUrl :: String -> LottieTrigger -> LottieAnimation
  -- URL + trigger, everything else defaulted

fromInline :: String -> LottieAnimation
  -- Inline JSON, autoplay on load
```

## Presets

Pre-configured animations for common patterns.

### loadingSpinner

```purescript
loadingSpinner :: String -> LottieAnimation
  -- URL -> spinner that loops forever
  -- Trigger: OnLoad
  -- Playback: autoplayLoop
  -- className: "loading-spinner"
  -- ariaLabel: "Loading"
```

### hoverAnimation

```purescript
hoverAnimation :: String -> LottieAnimation
  -- URL -> plays on hover, pauses on leave
  -- Trigger: OnHover
  -- Playback: manualPlayback (pauseOnHoverExit = true)
  -- ariaLabel: "Interactive animation"
```

### clickAnimation

```purescript
clickAnimation :: String -> LottieAnimation
  -- URL -> plays once per click
  -- Trigger: OnClick
  -- Playback: playOnce
```

### scrollAnimation

```purescript
scrollAnimation :: String -> LottieAnimation
  -- URL -> plays once when scrolled into view
  -- Trigger: OnEnter
  -- Playback: playOnce
```

### successAnimation / errorAnimation

```purescript
successAnimation :: String -> LottieAnimation
  -- URL -> manual trigger, plays once
  -- className: "success-animation"
  -- ariaLabel: "Success"

errorAnimation :: String -> LottieAnimation
  -- URL -> manual trigger, plays once
  -- className: "error-animation"
  -- ariaLabel: "Error"
```

**Usage for form feedback:**
```purescript
-- Agent triggers animation after validation
onFormSubmit = do
  result <- validateForm
  case result of
    Valid   -> triggerAnimation "success-anim"
    Invalid -> triggerAnimation "error-anim"
```

────────────────────────────────────────────────────────────────────────────────
                                                            // cross-references
────────────────────────────────────────────────────────────────────────────────

## Dependencies

**From Prelude:**
- `Eq`, `Ord`, `Show` — Standard typeclass instances

No external dependencies — this module is self-contained.

## Related Modules

**Within Motion:**
- `Motion/Orchestration.purs` — For sequencing animations with other transitions
- `Motion/Transition.purs` — CSS-based transitions (complementary approach)

**Component Consumers:**
- `Component/Button` — Click feedback animations
- `Component/Loading` — Spinner states
- `Component/Form` — Success/error feedback
- `Component/Card` — Hover effects

## Usage Examples

### Loading Spinner

```purescript
import Hydrogen.Schema.Motion.Lottie (loadingSpinner)

-- Simple loading state
spinner = loadingSpinner "/animations/spinner.json"

-- In a loading view:
loadingView = div
  [ lottiePlayer spinner
  , text "Loading..."
  ]
```

### Interactive Hover Icon

```purescript
import Hydrogen.Schema.Motion.Lottie 
  ( LottieAnimation(..)
  , hoverAnimation
  , markerRange
  )

-- Menu icon that animates on hover
menuIcon = let
  base = hoverAnimation "/animations/menu-hamburger.json"
  (LottieAnimation cfg) = base
  in LottieAnimation $ cfg
    { segment = markerRange "closed" "open"
    }
```

### Click Feedback

```purescript
import Hydrogen.Schema.Motion.Lottie (clickAnimation)

-- Like button with heart animation
likeButton = button
  [ onClick LikeClicked ]
  [ lottiePlayer $ clickAnimation "/animations/heart-burst.json"
  ]
```

### Scroll-Triggered Reveal

```purescript
import Hydrogen.Schema.Motion.Lottie (scrollAnimation)

-- Hero illustration that plays when scrolled into view
heroSection = section
  [ class_ "hero" ]
  [ lottiePlayer $ scrollAnimation "/animations/hero-entrance.json"
  , heading "Welcome"
  ]
```

### Custom Configuration

```purescript
import Hydrogen.Schema.Motion.Lottie

-- Slow-motion background animation with custom settings
backgroundAnim = lottieAnimation
  { source: LottieUrl "/animations/abstract-bg.json"
  , playback: lottiePlayback
      { autoplay: true
      , loop: LoopInfinite
      , speed: 0.3          -- Very slow
      , direction: Alternate -- Ping-pong
      , delayMs: 1000.0     -- Wait 1 second
      , pauseOnHoverExit: false
      , resetOnComplete: false
      }
  , segment: fullAnimation
  , trigger: TriggerOnLoad
  , renderer: RendererCanvas  -- Better performance
  , preserveAspectRatio: "xMidYMid slice"  -- Fill container
  , className: "bg-animation"
  , ariaLabel: "Background decoration"
  }
```

### Form Validation Feedback

```purescript
import Hydrogen.Schema.Motion.Lottie (successAnimation, errorAnimation)

-- Define animations
formSuccess = successAnimation "/animations/checkmark.json"
formError = errorAnimation "/animations/error-shake.json"

-- Usage in form handler
handleSubmit formData = do
  result <- submitToServer formData
  case result of
    Success _ -> do
      showAnimation "success-feedback" formSuccess
      navigateTo SuccessPage
    Error msg -> do
      showAnimation "error-feedback" formError
      showMessage msg
```

────────────────────────────────────────────────────────────────────────────────

