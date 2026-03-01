━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                   // 05 // motion // composition
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Composition Settings

Container definitions for motion graphics timelines.

────────────────────────────────────────────────────────────────────────────────
                                                                     // overview
────────────────────────────────────────────────────────────────────────────────

## Purpose

A Composition is the fundamental container for motion graphics — the timeline 
that holds layers, defines dimensions, and sets rendering parameters. This 
module provides:

- **Blend modes** — 28 standard compositing modes (Porter-Duff, SVG spec)
- **Track mattes** — Alpha/luma masking between adjacent layers
- **Color management** — Working color spaces and bit depths
- **Motion blur** — Shutter angle, samples, adaptive sampling
- **Composition settings** — Dimensions, frame rate, duration

**Why this matters for autonomous agents:**

When agents create compositions programmatically, they need bounded enumerations
for blend modes and track mattes — not arbitrary strings. The 28 blend modes
cover all standard compositing operations. The 5 track matte modes cover all
layer masking scenarios. An agent selecting `BMScreen` knows exactly what 
mathematical operation will occur.

Composition settings enforce video encoding constraints (dimensions divisible 
by 8). Invalid configurations cannot be constructed.

## File Map

```
src/Hydrogen/Schema/Motion/Composition.purs    # 474 lines
```

Single file covering composition infrastructure.

────────────────────────────────────────────────────────────────────────────────
                                                                 // blend // mode
────────────────────────────────────────────────────────────────────────────────

## BlendMode (28 variants)

Layer compositing blend modes following Porter-Duff and SVG specifications.
These are the same modes available in professional compositing software and CSS.

### Standard Modes

| Constructor | String ID | Category |
|-------------|-----------|----------|
| `BMNormal` | `"normal"` | Standard |
| `BMMultiply` | `"multiply"` | Standard |
| `BMScreen` | `"screen"` | Standard |
| `BMOverlay` | `"overlay"` | Standard |

### Darken Modes

| Constructor | String ID | Effect |
|-------------|-----------|--------|
| `BMDarken` | `"darken"` | Minimum of base and blend |
| `BMColorBurn` | `"color-burn"` | Darkens base by increasing contrast |
| `BMLinearBurn` | `"linear-burn"` | Darkens base by decreasing brightness |
| `BMDarkerColor` | `"darker-color"` | Selects darker of base or blend |

### Lighten Modes

| Constructor | String ID | Effect |
|-------------|-----------|--------|
| `BMLighten` | `"lighten"` | Maximum of base and blend |
| `BMColorDodge` | `"color-dodge"` | Lightens base by decreasing contrast |
| `BMLinearDodge` | `"linear-dodge"` | Lightens base by increasing brightness |
| `BMLighterColor` | `"lighter-color"` | Selects lighter of base or blend |

### Contrast Modes

| Constructor | String ID | Effect |
|-------------|-----------|--------|
| `BMHardLight` | `"hard-light"` | Multiply or Screen based on blend |
| `BMSoftLight` | `"soft-light"` | Subtle Overlay effect |
| `BMVividLight` | `"vivid-light"` | Burn or Dodge based on blend |
| `BMLinearLight` | `"linear-light"` | Linear Burn or Dodge based on blend |
| `BMPinLight` | `"pin-light"` | Replace based on blend brightness |
| `BMHardMix` | `"hard-mix"` | Posterize to 8 colors |

### Inversion Modes

| Constructor | String ID | Effect |
|-------------|-----------|--------|
| `BMDifference` | `"difference"` | Absolute difference |
| `BMExclusion` | `"exclusion"` | Similar to Difference, lower contrast |
| `BMSubtract` | `"subtract"` | Subtract blend from base |
| `BMDivide` | `"divide"` | Divide base by blend |

### Component Modes

| Constructor | String ID | Effect |
|-------------|-----------|--------|
| `BMHue` | `"hue"` | Hue of blend, saturation/luminosity of base |
| `BMSaturation` | `"saturation"` | Saturation of blend, hue/luminosity of base |
| `BMColor` | `"color"` | Hue/saturation of blend, luminosity of base |
| `BMLuminosity` | `"luminosity"` | Luminosity of blend, hue/saturation of base |

### Arithmetic Modes

| Constructor | String ID | Effect |
|-------------|-----------|--------|
| `BMAdd` | `"add"` | Add blend to base (clamped) |
| `BMDissolve` | `"dissolve"` | Random pixel selection based on opacity |

### Serialization

```purescript
blendModeToString   :: BlendMode -> String
blendModeFromString :: String -> Maybe BlendMode
```

### Predicates

```purescript
isBlendModeAdditive    :: BlendMode -> Boolean
  -- True for: Screen, ColorDodge, LinearDodge, Add, Lighten, LighterColor

isBlendModeSubtractive :: BlendMode -> Boolean
  -- True for: Multiply, ColorBurn, LinearBurn, Darken, DarkerColor, Subtract
```

────────────────────────────────────────────────────────────────────────────────
                                                                // track // matte
────────────────────────────────────────────────────────────────────────────────

## TrackMatteMode (5 variants)

Track mattes use one layer to define the transparency of another. The matte
layer sits directly above the source layer in the stack.

| Constructor | String ID | Source |
|-------------|-----------|--------|
| `TMNone` | `"none"` | No track matte |
| `TMAlpha` | `"alpha"` | Use matte layer's alpha channel |
| `TMAlphaInverted` | `"alpha-inverted"` | Use inverted alpha |
| `TMLuma` | `"luma"` | Use matte layer's luminance |
| `TMLumaInverted` | `"luma-inverted"` | Use inverted luminance |

### How Track Mattes Work

```
Layer Stack:        Result:
┌─────────────┐
│ Matte Layer │ ─────┐     ┌─────────────┐
├─────────────┤      ├────▶│ Source with │
│ Source Layer│ ─────┘     │ matte alpha │
└─────────────┘            └─────────────┘
```

- **Alpha matte**: White areas of matte = source visible, black = transparent
- **Luma matte**: Bright areas = visible, dark = transparent
- **Inverted**: Swap visible/transparent regions

### Serialization

```purescript
trackMatteModeToString   :: TrackMatteMode -> String
trackMatteModeFromString :: String -> Maybe TrackMatteMode
```

────────────────────────────────────────────────────────────────────────────────
                                                                // color // space
────────────────────────────────────────────────────────────────────────────────

## ColorSpace (7 variants)

Working color space for composition rendering.

| Constructor | String ID | Use Case |
|-------------|-----------|----------|
| `CSSrgb` | `"srgb"` | Standard web/display |
| `CSLinearSrgb` | `"linear-srgb"` | Compositing (physically accurate blending) |
| `CSRec709` | `"rec709"` | HD video standard |
| `CSRec2020` | `"rec2020"` | UHD/HDR video |
| `CSDciP3` | `"dci-p3"` | Digital cinema |
| `CSAcesCg` | `"aces-cg"` | ACES computer graphics |
| `CSAces2065` | `"aces-2065"` | ACES full gamut archival |

**Linear vs sRGB:** Compositing should happen in linear space for physically 
accurate results. sRGB applies gamma correction for display. When blending 
layers, linear-sRGB produces correct light mixing.

## BitDepth (3 variants)

Render bit depth per channel.

| Constructor | String ID | Range | Use Case |
|-------------|-----------|-------|----------|
| `BD8Bit` | `"8bpc"` | 0-255 | Standard delivery |
| `BD16Bit` | `"16bpc"` | 0-65535 | High quality gradients |
| `BD32Bit` | `"32bpc"` | Float | HDR, compositing, effects |

**32-bit float:** Values can exceed 0-1 range, preserving highlights and 
enabling exposure adjustment without clipping.

────────────────────────────────────────────────────────────────────────────────
                                                                // motion // blur
────────────────────────────────────────────────────────────────────────────────

## MotionBlurSettings

Motion blur simulates camera shutter by averaging multiple samples across 
the frame duration.

```purescript
newtype MotionBlurSettings = MotionBlurSettings
  { enabled          :: Boolean   -- Motion blur active
  , samplesPerFrame  :: Int       -- Sample count (typically 8-64)
  , shutterAngle     :: Number    -- 0-720 degrees
  , shutterPhase     :: Number    -- -360 to 360 degrees (offset)
  , adaptiveSampling :: Boolean   -- Increase samples for fast motion
  }
```

### Shutter Angle

| Angle | Effect |
|-------|--------|
| 0° | No motion blur |
| 90° | Minimal blur (1/4 frame) |
| 180° | Standard film look (1/2 frame) |
| 360° | Full frame blur |
| 720° | Extreme blur (2 frame duration) |

### Shutter Phase

Offset when the "shutter" opens relative to the frame:
- **0°**: Shutter centered on frame (standard)
- **-90°**: Motion blur trails behind object
- **+90°**: Motion blur leads ahead of object

### Constructors

```purescript
defaultMotionBlurSettings :: MotionBlurSettings
  -- Disabled, 16 samples, 180° shutter, 0° phase, adaptive on

motionBlurEnabled :: Int -> Number -> MotionBlurSettings
  -- Create enabled settings with samples and shutter angle
  -- Values clamped: samples >= 1, angle 0-720
```

────────────────────────────────────────────────────────────────────────────────
                                                     // composition // settings
────────────────────────────────────────────────────────────────────────────────

## CompositionId

Unique identifier for a composition (NonEmptyString semantics).

```purescript
newtype CompositionId = CompositionId String

mkCompositionId :: String -> Maybe CompositionId
  -- Returns Nothing for empty string
```

## CompositionSettings

Complete composition configuration — dimensions, timing, rendering.

```purescript
newtype CompositionSettings = CompositionSettings
  { width           :: Int                -- Pixels, aligned to 8
  , height          :: Int                -- Pixels, aligned to 8
  , frameCount      :: Int                -- Total frames
  , fps             :: FrameRate          -- Frames per second
  , duration        :: Seconds            -- Derived: frameCount / fps
  , backgroundColor :: String             -- Hex color (#RRGGBB)
  , colorSpace      :: ColorSpace         -- Working color space
  , bitDepth        :: BitDepth           -- Render depth
  , motionBlur      :: MotionBlurSettings
  , frameBlending   :: Boolean            -- Enable frame blending
  , autoResize      :: Boolean            -- Auto-resize to content
  }
```

### Invariants

- `width > 0`, aligned to 8-pixel boundary (video encoding requirement)
- `height > 0`, aligned to 8-pixel boundary
- `frameCount >= 0`
- `fps > 0`
- `duration = frameCount / fps` (derived, not settable independently)

### Constructors

```purescript
defaultCompositionSettings :: CompositionSettings
  -- 1920x1080 @ 30fps, 300 frames (10 seconds)
  -- sRGB, 8-bit, black background

mkCompositionSettings 
  :: Int           -- width
  -> Int           -- height  
  -> Int           -- frameCount
  -> FrameRate     -- fps
  -> String        -- backgroundColor
  -> Maybe CompositionSettings
  -- Returns Nothing if any value invalid
  -- Automatically aligns dimensions to 8-pixel boundary
```

### 8-Pixel Alignment

Video codecs (H.264, HEVC, etc.) require dimensions divisible by 8 for 
efficient encoding. The smart constructor enforces this:

```purescript
alignTo8 :: Int -> Int
alignTo8 n = floor ((n + 7) / 8) * 8

-- Examples:
-- alignTo8 1920 = 1920 (already aligned)
-- alignTo8 1921 = 1928
-- alignTo8 1080 = 1080 (already aligned)
```

### Accessors

```purescript
compositionWidth      :: CompositionSettings -> Int
compositionHeight     :: CompositionSettings -> Int
compositionFrameCount :: CompositionSettings -> Int
compositionFps        :: CompositionSettings -> FrameRate
compositionDuration   :: CompositionSettings -> Seconds
```

────────────────────────────────────────────────────────────────────────────────
                                                            // cross-references
────────────────────────────────────────────────────────────────────────────────

## Dependencies

**From Prelude:**
- `Eq`, `Ord`, `Show` — Standard typeclass instances

**From Data.Maybe:**
- `Maybe` — Smart constructors return `Maybe` for validation

**From Data.Int:**
- `floor`, `toNumber` — Used for 8-pixel alignment

**From Hydrogen.Schema.Dimension.Temporal:**
- `FrameRate` — Frames per second newtype
- `Seconds` — Duration newtype

## Related Modules

**Within Motion:**
- `Motion/Layer.purs` — Layers reference composition via CompositionId
- `Motion/Timeline.purs` — Timeline contains CompositionSettings
- `Motion/LayerReference.purs` — Track matte links use TrackMatteMode

**Within Schema:**
- Color pillar for advanced color space operations

## Usage Example

Creating a standard HD composition:

```purescript
import Hydrogen.Schema.Motion.Composition
import Hydrogen.Schema.Dimension.Temporal (FrameRate(FrameRate))
import Data.Maybe (fromJust)

-- Standard HD composition: 1920x1080, 30fps, 10 seconds
hdComp = fromJust $ mkCompositionSettings
  1920
  1080
  300           -- 300 frames at 30fps = 10 seconds
  (FrameRate 30.0)
  "#000000"     -- Black background

-- Access derived duration
duration = compositionDuration hdComp  -- Seconds 10.0

-- 4K composition with HDR settings
fourKHdr = (fromJust $ mkCompositionSettings 3840 2160 600 (FrameRate 60.0) "#000000")
  { colorSpace = CSRec2020
  , bitDepth = BD32Bit
  , motionBlur = motionBlurEnabled 32 180.0
  }
```

────────────────────────────────────────────────────────────────────────────────
