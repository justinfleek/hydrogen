────────────────────────────────────────────────────────────────────────────────
                           // schema // 05 // motion // effects // matte
────────────────────────────────────────────────────────────────────────────────

# Matte Effects

Alpha channel and edge refinement effects for Motion pillar.

## Source Files

- `Motion/Effects/Matte.purs` — Leader module (124 lines)
- `Motion/Effects/Matte/Types.purs` — Core types (377 lines)
- `Motion/Effects/Matte/Operations.purs` — Constructors and serialization (376 lines)
- `Motion/Effects/Matte/Queries.purs` — Predicates and utilities (228 lines)

**Total**: 4 files, ~1,105 lines

────────────────────────────────────────────────────────────────────────────────
                                                          // simple // choker
────────────────────────────────────────────────────────────────────────────────

## SimpleChokerEffect

Basic matte edge expansion/contraction.

### Type Definition

```purescript
type SimpleChokerEffect =
  { chokeMatte :: Number  -- Choke amount (-100 to 100)
  }
```

Positive values contract the matte, negative values expand it.

### Use Cases

- Remove green/blue fringing from keys
- Clean up garbage matte edges
- Expand slightly transparent edges

### Constructors

| Function | Description |
|----------|-------------|
| `defaultSimpleChoker` | No change (0.0) |
| `simpleChokerExpand amt` | Expand matte by amount |
| `simpleChokerContract amt` | Contract matte by amount |
| `simpleChokerWithAmount amt` | Set specific amount |

### Queries

| Function | Description |
|----------|-------------|
| `isChokerExpanding` | Check if chokeMatte < 0 |
| `isChokerContracting` | Check if chokeMatte > 0 |
| `isChokerSignificant` | Check if abs(chokeMatte) >= 5 |
| `combineChokerAmounts` | Add amounts (clamped) |
| `scaleChokerAmount factor` | Scale amount by factor |
| `chokerIntensityRatio` | Percentage of max (0-1) |

────────────────────────────────────────────────────────────────────────────────
                                                           // matte // choker
────────────────────────────────────────────────────────────────────────────────

## MatteChokerEffect

Advanced multi-pass edge refinement.

### Type Definition

```purescript
type MatteChokerEffect =
  { geometricSoftness1 :: GeometricSoftness  -- First pass softness
  , choke1 :: Number                          -- First pass choke (-100 to 100)
  , geometricSoftness2 :: GeometricSoftness  -- Second pass softness
  , choke2 :: Number                          -- Second pass choke (-100 to 100)
  , grayLevelSoftness :: Number               -- Gray edge handling (0-100)
  }
```

### GeometricSoftness Newtype

```purescript
newtype GeometricSoftness = GeometricSoftness Number  -- 0-100

-- Semigroup: combines with min(100, a + b)
geometricSoftness :: Number -> GeometricSoftness
unwrapGeometricSoftness :: GeometricSoftness -> Number
```

### Use Cases

- Multi-pass edge refinement
- Complex key cleanup
- Hair/fine detail preservation

### Constructors

| Function | Description |
|----------|-------------|
| `defaultMatteChoker` | No change |
| `matteChokerWithSpread soft choke` | First pass with specific values |

### Queries

| Function | Description |
|----------|-------------|
| `isMatteChokerDualPass` | Check if both choke1 and choke2 are non-zero |
| `effectiveChokeAmount` | Sum of choke1 + choke2 |
| `clampMatteChokerValues` | Clamp all values to valid ranges |

────────────────────────────────────────────────────────────────────────────────
                                                           // refine // matte
────────────────────────────────────────────────────────────────────────────────

## RefineMatteEffect

Professional edge refinement (Roto Brush output).

### Type Definition

```purescript
type RefineMatteEffect =
  { smooth :: Number               -- Edge smoothing (0-100)
  , feather :: Number              -- Edge feathering (0-250 pixels)
  , choke :: Number                -- Edge contraction (-100 to 100%)
  , shiftEdge :: Number            -- Edge shift (-100 to 100%)
  , reduceChatter :: Number        -- Temporal consistency (0-100)
  , motionBlurMode :: MotionBlurMode
  , motionBlurSamples :: Int       -- Blur samples (1-64)
  , motionBlurShutter :: Number    -- Shutter angle (0-720 degrees)
  , decontaminate :: Boolean       -- Color decontamination
  , decontaminateAmount :: Number  -- Decontamination strength (0-100)
  }
```

### Motion Blur Mode Enum

```purescript
data MotionBlurMode
  = MBMNone            -- No motion blur
  | MBMNormal          -- Standard motion blur
  | MBMHighQuality     -- High quality (more samples)
```

### Refinement Type Enum

```purescript
data RefinementType
  = RTSmooth           -- Smooth edges
  | RTFeather          -- Feathered edges
  | RTChoke            -- Contract edges
  | RTShiftEdge        -- Shift edge inward/outward
  | RTReduceChatter    -- Temporal consistency
```

### Use Cases

- Roto Brush output refinement
- Hair and fine detail edges
- Motion-tracked mattes

### Constructors

| Function | Description |
|----------|-------------|
| `defaultRefineMatte` | Minimal processing |
| `refineMatteWithSmooth amt` | With smooth amount |
| `refineMatteWithFeather amt` | With feather amount |

### Queries

| Function | Description |
|----------|-------------|
| `hasRefineMotionBlur` | Check if motion blur enabled |
| `hasRefineSmooth` | Check if smooth > 0 |
| `hasRefineFeather` | Check if feather > 0 |
| `isRefineMatteComplete` | Check if smooth >= 1 AND feather >= 1 |
| `effectiveFeatherRadius` | feather + (smooth * 0.5) |
| `classifyRefineIntensity` | Returns "heavy", "medium", "light", or "moderate" |

────────────────────────────────────────────────────────────────────────────────
                                                              // set // matte
────────────────────────────────────────────────────────────────────────────────

## SetMatteEffect

Use another layer's channel as matte.

### Type Definition

```purescript
type SetMatteEffect =
  { takeMatteFromLayer :: Int        -- Source layer index
  , useForMatte :: SetMatteChannel   -- Channel to use
  , invertMatte :: Boolean           -- Invert the matte
  , stretchMode :: SetMatteStretch   -- How to fit
  , premultiplyMatte :: Boolean      -- Handle premultiplied
  }
```

### SetMatteChannel Enum

```purescript
data SetMatteChannel
  = SMCRed             -- Red channel
  | SMCGreen           -- Green channel
  | SMCBlue            -- Blue channel
  | SMCAlpha           -- Alpha channel
  | SMCLuminance       -- Luminance (brightness)
  | SMCHue             -- Hue value
  | SMCSaturation      -- Saturation value
  | SMCLightness       -- Lightness value
  | SMCFullOn          -- Full white (no mask)
  | SMCFullOff         -- Full black (full mask)
```

### SetMatteStretch Enum

```purescript
data SetMatteStretch
  = SMSStretch         -- Stretch matte to fit
  | SMSTile            -- Tile matte
  | SMSCenter          -- Center matte (no stretch)
```

### Use Cases

- Luma matte from luminance
- Custom channel extraction
- Layer-based masking

### Constructors

| Function | Description |
|----------|-------------|
| `defaultSetMatte` | Alpha from layer 1 |
| `setMatteFromLayer layer` | Alpha from specific layer |
| `setMatteFromChannel layer channel` | Specific channel from layer |

### Queries

| Function | Description |
|----------|-------------|
| `isSetMatteInverted` | Check if invertMatte is true |

────────────────────────────────────────────────────────────────────────────────
                                                       // channel // combiner
────────────────────────────────────────────────────────────────────────────────

## ChannelCombinerEffect

Combine channels from multiple sources.

### Type Definition

```purescript
type ChannelCombinerEffect =
  { redOutput :: CombinerSource      -- Source for red
  , greenOutput :: CombinerSource    -- Source for green
  , blueOutput :: CombinerSource     -- Source for blue
  , alphaOutput :: CombinerSource    -- Source for alpha
  }
```

### CombinerSource Enum

```purescript
data CombinerSource
  = CSSourceRed        -- Source red channel
  | CSSourceGreen      -- Source green channel
  | CSSourceBlue       -- Source blue channel
  | CSSourceAlpha      -- Source alpha channel
  | CSSourceLuma       -- Source luminance
  | CSLayerRed Int     -- Layer red (by index)
  | CSLayerGreen Int   -- Layer green (by index)
  | CSLayerBlue Int    -- Layer blue (by index)
  | CSLayerAlpha Int   -- Layer alpha (by index)
  | CSLayerLuma Int    -- Layer luminance (by index)
  | CSFullOn           -- Full white
  | CSFullOff          -- Full black
  | CSInvert CombinerSource  -- Inverted source (recursive)
```

### Use Cases

- Channel swapping
- Multi-layer channel composition
- Custom matte construction

### Constructors

| Function | Description |
|----------|-------------|
| `defaultChannelCombiner` | Passthrough (R->R, G->G, B->B, A->A) |
| `channelCombinerWithSources r g b a` | Custom channel mapping |

────────────────────────────────────────────────────────────────────────────────
                                                          // matte // cleanup
────────────────────────────────────────────────────────────────────────────────

## MatteCleanupEffect

General-purpose matte refinement.

### Type Definition

```purescript
type MatteCleanupEffect =
  { blur :: Number                   -- Edge blur (0-100)
  , contrast :: Number               -- Edge contrast (-100 to 100)
  , gamma :: Number                  -- Gamma (0.1-10.0)
  , sizeAdjust :: Number             -- Shrink/expand (-100 to 100)
  , simplify :: Number               -- Edge simplification (0-100)
  , primaryOperation :: CleanupOperation  -- Main operation
  }
```

### CleanupOperation Enum

```purescript
data CleanupOperation
  = COBlur             -- Blur edges
  | COContrast         -- Increase contrast
  | COGamma            -- Gamma correction
  | COShrink           -- Shrink matte
  | COExpand           -- Expand matte
  | COSimplify         -- Simplify edges
```

### Use Cases

- Post-key cleanup
- Garbage matte refinement
- Quick edge fixes

### Constructors

| Function | Description |
|----------|-------------|
| `defaultMatteCleanup` | No change |
| `matteCleanupWithBlur amt` | With blur amount |

### Queries

| Function | Description |
|----------|-------------|
| `hasCleanupBlur` | Check if blur > 0 |
| `hasCleanupContrast` | Check if contrast != 0 |

────────────────────────────────────────────────────────────────────────────────
                                                              // gpu // rendering
────────────────────────────────────────────────────────────────────────────────

## GPU Shader Pattern

Matte effects operate on alpha channels:

```glsl
float newAlpha = refineAlpha(inputAlpha, edgeParams);
outputColor = vec4(inputColor.rgb, newAlpha);
```

All matte operations are designed for efficient GPU processing with bounded
parameters ensuring deterministic rendering.

────────────────────────────────────────────────────────────────────────────────
