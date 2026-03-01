────────────────────────────────────────────────────────────────────────────────
                         // schema // 05 // motion // effects // generate
────────────────────────────────────────────────────────────────────────────────

# Generate Effects

Procedural content generation effects for Motion pillar.

## Source Files

- `Motion/Effects/Generate.purs` — Leader module (154 lines)
- `Motion/Effects/Generate/Gradient.purs` — Gradient effects (205 lines)
- `Motion/Effects/Generate/Patterns.purs` — Pattern effects (407 lines)
- `Motion/Effects/Generate/Shapes.purs` — Shape effects (356 lines)
- `Motion/Effects/Generate/Animation.purs` — Animated effects (225 lines)

**Total**: 5 files, ~1,347 lines

────────────────────────────────────────────────────────────────────────────────
                                                              // gradient // ramp
────────────────────────────────────────────────────────────────────────────────

## GradientRampEffect

Linear or radial gradient fill.

### Type Definition

```purescript
type GradientRampEffect =
  { startPoint :: Point2D        -- Start of gradient
  , endPoint :: Point2D          -- End of gradient
  , startColor :: RGB            -- Color at start
  , endColor :: RGB              -- Color at end
  , rampShape :: RampShape       -- Linear or radial
  , scatter :: Number            -- Random scatter (0-100)
  , blendWithOriginal :: Number  -- Blend amount (0-100)
  }
```

### Ramp Shape Enum

```purescript
data RampShape
  = RSLinear       -- Linear gradient (straight line)
  | RSRadial       -- Radial gradient (circular)
```

### Constructors

| Function | Description |
|----------|-------------|
| `defaultGradientRamp` | Black to white, linear, top to bottom |
| `linearGradientRamp start end startCol endCol` | Linear gradient |
| `radialGradientRamp start end startCol endCol` | Radial gradient |

### Queries

| Function | Description |
|----------|-------------|
| `hasGradientScatter` | Check if scatter > 0 |
| `combineGradientScatter` | Add scatter values (clamped to 0-100) |

────────────────────────────────────────────────────────────────────────────────
                                                           // four-color gradient
────────────────────────────────────────────────────────────────────────────────

## FourColorGradientEffect

Four-corner gradient with blend and jitter.

### Type Definition

```purescript
type FourColorGradientEffect =
  { point1 :: Point2D            -- Corner 1 position
  , color1 :: RGB                -- Corner 1 color
  , point2 :: Point2D            -- Corner 2 position
  , color2 :: RGB                -- Corner 2 color
  , point3 :: Point2D            -- Corner 3 position
  , color3 :: RGB                -- Corner 3 color
  , point4 :: Point2D            -- Corner 4 position
  , color4 :: RGB                -- Corner 4 color
  , blend :: Number              -- Gradient blend amount (0-100)
  , jitter :: Number             -- Add noise (0-100)
  , opacity :: Number            -- Overall opacity (0-100)
  , blendMode :: BlendMode       -- Compositing mode
  }
```

### Constructors

| Function | Description |
|----------|-------------|
| `defaultFourColorGradient` | 200x200, RGBY corners, 50% blend |

────────────────────────────────────────────────────────────────────────────────
                                                               // cell // pattern
────────────────────────────────────────────────────────────────────────────────

## CellPatternEffect

Procedural cellular texture generation.

### Type Definition

```purescript
type CellPatternEffect =
  { cellType :: CellType         -- Type of cell pattern
  , size :: Number               -- Cell size (1-1000)
  , offset :: Point2D            -- Pattern offset
  , evolution :: Number          -- Evolution (0-360 degrees, animatable)
  , contrast :: Number           -- Edge contrast (0-100)
  , randomSeed :: Int            -- Random seed for reproducibility
  , invert :: Boolean            -- Invert output
  }
```

### Cell Type Enum

```purescript
data CellType
  = CTBubbles          -- Circular cells
  | CTPipes            -- Connected pipe-like cells
  | CTCrystals         -- Angular crystal-like cells
  | CTMixed            -- Mix of cell types
  | CTPlates           -- Flat plate-like cells
  | CTSoft             -- Soft-edged cells
```

### Constructors

| Function | Description |
|----------|-------------|
| `defaultCellPattern` | Bubbles, size 50 |
| `cellPatternWithType ct sz` | Specific type and size |

### Queries

| Function | Description |
|----------|-------------|
| `isCellPatternInverted` | Check if inverted |
| `combineCellEvolution` | Add evolution values (clamped to 0-360) |

────────────────────────────────────────────────────────────────────────────────
                                                                  // checkerboard
────────────────────────────────────────────────────────────────────────────────

## CheckerboardEffect

Alternating square pattern.

### Type Definition

```purescript
type CheckerboardEffect =
  { anchor :: Point2D            -- Pattern anchor
  , size :: { width :: Number, height :: Number }  -- Square size (1-1000 each)
  , feather :: Number            -- Edge feather (0-100)
  , color :: RGB                 -- Checker color
  , opacity :: Number            -- Opacity (0-100)
  , blendMode :: BlendMode       -- Compositing mode
  }
```

### Constructors

| Function | Description |
|----------|-------------|
| `defaultCheckerboard` | 100x100, black |
| `checkerboardWithSize w h col` | Specific size and color |

─────────────────────────────────────��──────────────────────────────────────────
                                                                         // grid
────────────────────────────────────────────────────────────────────────────────

## GridEffect

Regular grid pattern (lines or rectangles).

### Type Definition

```purescript
type GridEffect =
  { anchor :: Point2D            -- Grid anchor
  , corner :: Point2D            -- Grid corner (defines cell size)
  , gridType :: GridType         -- Lines or rectangles
  , border :: Number             -- Line thickness (0-100)
  , feather :: Number            -- Edge feather (0-100)
  , color :: RGB                 -- Grid color
  , opacity :: Number            -- Opacity (0-100)
  , blendMode :: BlendMode       -- Compositing mode
  }
```

### Grid Type Enum

```purescript
data GridType
  = GTLines           -- Lines only
  | GTRectangles      -- Filled rectangles
```

### Constructors

| Function | Description |
|----------|-------------|
| `defaultGrid` | 100x100 cells, 1px lines, white |
| `gridWithSize w h col` | Specific cell size and color |

────────────────────────────────────────────────────────────────────────────────
                                                                      // fractal
────────────────────────────────────────────────────────────────────────────────

## FractalEffect

Procedural fractal noise generation.

### Type Definition

```purescript
type FractalEffect =
  { fractalType :: FractalNoiseType  -- Noise algorithm
  , contrast :: Number           -- Output contrast (-200 to 200)
  , brightness :: Number         -- Output brightness (-200 to 200)
  , scale :: Number              -- Pattern scale (1-10000 %)
  , uniformScaling :: Boolean    -- Lock X/Y scale
  , offset :: Point2D            -- Pattern offset
  , rotation :: Number           -- Pattern rotation (0-360)
  , complexity :: Number         -- Octave count (1-20)
  , subInfluence :: Number       -- Sub-octave influence (0-100)
  , evolution :: Number          -- Evolution (0-360, animatable)
  , cycleEvolution :: Boolean    -- Cycle evolution
  , randomSeed :: Int            -- Random seed
  , invert :: Boolean            -- Invert output
  }
```

### Fractal Noise Type Enum

```purescript
data FractalNoiseType
  = FNTBasic           -- Basic noise
  | FNTTurbulentSmooth -- Turbulent smooth
  | FNTTurbulentSharp  -- Turbulent sharp
  | FNTDynamic         -- Dynamic (evolving)
  | FNTDynamicTwist    -- Dynamic twist
  | FNTSplineTurbulence -- Spline-based
```

### Constructors

| Function | Description |
|----------|-------------|
| `defaultFractal` | Basic, complexity 6 |
| `fractalWithComplexity ft cmplx` | Specific type and complexity |

### Queries

| Function | Description |
|----------|-------------|
| `isFractalInverted` | Check if inverted |
| `combineFractalEvolution` | Add evolution values (clamped to 0-360) |

────────────────────────────────────────────────────────────────────────────────
                                                                       // circle
────────────────────────────────────────────────────────────────────────────────

## CircleEffect

Simple circle shape with SDF rendering.

### Type Definition

```purescript
type CircleEffect =
  { center :: Point2D            -- Circle center
  , radius :: Number             -- Radius (0-10000)
  , edgeType :: CircleEdgeType   -- Filled or ring
  , edgeThickness :: Number      -- Ring thickness (0-1000)
  , feather :: { inner :: Number, outer :: Number }  -- Feathering (0-100 each)
  , invertCircle :: Boolean      -- Invert mask
  , color :: RGB                 -- Circle color
  , opacity :: Number            -- Opacity (0-100)
  , blendMode :: BlendMode       -- Compositing mode
  }
```

### Circle Edge Type Enum

```purescript
data CircleEdgeType
  = CETNone            -- Filled circle
  | CETThickness       -- Ring with thickness
```

### Constructors

| Function | Description |
|----------|-------------|
| `defaultCircle` | Center at 100,100, radius 50, white |
| `circleWithRadius center' radius' col` | Specific center, radius, color |

### Queries

| Function | Description |
|----------|-------------|
| `isCircleInverted` | Check if mask inverted |

────────────────────────────────────────────────────────────────────────────────
                                                                      // ellipse
────────────────────────────────────────────────────────────────────────────────

## EllipseEffect

Ellipse with separate width/height dimensions.

### Type Definition

```purescript
type EllipseEffect =
  { center :: Point2D            -- Ellipse center
  , size :: { width :: Number, height :: Number }  -- Dimensions (0-10000 each)
  , edgeType :: CircleEdgeType   -- Filled or ring
  , edgeThickness :: Number      -- Ring thickness (0-1000)
  , feather :: { inner :: Number, outer :: Number }  -- Feathering (0-100 each)
  , invertEllipse :: Boolean     -- Invert mask
  , color :: RGB                 -- Ellipse color
  , opacity :: Number            -- Opacity (0-100)
  , blendMode :: BlendMode       -- Compositing mode
  }
```

### Constructors

| Function | Description |
|----------|-------------|
| `defaultEllipse` | 100x60 at center, white |
| `ellipseWithSize center' w h col` | Specific center, size, color |

### Queries

| Function | Description |
|----------|-------------|
| `isEllipseInverted` | Check if mask inverted |

────────────────────────────────────────────────────────────────────────────────
                                                                         // fill
────────────────────────────────────────────────────────────────────────────────

## FillEffect

Solid color fill with mask support.

### Type Definition

```purescript
type FillEffect =
  { fillMask :: FillMaskMode     -- Which masks to fill
  , allMasks :: Boolean          -- Use all masks
  , color :: RGB                 -- Fill color
  , invertMask :: Boolean        -- Invert mask
  , horizontalFeather :: Number  -- H feather (0-100)
  , verticalFeather :: Number    -- V feather (0-100)
  , opacity :: Number            -- Opacity (0-100)
  , blendMode :: BlendMode       -- Compositing mode
  }
```

### Fill Mask Mode Enum

```purescript
data FillMaskMode
  = FMMAllMasks        -- Use all masks
  | FMMFillMask        -- Use fill mask only
  | FMMNone            -- Ignore masks
```

### Constructors

| Function | Description |
|----------|-------------|
| `defaultFill` | Red, full opacity |
| `fillWithColor col` | Specific color |

────────────────────────────────────────────────────────────────────────────────
                                                                       // stroke
────────────────────────────────────────────────────────────────────────────────

## StrokeEffect

Path stroke with brush properties.

### Type Definition

```purescript
type StrokeEffect =
  { allMasks :: Boolean          -- Use all masks
  , brushSize :: Number          -- Brush diameter (0.1-200)
  , brushHardness :: Number      -- Brush edge hardness (0-100)
  , opacity :: Number            -- Stroke opacity (0-100)
  , spacing :: Number            -- Brush spacing (1-1000 %)
  , paintStyle :: StrokePaintStyle -- Paint mode
  , color :: RGB                 -- Stroke color
  , blendMode :: BlendMode       -- Compositing mode
  , start :: Number              -- Start point (0-100 %)
  , end :: Number                -- End point (0-100 %)
  }
```

### Stroke Paint Style Enum

```purescript
data StrokePaintStyle
  = SPSOnTransparent   -- Stroke on transparent background
  | SPSOnOriginal      -- Stroke over original image
```

### Constructors

| Function | Description |
|----------|-------------|
| `defaultStroke` | 4px, 100% hardness, black |
| `strokeWithWidth width col` | Specific width and color |

────────────────────────────────────────────────────────────────────────────────
                                                                        // vegas
────────────────────────────────────────────────────────────────────────────────

## VegasEffect

Animated stroke segments along paths. Used for neon signs, animated outlines.

### Type Definition

```purescript
type VegasEffect =
  { pathMode :: VegasPathMode    -- Path source
  , segments :: Int              -- Number of segments (1-100)
  , length :: Number             -- Segment length (0-10000)
  , width :: Number              -- Line width (0-100)
  , hardness :: Number           -- Edge hardness (0-100)
  , rotation :: Number           -- Segment rotation (0-360)
  , randomPhase :: Boolean       -- Random start positions
  , blendMode :: BlendMode       -- Compositing mode
  , color :: RGB                 -- Primary color
  , startOpacity :: Number       -- Segment start opacity (0-100)
  , endOpacity :: Number         -- Segment end opacity (0-100)
  }
```

### Vegas Path Mode Enum

```purescript
data VegasPathMode
  = VPMMasks           -- Use layer masks
  | VPMLayer           -- Use layer outlines
  | VPMAllPaths        -- All paths in layer
```

### Constructors

| Function | Description |
|----------|-------------|
| `defaultVegas` | 5 segments, 50px length |
| `vegasWithSegments segs len col` | Specific segment count, length, color |

────────────────────────────────────────────────────────────────────────────────
                                                                  // lens // flare
────────────────────────────────────────────────────────────────────────────────

## LensFlareEffect

Optical lens flare simulation. Classic motion graphics effect.

### Type Definition

```purescript
type LensFlareEffect =
  { flareCenter :: Point2D       -- Light source position
  , flareBrightness :: Number    -- Brightness (0-500 %)
  , lensType :: LensType         -- Simulated lens
  , blendWithOriginal :: Number  -- Blend amount (0-100)
  }
```

### Lens Type Enum

```purescript
data LensType
  = LT50_300mm         -- 50-300mm zoom
  | LT35mm             -- 35mm prime
  | LT105mm            -- 105mm prime
```

### Constructors

| Function | Description |
|----------|-------------|
| `defaultLensFlare` | Center, 100% brightness |
| `lensFlareWithBrightness center bright` | Specific position and brightness |

────────────────────────────────────────────────────────────────────────────────
                                                              // gpu // rendering
────────────────────────────────────────────────────────────────────────────────

## GPU Shader Pattern

Generate effects are fully procedural, ideal for GPU shaders:

```glsl
vec4 generateColor = computePattern(uv, params);
outputColor = blend(inputColor, generateColor, blendMode);
```

Shape effects (Circle, Ellipse) use SDF (Signed Distance Fields) for efficient
GPU rendering with smooth edges and precise anti-aliasing.

────────────────────────────────────────────────────────────────────────────────
