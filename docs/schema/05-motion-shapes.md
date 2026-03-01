━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                   // 05 // motion // shapes
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Shapes Subsystem

Vector graphics primitives for motion graphics shape layers.

────────────────────────────────────────────────────────────────────────────────
                                                                     // overview
────────────────────────────────────────────────────────────────────────────────

## Purpose

Shape layers are the foundation of vector graphics in motion graphics. This 
subsystem provides:

- **14 core enumerations** — Fill rules, line caps/joins, path operators, content types
- **5 shape generators** — Rectangle, Ellipse, Polygon, Star, Bezier Path
- **12 shape operators** — Trim, Merge, Offset, Pucker/Bloat, ZigZag, Twist, Wiggle, etc.
- **7 modifier files** — Fill, Stroke, Gradient, Taper, Wave, Advanced, Utilities

All values are bounded to ensure deterministic behavior at billion-agent scale.
Same shape configuration = same rendered output, guaranteed.

## File Map

```
src/Hydrogen/Schema/Motion/
├── Shapes.purs                    # Core enums (652 lines)
├── Shapes/
│   ├── Generators.purs            # Shape generators (355 lines)
│   ├── Operators.purs             # Shape operators (625 lines)
│   └── Modifiers/
│       ├── Modifiers.purs         # Leader module (137 lines)
│       ├── Fill.purs              # Solid fill (55 lines)
│       ├── Stroke.purs            # Stroke + dash (144 lines)
│       ├── Gradient.purs          # Gradient fill/stroke (151 lines)
│       ├── Taper.purs             # Stroke taper (134 lines)
│       ├── Wave.purs              # Stroke wave (158 lines)
│       ├── Advanced.purs          # Advanced stroke (153 lines)
│       └── Utilities.purs         # Utilities (341 lines)
```

**Total: 11 files, ~2,905 lines**

────────────────────────────────────────────────────────────────────────────────
                                                                // core // enums
────────────────────────────────────────────────────────────────────────────────

## Shapes.purs (652 lines)

Core shape enumerations and type tags. All enums have serialization functions.

### FillRule

Determines inside/outside for path filling:

```purescript
data FillRule = FRNonzero | FREvenodd

fillRuleToString   :: FillRule -> String      -- "nonzero" | "evenodd"
fillRuleFromString :: String -> Maybe FillRule
```

### LineCap

Stroke endpoint style:

```purescript
data LineCap = LCButt | LCRound | LCSquare

lineCapToString   :: LineCap -> String        -- "butt" | "round" | "square"
lineCapFromString :: String -> Maybe LineCap
```

### LineJoin

Stroke corner style:

```purescript
data LineJoin = LJMiter | LJRound | LJBevel

lineJoinToString   :: LineJoin -> String      -- "miter" | "round" | "bevel"
lineJoinFromString :: String -> Maybe LineJoin
```

### TrimMode

How Trim Paths operator processes multiple paths:

```purescript
data TrimMode = TMSimultaneously | TMIndividually
```

### MergeMode (6 variants)

Boolean operations for Merge Paths:

```purescript
data MergeMode
  = MMAdd          -- Union
  | MMSubtract     -- Subtract from first
  | MMIntersect    -- Intersection
  | MMExclude      -- XOR
  | MMMinusFront   -- Subtract front from back
  | MMMinusBack    -- Subtract back from front
```

### OffsetJoin

Corner style for Offset Paths:

```purescript
data OffsetJoin = OJMiter | OJRound | OJBevel
```

### WigglePointType / ZigZagPointType

Point style for path distortion operators:

```purescript
data WigglePointType = WPTCorner | WPTSmooth
data ZigZagPointType = ZZPTCorner | ZZPTSmooth
```

### RepeaterComposite

Stacking order for Repeater copies:

```purescript
data RepeaterComposite = RCAbove | RCBelow
```

### ShapeContentType (24 variants)

Complete enumeration of shape content items:

**Generators (5):**
`SCTRectangle` | `SCTEllipse` | `SCTPolygon` | `SCTStar` | `SCTPath`

**Modifiers (4):**
`SCTFill` | `SCTStroke` | `SCTGradientFill` | `SCTGradientStroke`

**Operators (12):**
`SCTTrimPaths` | `SCTMergePaths` | `SCTOffsetPaths` | `SCTPuckerBloat` |
`SCTWigglePaths` | `SCTZigZag` | `SCTTwist` | `SCTRoundedCorners` |
`SCTRepeater` | `SCTTransform` | `SCTSimplifyPath` | `SCTSmoothPath`

**Other (3):**
`SCTGroup` | `SCTExtrude` | `SCTTrace`

**Classification predicates:**
```purescript
isShapeContentTypeGenerator :: ShapeContentType -> Boolean  -- Rectangle, Ellipse, etc.
isShapeContentTypeModifier  :: ShapeContentType -> Boolean  -- Fill, Stroke, Gradient
isShapeContentTypeOperator  :: ShapeContentType -> Boolean  -- Trim, Merge, Offset, etc.
```

### GradientType

```purescript
data GradientType = GTLinear | GTRadial
```

### ShapeQuality

Rendering quality for shapes:

```purescript
data ShapeQuality = SQDraft | SQNormal | SQHigh
```

### ExtrudeCapType

Cap style for 3D extrusion:

```purescript
data ExtrudeCapType = ECTFlat | ECTRound | ECTBevel
```

### TraceMode

Image trace modes:

```purescript
data TraceMode = TMBlackAndWhite | TMGrayscale | TMColor
```

### PathDirection

Winding direction:

```purescript
data PathDirection = PDClockwise | PDCounterClockwise

pathDirectionToInt :: PathDirection -> Int   -- 1 or -1 (for winding calculations)
```

────────────────────────────────────────────────────────────────────────────────
                                                                  // generators
────────────────────────────────────────────────────────────────────────────────

## Shapes/Generators.purs (355 lines)

Shape generator property records. Each creates a path from bounded parameters.

### CornerRadius

Corner radius for rectangles (uniform or per-corner):

```purescript
data CornerRadius
  = UniformRadius PositiveNumber
  | PerCornerRadius
      { topLeft     :: PositiveNumber
      , topRight    :: PositiveNumber
      , bottomRight :: PositiveNumber
      , bottomLeft  :: PositiveNumber
      }

cornerRadius        :: Number -> Number -> Number -> Number -> CornerRadius
cornerRadiusUniform :: Number -> CornerRadius
cornerRadiusNone    :: CornerRadius          -- Sharp corners
unwrapCornerRadius  :: CornerRadius -> Number
```

### RectangleProps

```purescript
type RectangleProps =
  { size         :: { width :: PositiveNumber, height :: PositiveNumber }
  , position     :: Point2D           -- Center position
  , roundness    :: Percent           -- 0-100%
  , cornerRadius :: CornerRadius
  , direction    :: PathDirection
  }

rectangleProps   :: Number -> Number -> Point2D -> Number -> CornerRadius -> PathDirection -> RectangleProps
defaultRectangle :: RectangleProps   -- 100x100 at origin
```

### EllipseProps

```purescript
type EllipseProps =
  { size      :: { width :: PositiveNumber, height :: PositiveNumber }
  , position  :: Point2D              -- Center position
  , direction :: PathDirection
  }

ellipseProps   :: Number -> Number -> Point2D -> PathDirection -> EllipseProps
defaultEllipse :: EllipseProps       -- 100x100 circle at origin
```

### PolygonProps

Regular polygon with n sides:

```purescript
type PolygonProps =
  { points         :: PositiveInt     -- Number of sides (3+, clamped)
  , position       :: Point2D         -- Center
  , outerRadius    :: PositiveNumber  -- Vertex distance from center
  , outerRoundness :: Percent         -- Vertex roundness
  , direction      :: PathDirection
  }

polygonProps   :: Int -> Point2D -> Number -> Number -> PathDirection -> PolygonProps
defaultPolygon :: PolygonProps       -- Hexagon (6 sides)
```

### StarProps

Star with inner and outer radii:

```purescript
type StarProps =
  { points         :: PositiveInt     -- Star points (3+)
  , position       :: Point2D
  , outerRadius    :: PositiveNumber  -- Outer point distance
  , innerRadius    :: PositiveNumber  -- Inner point distance
  , outerRoundness :: Percent         -- Outer point roundness
  , innerRoundness :: Percent         -- Inner point roundness
  , rotation       :: Number          -- Initial rotation (degrees, -36000 to 36000)
  , direction      :: PathDirection
  }

starProps   :: Int -> Point2D -> Number -> Number -> Number -> Number -> Number -> PathDirection -> StarProps
defaultStar :: StarProps             -- 5-pointed star
```

### PathProps

Bezier path (array of path commands):

```purescript
type PathProps =
  { path      :: Path                 -- Bezier path data
  , closed    :: Boolean              -- Closed path?
  , direction :: PathDirection
  }

pathProps   :: Path -> Boolean -> PathDirection -> PathProps
defaultPath :: PathProps             -- Empty path
```

────────────────────────────────────────────────────────────────────────────────
                                                                   // operators
────────────────────────────────────────────────────────────────────────────────

## Shapes/Operators.purs (625 lines)

Shape operator property records. Each transforms paths in specific ways.

### Bounded Value Types

Operators use bounded newtypes for all numeric values:

```purescript
newtype Percent        = Percent Number        -- -1000 to 1000
newtype Degrees        = Degrees Number        -- -36000 to 36000
newtype PositiveNumber = PositiveNumber Number -- 0 to 10000
newtype PositiveInt    = PositiveInt Int       -- 1 to 10000

percent        :: Number -> Percent
degrees        :: Number -> Degrees
positiveNumber :: Number -> PositiveNumber
positiveInt    :: Int -> PositiveInt

unwrapPercent        :: Percent -> Number
unwrapDegrees        :: Degrees -> Number
unwrapPositiveNumber :: PositiveNumber -> Number
unwrapPositiveInt    :: PositiveInt -> Int
```

### TrimPathsProps

Reveals portion of a path (stroke-draw animation):

```purescript
type TrimPathsProps =
  { start  :: Percent      -- Start of visible path (0-100%)
  , end    :: Percent      -- End of visible path (0-100%)
  , offset :: Degrees      -- Rotation offset
  , mode   :: TrimMode     -- Simultaneously or Individually
  }

trimPathsProps   :: Number -> Number -> Number -> TrimMode -> TrimPathsProps
defaultTrimPaths :: TrimPathsProps   -- 0% to 100% (full path)
```

### OffsetPathsProps

Expands or contracts paths:

```purescript
type OffsetPathsProps =
  { amount     :: Number       -- Offset pixels (-10000 to 10000)
  , lineJoin   :: OffsetJoin   -- Corner treatment
  , miterLimit :: Number       -- Miter limit (1-100)
  }

offsetPathsProps   :: Number -> OffsetJoin -> Number -> OffsetPathsProps
defaultOffsetPaths :: OffsetPathsProps  -- No offset
```

### RoundedCornersProps

```purescript
type RoundedCornersProps =
  { radius :: PositiveNumber   -- Corner radius in pixels
  }

roundedCornersProps   :: Number -> RoundedCornersProps
defaultRoundedCorners :: RoundedCornersProps  -- 0 radius
```

### PuckerBloatProps

Distorts paths toward or away from center:
- Negative = Pucker (inward)
- Positive = Bloat (outward)

```purescript
type PuckerBloatProps =
  { amount :: Percent          -- -100% to 100%
  }

puckerBloatProps   :: Number -> PuckerBloatProps
defaultPuckerBloat :: PuckerBloatProps  -- No distortion
```

### ZigZagProps

Adds zigzag distortion to path segments:

```purescript
type ZigZagProps =
  { size            :: PositiveNumber   -- Zigzag amplitude
  , ridgesPerSegment :: PositiveNumber  -- Number of ridges
  , pointType       :: ZigZagPointType  -- Corner or Smooth
  }

zigZagProps   :: Number -> Number -> ZigZagPointType -> ZigZagProps
defaultZigZag :: ZigZagProps  -- 10px size, 5 ridges, corner
```

### TwistProps

Rotates points based on distance from center:

```purescript
type TwistProps =
  { angle  :: Degrees   -- Twist angle
  , center :: Point2D   -- Twist center
  }

twistProps   :: Number -> Point2D -> TwistProps
defaultTwist :: TwistProps  -- No twist
```

### WigglePathsProps

Adds random wiggles to path points:

```purescript
type WigglePathsProps =
  { size          :: PositiveNumber     -- Wiggle amplitude
  , detail        :: PositiveNumber     -- Points per segment
  , pointType     :: WigglePointType    -- Corner or Smooth
  , correlation   :: Percent            -- Adjacent wiggle correlation (0-100%)
  , temporalPhase :: Degrees            -- Animation phase offset
  , spatialPhase  :: Degrees            -- Spatial phase offset
  , randomSeed    :: Int                -- Deterministic random seed (0-999999)
  }

wigglePathsProps   :: Number -> Number -> WigglePointType -> Number -> Number -> Number -> Int -> WigglePathsProps
defaultWigglePaths :: WigglePathsProps
```

### RepeaterTransform / RepeaterProps

Duplicates shapes with cumulative transforms:

```purescript
type RepeaterTransform =
  { position      :: Point2D            -- Position offset per copy
  , anchorPoint   :: Point2D            -- Anchor offset
  , scale         :: { x :: Number, y :: Number }  -- Scale per copy (%)
  , rotation      :: Degrees            -- Rotation per copy
  , startOpacity  :: Percent            -- First copy opacity
  , endOpacity    :: Percent            -- Last copy opacity
  }

type RepeaterProps =
  { copies    :: PositiveInt            -- Number of copies
  , offset    :: Number                 -- Stacking offset (-100 to 100)
  , composite :: RepeaterComposite      -- Above or Below
  , transform :: RepeaterTransform
  }

repeaterProps            :: Int -> Number -> RepeaterComposite -> RepeaterTransform -> RepeaterProps
defaultRepeater          :: RepeaterProps   -- 3 copies, no transform
defaultRepeaterTransform :: RepeaterTransform
```

### MergePathsProps

Combines paths with boolean operations:

```purescript
type MergePathsProps = { mode :: MergeMode }

mergePathsProps   :: MergeMode -> MergePathsProps
defaultMergePaths :: MergePathsProps  -- Add (union)
```

### ShapeTransformProps

Transform applied to shapes within a group:

```purescript
type ShapeTransformProps =
  { position    :: Point2D
  , anchorPoint :: Point2D
  , scale       :: { x :: Number, y :: Number }  -- Scale (%)
  , rotation    :: Degrees
  , skew        :: Degrees
  , skewAxis    :: Degrees
  , opacity     :: Percent
  }

shapeTransformProps   :: ... -> ShapeTransformProps
defaultShapeTransform :: ShapeTransformProps  -- Identity transform
```

### SimplifyPathProps / SmoothPathProps

Path simplification and smoothing:

```purescript
type SimplifyPathProps = { tolerance :: PositiveNumber }
type SmoothPathProps   = { smoothness :: Percent }

simplifyPathProps   :: Number -> SimplifyPathProps
smoothPathProps     :: Number -> SmoothPathProps
defaultSimplifyPath :: SimplifyPathProps  -- 2.5 tolerance
defaultSmoothPath   :: SmoothPathProps    -- 100% smoothness
```

────────────────────────────────────────────────────────────────────────────────
                                                                   // modifiers
────────────────────────────────────────────────────────────────────────────────

## Shapes/Modifiers.purs (137 lines)

Leader module that re-exports all modifier submodules.

## Shapes/Modifiers/Fill.purs (55 lines)

Solid color fill:

```purescript
type FillProps =
  { color    :: RGB           -- Fill color
  , opacity  :: Percent       -- Fill opacity (0-100%)
  , fillRule :: FillRule      -- Nonzero or Evenodd
  }

fillProps   :: RGB -> Number -> FillRule -> FillProps
defaultFill :: FillProps     -- White, 100% opacity, nonzero rule
```

## Shapes/Modifiers/Stroke.purs (144 lines)

Stroke with dash pattern support:

```purescript
type StrokeDash =
  { dash :: PositiveNumber    -- Dash length
  , gap  :: PositiveNumber    -- Gap length
  }

type DashPattern =
  { dashes :: Array StrokeDash   -- Dash/gap pairs
  , offset :: Number             -- Dash offset (animatable, -10000 to 10000)
  }

strokeDash  :: Number -> Number -> StrokeDash
dashPattern :: Array StrokeDash -> Number -> DashPattern
solidDash   :: DashPattern           -- No dashes
dottedDash  :: Number -> DashPattern -- Dots with size
dashedDash  :: Number -> Number -> DashPattern

type StrokeProps =
  { color       :: RGB
  , opacity     :: Percent
  , width       :: PositiveNumber    -- Stroke width
  , lineCap     :: LineCap
  , lineJoin    :: LineJoin
  , miterLimit  :: Number            -- 1-100
  , dashPattern :: DashPattern
  }

strokeProps   :: RGB -> Number -> Number -> LineCap -> LineJoin -> Number -> DashPattern -> StrokeProps
defaultStroke :: StrokeProps   -- Black, 1px, solid
```

## Shapes/Modifiers/Gradient.purs (151 lines)

Gradient fill and stroke:

```purescript
type GradientFillProps =
  { gradientType :: GradientType     -- Linear or Radial
  , startPoint   :: Point2D
  , endPoint     :: Point2D
  , opacity      :: Percent
  , colorStops   :: Array ColorStop
  , fillRule     :: FillRule
  }

type GradientStrokeProps =
  { gradientType :: GradientType
  , startPoint   :: Point2D
  , endPoint     :: Point2D
  , opacity      :: Percent
  , width        :: PositiveNumber
  , colorStops   :: Array ColorStop
  , lineCap      :: LineCap
  , lineJoin     :: LineJoin
  , miterLimit   :: Number
  , dashPattern  :: DashPattern
  }

gradientFillProps     :: GradientType -> Point2D -> Point2D -> Number -> Array ColorStop -> FillRule -> GradientFillProps
gradientStrokeProps   :: ... -> GradientStrokeProps
defaultGradientFill   :: GradientFillProps    -- Black to white linear
defaultGradientStroke :: GradientStrokeProps  -- Black to white, 1px
```

## Shapes/Modifiers/Taper.purs (134 lines)

Stroke width taper (professional motion graphics, 2020+ feature):

```purescript
type StrokeTaper =
  { enabled     :: Boolean
  , startLength :: Percent       -- Start taper length (0-100%)
  , endLength   :: Percent       -- End taper length (0-100%)
  , startWidth  :: Percent       -- Width at start (0-100%)
  , endWidth    :: Percent       -- Width at end (0-100%)
  , startEase   :: Percent       -- Start ease curve (0-100%)
  , endEase     :: Percent       -- End ease curve (0-100%)
  }

strokeTaper     :: Boolean -> Number -> Number -> Number -> Number -> Number -> Number -> StrokeTaper
noTaper         :: StrokeTaper          -- Disabled, constant width
defaultTaper    :: StrokeTaper          -- Enabled, symmetric 10% fade
taperFromStart  :: Number -> StrokeTaper -- Point at start
taperToEnd      :: Number -> StrokeTaper -- Point at end
taperBothEnds   :: Number -> Number -> StrokeTaper
```

## Shapes/Modifiers/Wave.purs (158 lines)

Stroke wave deformation (professional motion graphics, 2020+ feature):

```purescript
data WaveType = WTSine | WTSquare | WTTriangle | WTSawtooth

type StrokeWave =
  { enabled   :: Boolean
  , amount    :: PositiveNumber     -- Wave amplitude (0-500)
  , frequency :: PositiveNumber     -- Number of waves (0-50)
  , phase     :: Number             -- Phase offset (0-360 degrees)
  , waveType  :: WaveType
  }

strokeWave    :: Boolean -> Number -> Number -> Number -> WaveType -> StrokeWave
noWave        :: StrokeWave         -- Disabled
defaultWave   :: StrokeWave         -- Sine, 10 amplitude, 5 frequency
sineWave      :: Number -> Number -> StrokeWave
squareWave    :: Number -> Number -> StrokeWave
triangleWave  :: Number -> Number -> StrokeWave
sawtoothWave  :: Number -> Number -> StrokeWave
```

## Shapes/Modifiers/Advanced.purs (153 lines)

Advanced stroke combining taper and wave:

```purescript
type AdvancedStrokeProps =
  { color       :: RGB
  , opacity     :: Percent
  , width       :: PositiveNumber
  , lineCap     :: LineCap
  , lineJoin    :: LineJoin
  , miterLimit  :: Number
  , dashPattern :: DashPattern
  , taper       :: StrokeTaper        -- CC 2020+ taper
  , wave        :: StrokeWave         -- CC 2020+ wave
  }

advancedStrokeProps       :: ... -> AdvancedStrokeProps
defaultAdvancedStroke     :: AdvancedStrokeProps  -- No taper, no wave
strokeWithTaper           :: RGB -> Number -> StrokeTaper -> AdvancedStrokeProps
strokeWithWave            :: RGB -> Number -> StrokeWave -> AdvancedStrokeProps
strokeWithTaperAndWave    :: RGB -> Number -> StrokeTaper -> StrokeWave -> AdvancedStrokeProps

hasTaper            :: AdvancedStrokeProps -> Boolean
hasWave             :: AdvancedStrokeProps -> Boolean
hasAdvancedFeatures :: AdvancedStrokeProps -> Boolean
```

## Shapes/Modifiers/Utilities.purs (341 lines)

Serialization, comparison, and utility functions:

### Serialization

```purescript
dashPatternToString :: DashPattern -> String   -- "solid" or "dashed"
describeTaper       :: StrokeTaper -> String   -- "Taper(...)" or "no-taper"
describeWave        :: StrokeWave -> String    -- "Wave(...)" or "no-wave"
```

### Utilities

```purescript
totalTaperLength       :: StrokeTaper -> Number         -- startLength + endLength
effectiveWaveFrequency :: StrokeWave -> Number -> Number -- Frequency scaled by path length
scaleTaper             :: Number -> StrokeTaper -> StrokeTaper
scaleWave              :: Number -> StrokeWave -> StrokeWave
combineTapers          :: StrokeTaper -> StrokeTaper -> StrokeTaper  -- Average
combineWaves           :: StrokeWave -> StrokeWave -> StrokeWave     -- Average
allWaveTypes           :: Array WaveType
```

### Comparisons

```purescript
compareStrokeWidth  :: StrokeProps -> StrokeProps -> Ordering
isStrokeThin        :: StrokeProps -> Boolean     -- < 2px
isStrokeThick       :: StrokeProps -> Boolean     -- >= 10px
isTaperSymmetric    :: StrokeTaper -> Boolean
taperStartsFromZero :: StrokeTaper -> Boolean
taperEndsAtZero     :: StrokeTaper -> Boolean
isWaveHighFrequency :: StrokeWave -> Boolean      -- > 10
isWaveLowAmplitude  :: StrokeWave -> Boolean      -- < 5
minStrokeByWidth    :: StrokeProps -> StrokeProps -> StrokeProps
maxStrokeByWidth    :: StrokeProps -> StrokeProps -> StrokeProps
taperEquals         :: StrokeTaper -> StrokeTaper -> Boolean
waveEquals          :: StrokeWave -> StrokeWave -> Boolean
isDashPatternSolid  :: DashPattern -> Boolean
hasDashes           :: DashPattern -> Boolean
negateWavePhase     :: StrokeWave -> StrokeWave   -- Flip 180 degrees
invertTaper         :: StrokeTaper -> StrokeTaper -- Swap start/end
strokeCoverage      :: StrokeProps -> Number      -- 100% for solid, ~50% for dashed
taperDiffersBy      :: StrokeTaper -> StrokeTaper -> Number -> Boolean  -- Differs by threshold
taperNotEquals      :: StrokeTaper -> StrokeTaper -> Boolean
waveNotEquals       :: StrokeWave -> StrokeWave -> Boolean
minTaperLength      :: StrokeTaper -> Number      -- Min of startLength/endLength
maxTaperLength      :: StrokeTaper -> Number      -- Max of startLength/endLength
minWaveParam        :: StrokeWave -> Number       -- Min of amount/frequency
maxWaveParam        :: StrokeWave -> Number       -- Max of amount/frequency
```

### Semigroup Combinable

```purescript
newtype CombinableStrokeWidth = CombinableStrokeWidth PositiveNumber

instance Semigroup CombinableStrokeWidth  -- Averages widths

combinableWidth     :: Number -> CombinableStrokeWidth
unwrapCombinableWidth :: CombinableStrokeWidth -> Number
```

────────────────────────────────────────────────────────────────────────────────
                                                              // cross-references
────────────────────────────────────────────────────────────────────────────────

## Dependencies

**From Schema:**
- `Hydrogen.Schema.Bounded` — `clampNumber` for bounded values
- `Hydrogen.Schema.Color.RGB` — `RGB`, `rgb` for colors
- `Hydrogen.Schema.Color.Gradient` — `ColorStop`, `colorStop` for gradients
- `Hydrogen.Schema.Dimension.Point2D` — `Point2D`, `origin` for positions
- `Hydrogen.Schema.Geometry.Path.Types` — `Path` for bezier paths

**Within Motion:**
- Layer system uses `ShapeContent` for shape layers
- Effects can reference shape paths
- Animated properties can keyframe any bounded value

## Usage Example

Creating a 5-pointed star with gradient fill and tapered stroke:

```purescript
import Hydrogen.Schema.Motion.Shapes
import Hydrogen.Schema.Motion.Shapes.Generators
import Hydrogen.Schema.Motion.Shapes.Modifiers

star = defaultStar { points = positiveInt 5, outerRadius = positiveNumber 100.0 }

gradientFill = defaultGradientFill 
  { colorStops = 
      [ colorStop (rgb 255 0 0) 0.0
      , colorStop (rgb 255 255 0) 1.0
      ]
  }

taperedStroke = strokeWithTaper (rgb 0 0 0) 3.0 (taperBothEnds 20.0 20.0)
```

────────────────────────────────────────────────────────────────────────────────
