# Motion Pillar: Distortion Effects

> Part of the Motion pillar documentation. See [05-motion.md](./05-motion.md) for index.

## Overview

The Distortion subsystem provides **spatial warping and displacement effects** with
full professional compositing parity. Implements 27+ distinct effects organized into categories:

- **Warp Effects**: Geometric deformations (Warp, Bezier Warp, Bulge, Twirl, Wave, Ripple, Spherize, Liquify)
- **Displacement Effects**: Map-based pixel displacement (Displacement Map, Turbulent Displace)
- **Transform Effects**: Spatial transformations (Corner Pin, Mirror, Offset, Optics Compensation, Polar Coordinates, Transform)
- **CC Effects**: 12 CC-style distortion effects

All effects use bounded primitives with Point2D for center/anchor points and
explicit clamping behavior for deterministic rendering.

## Source Files

```
Distortion/
├── Distortion.purs      # 243 lines - Leader module with re-exports
├── Types.purs           # 326 lines - Core enumerations
├── Warp.purs            # 478 lines - Warp, Bezier, Bulge, Twirl, Wave, Ripple, Spherize, Liquify
├── Displacement.purs    # 179 lines - Displacement Map, Turbulent Displace
├── Transform.purs       # 267 lines - Corner Pin, Mirror, Offset, Optics, Polar, Transform
├── CC.purs              # 377 lines - 12 CC effects
└── Queries.purs         # 373 lines - Effect names, descriptions, queries, utilities
```

**Total: 7 files, ~2,243 lines**

## Core Types

**Module**: `Hydrogen.Schema.Motion.Effects.Distortion.Types`

Core enumerations used across all distortion effects.

### Warp Style

15 professional warp presets:

```purescript
data WarpStyle
  = WSArc | WSArcLower | WSArcUpper | WSArch | WSBulge
  | WSShellLower | WSShellUpper | WSFlag | WSWave | WSFish
  | WSRise | WSFisheye | WSInflate | WSSqueeze | WSTwist
```

### Displacement Map Type

Source types for displacement maps:

```purescript
data DisplacementMapType
  = DMTLayer      -- Use another layer
  | DMTNoise      -- Procedural noise
  | DMTGradientH  -- Horizontal gradient
  | DMTGradientV  -- Vertical gradient
  | DMTRadial     -- Radial gradient
  | DMTSineH      -- Horizontal sine wave
  | DMTSineV      -- Vertical sine wave
  | DMTChecker    -- Checkerboard pattern
```

### Displacement Channel

Which channel to sample for displacement:

```purescript
data DisplacementChannel
  = DCRed | DCGreen | DCBlue | DCAlpha | DCLuminance | DCOff
```

### Edge Behavior

How effects handle image edges:

```purescript
data EdgeBehavior
  = EBOff     -- No edge handling
  | EBTiles   -- Tile/wrap edges
  | EBMirror  -- Mirror at edges
```

### Ramp Shape

```purescript
data RampShape = RSLinear | RSRadial
```

## Warp Effects

**Module**: `Hydrogen.Schema.Motion.Effects.Distortion.Warp`

8 warp-based distortion effects.

### Warp Effect

Professional raster-style warp with 15 presets:

```purescript
type WarpEffect =
  { warpStyle :: WarpStyle         -- Warp preset
  , bend :: Number                  -- -100 to 100
  , horizontalDistortion :: Number  -- -100 to 100
  , verticalDistortion :: Number    -- -100 to 100
  }
```

### Bezier Warp Effect

4-point bezier mesh deformation:

```purescript
type BezierWarpEffect =
  { topLeft :: Point2D, topRight :: Point2D
  , bottomLeft :: Point2D, bottomRight :: Point2D
  , topLeftTangent :: Point2D, topRightTangent :: Point2D
  , bottomLeftTangent :: Point2D, bottomRightTangent :: Point2D
  , quality :: Int                  -- 1-10
  }
```

### Bulge Effect

Spherical bulge distortion:

| Property | Range | Default |
|----------|-------|---------|
| horizontalRadius | 0-1000 | 100 |
| verticalRadius | 0-1000 | 100 |
| bulgeHeight | -4 to 4 | 1.0 |
| taperRadius | 0-100 | 0 |

### Twirl Effect

Rotational distortion:

| Property | Range | Default |
|----------|-------|---------|
| angle | -3600 to 3600 | 0 |
| twirlRadius | 0-2000 | 100 |
| twirlCenter | Point2D | (50, 50) |

### Wave Warp Effect

Sine wave distortion with 8 wave types:

```purescript
data WaveType
  = WTSine | WTSquare | WTTriangle | WTSawtooth
  | WTCircle | WTSemicircle | WTUncircle | WTNoise
```

| Property | Range | Default |
|----------|-------|---------|
| waveHeight | 0-500 | 25 |
| waveWidth | 1-1000 | 100 |
| direction | 0-360 | 0 |
| waveSpeed | Number | 1.0 |
| phase | 0-360 | 0 |

### Ripple Effect

Radial wave distortion:

```purescript
data RippleConversion = RCSymmetric | RCAsymmetric
```

| Property | Range | Default |
|----------|-------|---------|
| radius | 0-2000 | 100 |
| waveWidth | 1-1000 | 30 |
| waveHeight | -500 to 500 | 20 |
| ripplePhase | 0-360 | 0 |

### Spherize Effect

Wrap around sphere:

| Property | Range | Default |
|----------|-------|---------|
| radius | 0-1000 | 100 |
| amount | -100 to 100 | 100 |
| center | Point2D | (50, 50) |

### Liquify Effect

Brush-based deformation with 9 tools:

```purescript
data LiquifyTool
  = LTWarp | LTTurbulence | LTTwirl | LTTwirlCCW
  | LTPucker | LTBloat | LTShift | LTReflection | LTReconstruction
```

| Property | Range | Default |
|----------|-------|---------|
| brushSize | 1-1500 | 100 |
| brushPressure | 0-100 | 50 |
| brushRate | 0-100 | 50 |
| turbulentJitter | 0-100 | 0 |

## Displacement Effects

**Module**: `Hydrogen.Schema.Motion.Effects.Distortion.Displacement`

### Displacement Map Effect

Displace pixels using map image:

```purescript
type DisplacementMapEffect =
  { mapLayer :: Int                          -- Source layer index
  , mapType :: DisplacementMapType           -- Map source type
  , horizontalChannel :: DisplacementChannel -- Channel for X
  , verticalChannel :: DisplacementChannel   -- Channel for Y
  , maxHorizontalDisplacement :: Number      -- 0-1000 pixels
  , maxVerticalDisplacement :: Number        -- 0-1000 pixels
  , edgeBehavior :: EdgeBehavior
  , expandOutput :: Boolean
  }
```

### Turbulent Displace Effect

Fractal-based displacement:

```purescript
data TurbulentDisplaceType
  = TDTTurbulentSmooth | TDTTurbulentSharp
  | TDTBulgeSmooth | TDTBulgeSharp | TDTTwist
```

| Property | Range | Default |
|----------|-------|---------|
| amount | 0-1000 | 50 |
| size | 1-2000 | 100 |
| complexity | 1-10 | 2 |
| evolution | degrees | 0 |
| cycleRevolutions | Int | 1 |
| randomSeed | Int | 0 |

## Transform Effects

**Module**: `Hydrogen.Schema.Motion.Effects.Distortion.Transform`

6 spatial transformation effects.

### Corner Pin Effect

4-corner perspective distortion:

```purescript
type CornerPinEffect =
  { upperLeft :: Point2D, upperRight :: Point2D
  , lowerLeft :: Point2D, lowerRight :: Point2D
  }
```

### Mirror Effect

Reflection along axis:

| Property | Range | Default |
|----------|-------|---------|
| reflectionCenter | Point2D | (50, 50) |
| reflectionAngle | 0-360 | 0 |

### Offset Effect

Tile/offset image:

| Property | Range | Default |
|----------|-------|---------|
| shiftCenterTo | Point2D | (0, 0) |
| blendWithOriginal | 0-100 | 0 |

### Optics Compensation Effect

Lens distortion correction:

| Property | Range | Default |
|----------|-------|---------|
| fieldOfView | 0-180 | 45 |
| reverseLensDistortion | Boolean | false |
| fovOrientationHorizontal | Boolean | true |
| viewCenter | Point2D | (50, 50) |

### Polar Coordinates Effect

Rectangular to polar conversion:

```purescript
data PolarType = PTRectToPolar | PTPolarToRect
```

| Property | Range | Default |
|----------|-------|---------|
| typeOfConversion | PolarType | PTRectToPolar |
| interpolation | 0-100 | 100 |

### Transform Effect

Independent spatial transform:

| Property | Range | Default |
|----------|-------|---------|
| anchorPoint | Point2D | (50, 50) |
| position | Point2D | (50, 50) |
| scaleHeight | 0-1000% | 100 |
| scaleWidth | 0-1000% | 100 |
| skew | -90 to 90 | 0 |
| skewAxis | 0-360 | 0 |
| rotation | degrees | 0 |
| opacity | 0-100 | 100 |
| shuttleAngle | 0-720 | 0 |

## CC Effects

**Module**: `Hydrogen.Schema.Motion.Effects.Distortion.CC`

12 CC-style distortion effects.

### CC Bend It

Bend layer around axis:

| Property | Range | Default |
|----------|-------|---------|
| start | Point2D | (0, 50) |
| finish | Point2D | (100, 50) |
| bend | -100 to 100 | 0 |
| quality | 1-10 | 5 |

### CC Blobbylize

Organic blob distortion:

| Property | Range | Default |
|----------|-------|---------|
| softness | 0-100 | 50 |
| cutAway | 0-100 | 50 |
| blobLayer | Int | 1 |

### CC Flo Motion

Flow-based motion blur:

| Property | Range | Default |
|----------|-------|---------|
| gradientLayer | Int | 1 |
| timeStep | 0-100 | 50 |
| motionVectors | 1-32 | 8 |
| quality | 1-10 | 5 |

### CC Griddler

Grid-based distortion:

| Property | Range | Default |
|----------|-------|---------|
| horizontalScale | 0-200 | 100 |
| verticalScale | 0-200 | 100 |
| rotation | 0-360 | 0 |
| rows | 1-100 | 10 |
| columns | 1-100 | 10 |

### CC Lens

Lens distortion:

| Property | Range | Default |
|----------|-------|---------|
| center | Point2D | (50, 50) |
| size | 0-1000 | 100 |
| convergence | -100 to 100 | 0 |

### CC Page Turn

Page turn effect:

| Property | Range | Default |
|----------|-------|---------|
| foldPosition | 0-100 | 50 |
| foldRadius | 0-200 | 25 |
| foldDirection | 0-360 | 0 |
| lightDirection | 0-360 | 135 |
| lightIntensity | 0-100 | 50 |
| backPageOpacity | 0-100 | 100 |

### CC Power Pin

Advanced corner pin:

| Property | Range | Default |
|----------|-------|---------|
| topLeft, topRight | Point2D | corners |
| bottomLeft, bottomRight | Point2D | corners |
| perspective | Boolean | true |
| autoFocal | Boolean | true |
| focalLength | Number | 50 |

### CC Ripple Pulse

Expanding ripple:

| Property | Range | Default |
|----------|-------|---------|
| center | Point2D | (50, 50) |
| radius | 0-2000 | 100 |
| amplitude | 0-200 | 25 |
| pulseLevel | 0-100 | 100 |
| waveWidth | 1-500 | 50 |

### CC Slant

Perspective slant:

| Property | Range | Default |
|----------|-------|---------|
| slant | -100 to 100 | 0 |
| floor | 0-100 | 50 |
| height | 0-200 | 100 |
| direction | 0-360 | 0 |

### CC Smear

Directional smear:

| Property | Range | Default |
|----------|-------|---------|
| sourcePoint | Point2D | (25, 50) |
| destinationPoint | Point2D | (75, 50) |
| percentSource | 0-100 | 50 |
| percentDestination | 0-100 | 50 |

### CC Split

Split/duplicate effect:

```purescript
data CCSplitDirection = CSDHorizontal | CSDVertical | CSDBoth
```

| Property | Range | Default |
|----------|-------|---------|
| splitPoint | Point2D | (50, 50) |
| direction | CCSplitDirection | Horizontal |
| splitWidth | 0-500 | 0 |

### CC Tiler

Tiling effect:

| Property | Range | Default |
|----------|-------|---------|
| scale | 1-1000 | 100 |
| offset | Point2D | (0, 0) |
| rotation | 0-360 | 0 |
| blendOriginal | 0-100 | 0 |
| mirrorEdges | Boolean | false |

## Queries

**Module**: `Hydrogen.Schema.Motion.Effects.Distortion.Queries`

Utility functions for distortion effects.

### Effect Names

Each effect has a name function:

```purescript
warpEffectName :: WarpEffect -> String           -- "Warp"
bulgeEffectName :: BulgeEffect -> String         -- "Bulge"
twirlEffectName :: TwirlEffect -> String         -- "Twirl"
ccBendItEffectName :: CCBendItEffect -> String   -- "CC Bend It"
-- ... (27 total)
```

### Effect Descriptions

Human-readable descriptions:

```purescript
describeWarp :: WarpEffect -> String
-- "Warp(WSArc, bend: 50.0)"

describeBulge :: BulgeEffect -> String
-- "Bulge(radius: 100x100, height: 1.0)"

describeTwirl :: TwirlEffect -> String
-- "Twirl(angle: 90°, radius: 100)"
```

### Query Predicates

```purescript
isWarpBent :: WarpEffect -> Boolean
-- True if bend != 0

isDisplacementActive :: DisplacementMapEffect -> Boolean
-- True if displacement > 0

hasBulgeHeight :: BulgeEffect -> Boolean
-- True if |height| > 0.1

isTwirlSignificant :: TwirlEffect -> Boolean
-- True if |angle| >= 10

isWaveWarpAnimated :: WaveWarpEffect -> Boolean
-- True if waveSpeed > 0

isTurbulentDisplaceComplex :: TurbulentDisplaceEffect -> Boolean
-- True if complexity >= 5
```

### Utility Functions

```purescript
scaleWarpBend :: Number -> WarpEffect -> WarpEffect
-- Scale bend by factor

combineBulgeHeights :: BulgeEffect -> BulgeEffect -> Number
-- Average heights

totalDisplacementMagnitude :: DisplacementMapEffect -> Number
-- H + V displacement

waveWarpIntensity :: WaveWarpEffect -> Number
-- height * (100 / width)

twirlRevolutions :: TwirlEffect -> Number
-- angle / 360

classifyWarpIntensity :: WarpEffect -> String
-- "none" | "subtle" | "moderate" | "strong" | "extreme"

hasTransformChange :: TransformEffect -> Boolean
-- True if any property differs from default

hasWarpBothDistortions :: WarpEffect -> Boolean
-- True if both H and V distortion active
```

