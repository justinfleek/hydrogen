━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     // 05 // motion // spatial
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Motion: Spatial Keyframes & Paths

Motion path keyframes with bezier handles in 2D/3D space.

────────────────────────────────────────────────────────────────────────────────
                                              // motion // graphics // parity
────────────────────────────────────────────────────────────────────────────────

In professional motion graphics software, position keyframes have TWO sets of bezier handles:

1. **Spatial Handles**: Control the SHAPE of the motion path
   - Visible in the composition viewport as path tangents
   - Define the curve the object travels through space

2. **Temporal Handles**: Control the SPEED along the path
   - Visible in the Graph Editor (speed graph / value graph)
   - Define how fast the object moves between keyframes

```
                   +-------------------------------------+
                   |         SPATIAL DOMAIN              |
                   |   (Composition Viewport)            |
                   |                                     |
      inSpatial -->*----------------*<-- outSpatial      |
                  KF1              KF2                   |
                   |   motion path curve                 |
                   +-------------------------------------+

                   +-------------------------------------+
                   |         TEMPORAL DOMAIN             |
                   |   (Graph Editor)                    |
                   |                                     |
                   |         ,-------,                   |
     inTemporal -->*--------'       '----*<-- outTemporal|
                  KF1                   KF2              |
                   |   speed curve (ease in/out)         |
                   +-------------------------------------+
```

────────────────────────────────────────────────────────────────────────────────
                                                                       // atoms
────────────────────────────────────────────────────────────────────────────────

## SpatialKeyframe/Types.purs (171 lines)

Keyframe flags, interpolation modes, and dimension configuration.

**KeyframeFlags:**
```purescript
{ roving :: Boolean            -- Roving keyframe (auto-time adjustment)
, lockToTime :: Boolean        -- Locked to specific time
, continuousBezier :: Boolean  -- Continuous bezier tangents
, autoBezier :: Boolean        -- Auto-calculated tangents
}
```

**SpatialInterpolation:**
- `SILinear` — Straight line between keyframes
- `SIBezier` — Curved path with spatial handles
- `SIAuto` — Auto-calculated smooth path

**TemporalInterpolation:**
- `TILinear` — Constant speed
- `TIBezier` — Curved speed with temporal handles
- `TIHold` — No interpolation (instant jump)
- `TIAuto` — Auto-calculated smooth easing

**DimensionMode:**
- `DMUnified` — Single property with spatial handles (X/Y/Z together)
- `DMSeparated` — X, Y, Z as separate properties

## SpatialKeyframe/Handle.purs (174 lines)

Bezier handles for spatial and temporal control.

**SpatialHandle2D:**
```purescript
newtype SpatialHandle2D = SpatialHandle2D { dx :: Number, dy :: Number }
```
- Tangent direction and magnitude relative to keyframe position
- `spatialHandle2D :: Number -> Number -> SpatialHandle2D` — Create from dx, dy
- `spatialHandle2DZero :: SpatialHandle2D` — Zero-length (linear)
- `unwrapSpatialHandle2D :: SpatialHandle2D -> { dx :: Number, dy :: Number }` — Extract values

**SpatialHandle3D:**
```purescript
newtype SpatialHandle3D = SpatialHandle3D { dx :: Number, dy :: Number, dz :: Number }
```
- 3D tangent for motion paths in 3D space
- `spatialHandle3D :: Number -> Number -> Number -> SpatialHandle3D` — Create from dx, dy, dz
- `spatialHandle3DZero :: SpatialHandle3D` — Zero-length (linear)
- `unwrapSpatialHandle3D :: SpatialHandle3D -> { dx :: Number, dy :: Number, dz :: Number }` — Extract values

**TemporalHandle:**
```purescript
newtype TemporalHandle = TemporalHandle { influence :: Number, speed :: Number }
```
- `influence` — How far handle extends (0-100%, clamped)
- `speed` — Velocity at keyframe (units/frame)
- `temporalHandle :: Number -> Number -> TemporalHandle` — Create from influence, speed
- `unwrapTemporalHandle :: TemporalHandle -> { influence :: Number, speed :: Number }` — Extract values
- Presets: `temporalHandleLinear`, `temporalHandleEaseIn`, `temporalHandleEaseOut`, `temporalHandleEaseInOut`, `temporalHandleHold`

────────────────────────────────────────────────────────────────────────────────
                                                                   // molecules
────────────────────────────────────────────────────────────────────────────────

## SpatialKeyframe/Keyframe.purs (303 lines)

Complete 2D/3D keyframes with all handles.

**SpatialKeyframe2D:**
```purescript
{ frame :: Frames
, position :: { x :: Number, y :: Number }
, spatialIn :: SpatialHandle2D
, spatialOut :: SpatialHandle2D
, temporalIn :: TemporalHandle
, temporalOut :: TemporalHandle
, spatialInterp :: SpatialInterpolation
, temporalInterp :: TemporalInterpolation
, flags :: KeyframeFlags
}
```

**2D Constructors:**
```purescript
spatialKeyframe2D :: Frames -> Number -> Number -> SpatialKeyframe2D
-- Basic keyframe (auto interpolation)

spatialKeyframe2DLinear :: Frames -> Number -> Number -> SpatialKeyframe2D
-- Linear interpolation (no curves)

spatialKeyframe2DWithHandles 
  :: Frames -> Number -> Number 
  -> SpatialHandle2D -> SpatialHandle2D 
  -> TemporalHandle -> TemporalHandle 
  -> SpatialKeyframe2D
-- Explicit handles (bezier mode)
```

**SpatialKeyframe3D:**
Same structure with 3D position `{ x, y, z }` and `SpatialHandle3D`.

**3D Constructors:**
```purescript
spatialKeyframe3D :: Frames -> Number -> Number -> Number -> SpatialKeyframe3D
-- Basic 3D keyframe (auto interpolation)

spatialKeyframe3DLinear :: Frames -> Number -> Number -> Number -> SpatialKeyframe3D
-- Linear 3D interpolation (no curves)

spatialKeyframe3DWithHandles 
  :: Frames -> Number -> Number -> Number
  -> SpatialHandle3D -> SpatialHandle3D 
  -> TemporalHandle -> TemporalHandle 
  -> SpatialKeyframe3D
-- Explicit 3D handles (bezier mode)
```

**Accessors:**
- `keyframePosition2D`, `keyframePosition3D`, `keyframeFrame`
- `keyframeSpatialIn2D`, `keyframeSpatialOut2D`, `keyframeSpatialIn3D`, `keyframeSpatialOut3D`
- `keyframeTemporalIn`, `keyframeTemporalOut`, `keyframeFlags`

**Operations:**
- `setPosition2D`, `setPosition3D` — Update position
- `setSpatialHandles2D`, `setSpatialHandles3D` — Set spatial tangents
- `setTemporalHandles` — Set temporal easing
- `convertToRoving`, `convertToLinear`, `convertToBezier`, `convertToHold`, `convertToAuto`

## SpatialKeyframe/Bezier.purs (297 lines)

Cubic bezier mathematics and arc length calculation.

**Cubic Bezier Formula:**
```
B(t) = (1-t)³P₀ + 3(1-t)²tP₁ + 3(1-t)t²P₂ + t³P₃
```
Where P0=start, P1=start+outTangent, P2=end+inTangent, P3=end.

**Core Functions:**
- `cubicBezier` — Evaluate bezier at parameter t (single component)
- `cubicBezierDerivative` — Velocity at parameter t
- `evalBezier2D`, `evalBezier3D` — Evaluate full keyframe pair

**Temporal Easing:**
- `applyTemporalEasing` — Convert linear time to eased parameter
- `solveForT` — Newton-Raphson solver for temporal bezier

**Arc Length:**
- `bezierArcLength2D`, `bezierArcLength3D` — 5-point Gaussian quadrature
- `bezierSpeed2D`, `bezierSpeed3D` — Instantaneous speed (|B'(t)|)

## SpatialKeyframe/Path.purs (457 lines)

Motion paths and speed graphs.

**MotionPath2D/3D:**
```purescript
{ keyframes :: Array SpatialKeyframe2D
, closed :: Boolean           -- Does path loop?
, dimensionMode :: DimensionMode
}
```

**Construction:**
- `motionPath2D`, `motionPath3D` — Empty paths
- `motionPath2DFromKeyframes`, `motionPath3DFromKeyframes` — From keyframe array

**Evaluation:**
- `evaluateMotionPath2D`, `evaluateMotionPath3D` — Get position at frame
  - Finds surrounding keyframes
  - Calculates normalized time
  - Applies temporal easing
  - Evaluates cubic bezier

**Arc Length:**
- `motionPathLength2D`, `motionPathLength3D` — Total path length via Gaussian quadrature

**SpeedGraph:**
```purescript
{ samples :: Array { frame :: Number, speed :: Number }
, minSpeed :: Number
, maxSpeed :: Number
, averageSpeed :: Number
}
```

**Speed Graph Functions:**
- `speedGraph` — Create from samples
- `speedAt` — Interpolated speed at frame
- `averageSpeed`, `maxSpeed`, `minSpeed` — Statistics

────────────────────────────────────────────────────────────────────────────────
                                                                // source files
────────────────────────────────────────────────────────────────────────────────

```
src/Hydrogen/Schema/Motion/
├── SpatialKeyframe.purs (leader, 166 lines)
└── SpatialKeyframe/
    ├── Types.purs (171 lines)
    ├── Handle.purs (174 lines)
    ├── Keyframe.purs (303 lines)
    ├── Bezier.purs (297 lines)
    └── Path.purs (457 lines)
```

~1,568 lines total.

────────────────────────────────────────────────────────────────────────────────
                                                           // path // motion
────────────────────────────────────────────────────────────────────────────────

Cinema-grade path animation like professional motion graphics, 3D modeling, and vector editors.

## PathMotion/Types.purs (172 lines)

**PathSource:**
- `CatmullRomSource CatmullRomSpline` — Smooth interpolating spline
- `BSplineSource BSpline` — Approximating spline
- `PointArraySource (Array Point2D)` — Linear interpolation

**OrientMode:**
- `NoOrient` — Keep original rotation
- `OrientToPath` — Rotate to face movement direction
- `OrientToPathFlipped` — 180° from movement direction
- `OrientPerpendicular` — Perpendicular to path
- `OrientCustomOffset Degrees` — Path rotation + custom offset

**MotionSample:**
```purescript
{ position :: Point2D
, rotation :: Degrees
, tangent :: Vector2D
, progress :: Number    -- 0-1 normalized
, arcLength :: Number   -- Distance along path
, speed :: Number       -- Current velocity
, bank :: Degrees       -- Banking angle for turns
}
```

**MotionPath:**
```purescript
{ source :: PathSource
, durationFrames :: Number
, easing :: Easing
, orientMode :: OrientMode
, bankAngle :: Degrees       -- Max banking for turns
, bankSmoothing :: Number    -- 0-1 smoothing amount
, loop :: Boolean
, pingPong :: Boolean
, startOffset :: Number      -- 0-1 path start
, endOffset :: Number        -- 0-1 path end
, startFrame :: Number
}
```

## PathMotion/Core.purs (199 lines)

**Construction:**
- `motionPath` — Full configuration (source, duration, easing)
- `motionPathSimple` — Linear easing
- `motionPathWithBank` — Auto-orient with banking

**Configuration:**
- `setDuration`, `setEasing`, `setOrientMode`, `setAutoOrient`
- `setBankAngle`, `setLoop`, `setPingPong`, `setOffset`

**Accessors:**
- `pathSource`, `duration`, `easing`, `orientMode`, `isLooping`, `isPingPong`

**Presets:**
- `defaultEasing` — ease in-out

## PathMotion/Evaluation.purs (325 lines)

**Position Evaluation:**
- `positionAtFrame` — Position at frame number
- `positionAtTime` — Position at normalized time (0-1)
- `positionAtProgress` — Position with easing applied

**Tangent/Rotation:**
- `tangentAtFrame`, `tangentAtProgress` — Direction vector
- `rotationAtFrame` — Rotation based on orient mode

**Full Sampling:**
- `sampleAtFrame`, `sampleAtProgress` — Complete MotionSample

**Path Length:**
- `pathLength` — Total arc length
- `progressToArcLength`, `arcLengthToProgress` — Conversions

**Frame Utilities:**
- `frameToProgress`, `progressToFrame` — Frame/progress conversion
- `isActiveAtFrame` — Animation active check

**Batch Sampling:**
- `sampleFrameRange` — Sample every frame in range
- `samplePoints` — N evenly-spaced positions

## PathMotion/Internal.purs (278 lines)

Internal helpers:
- `evaluatePathPosition`, `evaluatePathTangent`, `evaluatePathLength`
- `interpolatePointArray`, `interpolatePointArrayTangent`, `pointArrayLength`
- `vectorToAngle`, `addDegrees`, `calculateBank`
- Array/math utilities

────────────────────────────────────────────────────────────────────────────────
                                                       // path // operations
────────────────────────────────────────────────────────────────────────────────

Vector/3D-style path manipulation.

## PathOperations/Insertion.purs (151 lines)

**Point Insertion:**
- `insertPoint` — Insert at parameter t (0-1)
- `insertPointAtLength` — Insert at arc length

**Subdivision:**
- `subdivide` — N iterations of midpoint insertion
- `subdivideOnce` — Single subdivision pass
- `subdivideAdaptive` — More points in high-curvature areas

## PathOperations/Transform.purs (307 lines)

**Spacing:**
- `equalizeSpacing` — Create n evenly-spaced points (3D resample tool)
- `resample` — Alias for equalizeSpacing
- `resampleByLength` — Resample with target segment length

**Smoothing:**
- `smooth` — Chaikin smoothing with iterations
- `chaikinSmooth` — Single Chaikin pass
- `smoothLaplacian` — Laplacian smoothing
- `laplacianPass` — Single Laplacian pass
- `simplify` — Remove points by distance threshold
- `simplifyRDP` — Ramer-Douglas-Peucker simplification

**Direction:**
- `reversePath`, `flipPath` — Reverse path direction

**Offset:**
- `offsetPath` — Parallel path at distance (positive = left)
- `outlinePath` — Create outline (both sides)

## PathOperations/Analysis.purs (273 lines)

**Analysis:**
- `pathSegmentLengths` — Length of each segment
- `pathCurvatures` — Curvature at each point
- `findSharpCorners` — Indices of high-curvature points
- `totalCurvature` — Sum of absolute curvatures

**Utilities:**
- `closePathLoop` — Connect last to first
- `openPath` — Remove closing point
- `splitAtPoint` — Split at parameter t
- `joinPaths` — Concatenate paths

**Filtering:**
- `filterByDistance` — Remove points too close together
- `filterByAngle` — Remove low-curvature points
- `removeConsecutiveDuplicates`

**Display:**
- `showPath`, `showPathCompact` — String representations

## PathOperations/Internal.purs (257 lines)

Internal helpers:
- `epsilon`, `clamp01`, `floorInt`, `mod`
- `buildArray`, `buildIntArray`, `buildIntRange`
- `pointToLineDistance`, `computeAngle`, `computeCurvatures`
- `sumSegmentLengths`, `pointAtArcLength`, `computeNormalAt`

────────────────────────────────────────────────────────────────────────────────
                                                                // source files
────────────────────────────────────────────────────────────────────────────────

```
src/Hydrogen/Schema/Motion/
├── SpatialKeyframe.purs (leader, 166 lines)
├── SpatialKeyframe/
│   ├── Types.purs (171 lines)
│   ├── Handle.purs (174 lines)
│   ├── Keyframe.purs (303 lines)
│   ├── Bezier.purs (297 lines)
│   └── Path.purs (457 lines)
├── PathMotion.purs (leader, 74 lines)
├── PathMotion/
│   ├── Types.purs (172 lines)
│   ├── Core.purs (199 lines)
│   ├── Evaluation.purs (325 lines)
│   └── Internal.purs (278 lines)
├── PathOperations.purs (leader, 65 lines)
└── PathOperations/
    ├── Insertion.purs (151 lines)
    ├── Transform.purs (307 lines)
    ├── Analysis.purs (273 lines)
    └── Internal.purs (257 lines)
```

~3,669 lines total.

────────────────────────────────────────────────────────────────────────────────

