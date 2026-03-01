━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                              // 05 // motion
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Motion Pillar

The complete vocabulary for time-based animation and motion graphics.
169 source files defining temporal primitives, keyframe systems, effects,
layer architecture, 3D cameras, text animation, and AI-driven motion.

────────────────────────────────────────────────────────────────────────────────
                                                                    // overview
────────────────────────────────────────────────────────────────────────────────

## Purpose

Motion provides bounded, deterministic primitives for:
- Temporal measurement (timecode, frame rates, time ranges)
- Keyframe-based animation with easing curves
- Spatial interpolation along paths
- Layer composition and references
- Visual effects (blur, color correction, distortion, simulation)
- Shape generation and modification
- 3D camera and lighting
- Text animation
- AI/diffusion-based motion synthesis

────────────────────────────────────────────────────────────────────────────────
                                                         // core // temporal
────────────────────────────────────────────────────────────────────────────────

## Atoms

### Timecode.purs (446 lines)

SMPTE timecode representation for professional video/motion graphics.

**Types:**
- `Timecode` — Stores total frame count with frame rate and drop-frame flag
- `TimecodeComponents` — Display components { hours, minutes, seconds, frames }

**Constructors:**
- `timecode` — Create from hour, minute, second, frame components
- `fromFrames` — Create from raw frame count
- `fromSeconds` — Create from seconds
- `zero` — Zero timecode (00:00:00:00)

**Operations:**
- `addFrames`, `subtractFrames` — Frame arithmetic
- `addTimecode`, `subtractTimecode` — Timecode arithmetic
- `parse` — Parse SMPTE string ("HH:MM:SS:FF" or "HH:MM:SS;FF" for drop-frame)
- `format`, `formatCompact` — Format for display
- `toFrames`, `toSeconds`, `toComponents` — Conversion

**Queries:**
- `isDropFrame` — Uses drop-frame format?
- `frameRate` — Get frame rate
- `totalFrames` — Get total frames
- `isValid`, `normalize` — Validation

**Drop-Frame:**
NTSC runs at 29.97fps. Drop-frame skips frames 0,1 at minute start (except 10th minute)
to sync timecode with wall-clock time. Uses semicolon separator: `01:02:03;04`

### TimeRange.purs (372 lines)

Time range (in/out points) for motion graphics.

**Types:**
- `TimeRange` — { inPoint :: Frames, outPoint :: Frames }

**Invariants:** inPoint <= outPoint, both >= 0 (enforced by constructors)

**Constructors:**
- `timeRange` — From in/out points (auto-ordered)
- `fromDuration` — From start point and duration
- `empty` — Zero-length at frame 0
- `infinite` — Large bounded range (avoids actual infinity)

**Accessors:**
- `inPoint`, `outPoint`, `duration`

**Predicates:**
- `contains` — Frame within range?
- `containsRange` — Range fully contains another?
- `overlaps` — Two ranges overlap?
- `isEmpty` — Zero duration?

**Operations:**
- `setInPoint`, `setOutPoint` — Modify points (with clamping)
- `shift` — Move entire range by offset
- `scale` — Scale duration from in point
- `trim` — Clamp to bounds
- `expand` — Add to both ends
- `intersect` — Get overlap (Maybe)
- `union` — Smallest containing range

## Molecules

### Timeline.purs (663 lines)

Frame-based animation timing and layer coordination.

**Types:**
- `Timeline` — { frameRate, totalFrames, layers, looping, pingPong }
- `TimelineLayer` — { name, startFrame, endFrame, inPoint, outPoint, timeRemap, enabled }
- `FrameRate` — Number (fps)

**Frame Rate Presets:**
- `fps24` (film), `fps25` (PAL), `fps30` (NTSC)
- `fps48` (HFR film), `fps60` (games), `fps120` (high refresh)
- `customFps` — Custom rate (clamped 1-240)

**Construction:**
- `timeline` — Create with fps and frame count
- `emptyTimeline` — Default empty
- `fromDuration` — From fps and seconds

**Layer Management:**
- `addLayer`, `removeLayer`, `getLayer`
- `setLayerTiming`, `setLayerTimeRemap`
- `getLayerByIndex`, `layerCount`, `hasLayer`

**Frame Calculation:**
- `globalToLocal` — Global frame to layer-local frame (accounts for offset + time remap)
- `localToGlobal` — Inverse transformation
- `layerTimeAtFrame`, `frameAtLayerTime` — Named access
- `isLayerActiveAtFrame` — Layer visible at frame?

**Time Conversion:**
- `frameToSeconds`, `secondsToFrame`
- `progressAtFrame`, `frameAtProgress` — 0-1 progress

**Playback Modes:**
- `clampFrame` — Clamp to timeline bounds
- `wrapFrame` — Loop playback
- `pingPongFrame` — Forward-backward playback

**Batch Operations:**
- `activeLayersAtFrame` — All active layers
- `layerTimesAtFrame` — Local times for all active layers
- `evaluateFrame` — Complete render state { frame, time, progress, layers }

**Advanced:**
- `reverseTimeline` — Reverse playback direction
- `clearTimeRemap`, `isLayerRemapped`
- `isFramePlayable`, `seekToLayerFrame`

### TimeRemap/ (6 files, ~1,059 lines)

Variable speed, time remapping, and ramps for animation.
Leader module re-exports from submodules.

**TimeRemap/Types.purs (99 lines):**

- `RemapMode` — Enumeration:
  - `LinearRemap` — Constant speed factor
  - `CurveRemap Easing` — Speed follows easing curve
  - `KeyframeRemap` — Speed defined by keyframes
  - `FreezeRemap Number` — Frozen at specific time
  - `PingPongRemap` — Forward then backward
  - `LoopRemap Number` — Loop every n frames

- `SpeedKeyframe` — { frame, speed, easing }
  - speed = 1.0 normal, 0.5 half speed, 2.0 double, 0.0 freeze

- `TimeRemap` — { mode, speedFactor, startSpeed, endSpeed, originalDuration, keyframes }

**TimeRemap/Construction.purs (174 lines):**

- `identity` — No change (1x speed)
- `uniformSpeed` — Constant speed change (0.5 = slow-mo, 2.0 = fast-forward)
- `reverse` — Backward playback (-1x)
- `freezeAt` — Hold specific frame
- `timeStretch` — Uniform speed to achieve target duration
- `speedRamp` — Custom easing from start to end speed
- `speedRampIn` — Slow start (ease-in)
- `speedRampOut` — Slow end (ease-out)
- `speedRampInOut` — Slow start and end
- `fromSpeedKeyframes` — Build from keyframe array
- `addSpeedKeyframe`, `removeSpeedKeyframe`

**TimeRemap/Evaluation.purs (257 lines):**

- `apply` — Remap input frame to output frame
- `applyInverse` — Inverse: find input from output (Newton-Raphson for curves)
- `applyToProgress` — Remap normalized 0-1 progress
- `speedAt` — Speed at specific frame
- `derivativeAt` — Rate of time change (alias for speedAt)
- `remappedDuration`, `originalDuration`, `setOriginalDuration`

**TimeRemap/Composition.purs (260 lines):**

Composition:
- `compose` — Apply first, then second (multiply speeds)
- `chain` — Sequential (first plays, then second)
- `blend` — Weighted blend (0.0 = first, 1.0 = second)

Presets:
- `slowMotion` — 50% speed
- `fastForward` — 2x speed
- `pingPong` — Forward then reverse
- `loop` — Loop every n frames
- `hold` — Freeze at end
- `bounce` — Ease in-out with brief hold

Analysis:
- `averageSpeed`, `minSpeed`, `maxSpeed`
- `isConstantSpeed`
- `sampleRemap`, `sampleSpeed` — Sample at n evenly-spaced points

**TimeRemap/Utilities.purs (186 lines):**

- `defaultSpeed` — 1.0 (normal)
- `isValidRemap` — Duration positive, speeds reasonable
- `normalizeRemap` — Scale to average speed 1.0
- `speedKeyframe` — Create keyframe with linear easing
- `combineRemaps` — Average multiple remaps
- `speedMagnitude` — 2D speed vector magnitude
- `hasSpeedChange` — Not identity?

**TimeRemap/Internal.purs (243 lines):**

Internal helpers (not re-exported):
- Numeric: `clamp01`, `clampNumber`, `floorNum`, `floorInt`, `mod`, `epsilon`, `infinity`
- Array: `buildArray`, `buildIntArray`
- Integration: `integrateSpeed`, `integrateKeyframes` (trapezoidal approximation)
- Keyframes: `speedAtKeyframes`, `findSurroundingKeyframes`, `sortKeyframes`



────────────────────────────────────────────────────────────────────────────────
                                                         // easing // interpolation
────────────────────────────────────────────────────────────────────────────────

## Atoms

### Easing.purs (446 lines)

Easing curves for animation interpolation. Maps normalized time (0-1) to
normalized value (0-1).

**Types:**
- `CubicBezier` — { x1, y1, x2, y2 } control points (start 0,0 and end 1,1 implicit)
- `Easing` — Sum type:
  - `Linear` — No acceleration
  - `Bezier CubicBezier String` — Cubic bezier with name
  - `Steps Int Boolean` — Step function (count, jump-start?)

**Constructors:**
- `linear` — No acceleration
- `cubicBezier` — Custom cubic bezier (x1, y1, x2, y2)
- `steps` — Step function

**Standard Presets (CSS-compatible):**
- `ease`, `easeIn`, `easeOut`, `easeInOut`

**Easing Families (30 presets):**
- Sine: `easeInSine`, `easeOutSine`, `easeInOutSine`
- Quad: `easeInQuad`, `easeOutQuad`, `easeInOutQuad`
- Cubic: `easeInCubic`, `easeOutCubic`, `easeInOutCubic`
- Quart: `easeInQuart`, `easeOutQuart`, `easeInOutQuart`
- Quint: `easeInQuint`, `easeOutQuint`, `easeInOutQuint`
- Expo: `easeInExpo`, `easeOutExpo`, `easeInOutExpo`
- Circ: `easeInCirc`, `easeOutCirc`, `easeInOutCirc`
- Back: `easeInBack`, `easeOutBack`, `easeInOutBack` (overshoot)
- Elastic: `easeInElastic`, `easeOutElastic`, `easeInOutElastic` (approximation)
- Bounce: `easeInBounce`, `easeOutBounce`, `easeInOutBounce` (approximation)

**Evaluation:**
- `evaluate` — Evaluate easing at time t (0-1), returns eased value
- `evaluateBezier` — Evaluate cubic bezier (Newton-Raphson for x→t mapping)

**Accessors:**
- `toControlPoints`, `p1x`, `p1y`, `p2x`, `p2y`
- `toLegacyCssString` — Export for legacy CSS systems (NOT for Hydrogen rendering)
- `name` — Get easing name

### Interpolation.purs (575 lines)

Keyframe interpolation types for motion graphics.

**FullInterpolationType (33 variants):**

Complete enumeration matching `Lattice.Animation.FullInterpolationType`:

Base types:
- `FITLinear` — Constant speed
- `FITBezier` — Custom bezier (uses handle data)
- `FITHold` — Hold value until next keyframe

Easing presets (30 variants):
- Sine, Quad, Cubic, Quart, Quint, Expo, Circ, Back, Elastic, Bounce
- Each with In, Out, InOut variants

**Predicates:**
- `isBaseInterpolation` — Is linear/bezier/hold?
- `isEasingInterpolation` — Is easing preset?

**Serialization:**
- `fullInterpolationTypeToString`, `fullInterpolationTypeFromString`
- `allFullInterpolationTypes` — Complete enumeration array

## Molecules

### SpatialTangent

Direction and magnitude of motion path tangents (for position keyframes).

- `SpatialTangent` — { x, y, z :: Number }
- `mkSpatialTangent`, `defaultSpatialTangent`, `spatialTangentZero`

### BezierHandle

Control point for bezier curve interpolation.

- `BezierHandle` — { frame, value, enabled }
  - `frame`: Relative offset (negative for in-handle)
  - `value`: Influence amount
  - `enabled`: Is active?
- `mkBezierHandle`, `defaultInHandle` (-5.0), `defaultOutHandle` (+5.0)

### ControlMode

How in/out handles relate:

- `CMSymmetric` — Handles mirror exactly
- `CMSmooth` — Colinear but different lengths
- `CMCorner` — Independent handles

### ExtendedKeyframeData

Complete interpolation settings for a keyframe:

```purescript
ExtendedKeyframeData
  { interpolation :: FullInterpolationType
  , inHandle :: BezierHandle
  , outHandle :: BezierHandle
  , controlMode :: ControlMode
  , spatialInTangent :: Maybe SpatialTangent
  , spatialOutTangent :: Maybe SpatialTangent
  }
```

- `defaultExtendedKeyframeData` — Linear with smooth control mode



────────────────────────────────────────────────────────────────────────────────
                                                         // keyframe // animation
────────────────────────────────────────────────────────────────────────────────

## Atoms

### Keyframe.purs (396 lines)

Keyframe data for motion graphics animation.

**Types:**
- `KeyframeId` — Unique identifier (deterministically generated)
- `InterpolationType` — { Linear, Bezier, Hold, Auto }
- `Tangent` — { x, y } control point offset for bezier
- `KeyframeValue` — Value sum type:
  - `NumberValue Number`
  - `Vec2Value { x, y }`
  - `Vec3Value { x, y, z }`
  - `ColorValue { r, g, b, a }`
  - `AngleValue Number` (degrees)
  - `PercentValue Number` (0-100)

- `Keyframe` — Complete keyframe:
  - `{ id, frame, value, interpolation, inTangent, outTangent }`

**Constructors:**
- `keyframe` — Basic keyframe with auto-generated ID
- `keyframeWithId` — With explicit ID
- `tangent`, `tangentFlat`, `tangentAuto`

**Builders:**
- `withInterpolation`, `withInTangent`, `withOutTangent`
- `withBezierTangents` — Set both tangents + bezier mode
- `withHold`, `withLinear`, `withAuto`

**Accessors:**
- `frame`, `value`, `interpolationType`, `inTangent`, `outTangent`, `keyframeId`

**Predicates:**
- `isBezier`, `isHold`, `isLinear`, `isAuto`

**Operations:**
- `setFrame`, `setValue`, `shiftFrame`
- `lerpValue` — Linear interpolation between values
- `addValues`, `scaleValue`

### KeyframeAnimation/Types.purs (229 lines)

Core enumerations for keyframe animations.

**AnimationProperty (20 variants):**
- Transform: `PropTranslateX/Y/Z`, `PropRotate/X/Y/Z`, `PropScale/X/Y`, `PropSkewX/Y`
- Visual: `PropOpacity`, `PropBlur`, `PropBrightness`, `PropSaturate`
- Color: `PropBackgroundColor`, `PropBorderColor`, `PropShadowColor`
- Custom: `PropCustom String`

**AnimationDirection:**
- `DirectionNormal`, `DirectionReverse`
- `DirectionAlternate`, `DirectionAlternateReverse`

**AnimationFillMode:**
- `FillNone`, `FillForwards`, `FillBackwards`, `FillBoth`

**AnimationPlayState:**
- `PlayStatePlaying`, `PlayStatePaused`

## Molecules

### KeyframeAnimation/Keyframe.purs

`PropertyKeyframe` — Keyframe with percent offset (0-100) and value.

Helpers:
- `propertyKeyframe`, `opacityKeyframe`, `translateXKeyframe`
- `translateYKeyframe`, `rotateKeyframe`, `scaleKeyframe`, `colorKeyframe`

### KeyframeAnimation/Core.purs (238 lines)

`KeyframeAnimation` — Complete animation specification:

```purescript
{ id, name, property, keyframes, duration, delay,
  iterations, direction, fillMode, playState, easing }
```

**Constructors:**
- `keyframeAnimation` — Full control (name, property, keyframes, duration)
- `simpleAnimation` — Two-keyframe (start → end)

**Builders:**
- `withDuration`, `withDelay`, `withIterations`, `withInfinite`
- `withDirection`, `withFillMode`, `withEasing`, `withProperty`
- `addKeyframe`

**Accessors:**
- `duration`, `delay`, `iterations`, `direction`, `fillMode`
- `keyframes`, `property`

**Predicates:**
- `isInfinite`, `isPaused`, `hasKeyframes`

## Compounds (Presets)

### KeyframeAnimation/Presets/Attention.purs

Attention-grabbing animations:
- `bounce`, `flash`, `pulse`, `rubberBand`, `shake`
- `swing`, `tada`, `wobble`, `jello`, `heartBeat`

### KeyframeAnimation/Presets/Enter.purs

Entry animations:
- `fadeIn`, `fadeInUp/Down/Left/Right`
- `slideInUp/Down/Left/Right`
- `zoomIn`, `bounceIn`

### KeyframeAnimation/Presets/Exit.purs

Exit animations:
- `fadeOut`, `fadeOutUp/Down/Left/Right`
- `slideOutUp/Down/Left/Right`
- `zoomOut`, `bounceOut`

### KeyframeAnimation/Presets/Loading.purs

Loading state animations:
- `spin`, `spinReverse`, `pingPong`, `breathe`



────────────────────────────────────────────────────────────────────────────────
                                                         // spatial // keyframes
────────────────────────────────────────────────────────────────────────────────

## Atoms



## Molecules



────────────────────────────────────────────────────────────────────────────────
                                                         // path // motion
────────────────────────────────────────────────────────────────────────────────

## Atoms



## Molecules



────────────────────────────────────────────────────────────────────────────────
                                                         // layer // architecture
────────────────────────────────────────────────────────────────────────────────

## Atoms



## Molecules



## Compounds



────────────────────────────────────────────────────────────────────────────────
                                                         // transform
────────────────────────────────────────────────────────────────────────────────

## Atoms



## Molecules



────────────────────────────────────────────────────────────────────────────────
                                                         // effects // core
────────────────────────────────────────────────────────────────────────────────

## Atoms



## Molecules



────────────────────────────────────────────────────────────────────────────────
                                                         // effects // blur
────────────────────────────────────────────────────────────────────────────────

## Atoms



## Molecules



────────────────────────────────────────────────────────────────────────────────
                                                         // effects // color
────────────────────────────────────────────────────────────────────────────────

## Atoms



## Molecules



────────────────────────────────────────────────────────────────────────────────
                                                         // effects // distortion
────────────────────────────────────────────────────────────────────────────────

## Atoms



## Molecules



────────────────────────────────────────────────────────────────────────────────
                                                         // effects // perspective
────────────────────────────────────────────────────────────────────────────────

## Atoms



## Molecules



────────────────────────────────────────────────────────────────────────────────
                                                         // effects // simulation
────────────────────────────────────────────────────────────────────────────────

## Atoms



## Molecules



────────────────────────────────────────────────────────────────────────────────
                                                         // effects // other
────────────────────────────────────────────────────────────────────────────────

## Matte



## Keying



## Glow



## Stylize



## Time Effects



## Noise



## Mesh



────────────────────────────────────────────────────────────────────────────────
                                                         // shapes
────────────────────────────────────────────────────────────────────────────────

## Atoms



## Molecules



## Modifiers



────────────────────────────────────────────────────────────────────────────────
                                                         // camera // 3d
────────────────────────────────────────────────────────────────────────────────

## Atoms



## Molecules



────────────────────────────────────────────────────────────────────────────────
                                                         // light // 3d
────────────────────────────────────────────────────────────────────────────────

## Atoms



## Molecules



────────────────────────────────────────────────────────────────────────────────
                                                         // text // animation
────────────────────────────────────────────────────────────────────────────────

## Atoms



## Molecules



────────────────────────────────────────────────────────────────────────────────
                                                         // diffusion // ai
────────────────────────────────────────────────────────────────────────────────

## Atoms



## Molecules



────────────────────────────────────────────────────────────────────────────────
                                                         // professional
────────────────────────────────────────────────────────────────────────────────

## PropertyValue Types



────────────────────────────────────────────────────────────────────────────────
                                                         // composition
────────────────────────────────────────────────────────────────────────────────

## Atoms



## Molecules



────────────────────────────────────────────────────────────────────────────────
                                                         // orchestration
────────────────────────────────────────────────────────────────────────────────

## Atoms



## Molecules



────────────────────────────────────────────────────────────────────────────────
                                                         // source // files
────────────────────────────────────────────────────────────────────────────────

```
src/Hydrogen/Schema/Motion/
├── Professional/
├── AnimatedTransform/
├── Camera3D/
├── Diffusion/
├── Effects/
├── KeyframeAnimation/
├── Layer/
├── LayerReference/
├── PathMotion/
├── PathOperations/
├── Shapes/
├── SpatialKeyframe/
├── TextAnimator/
├── TimeRemap/
└── [root files]
```

169 files, ~45,116 lines total.

────────────────────────────────────────────────────────────────────────────────
