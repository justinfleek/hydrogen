━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                      // 05 // motion // easing
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Motion: Easing & Interpolation

Timing curves and interpolation types for animation.

────────────────────────────────────────────────────────────────────────────────
                                                                       // atoms
────────────────────────────────────────────────────────────────────────────────

## Easing.purs (446 lines)

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

## Interpolation.purs (575 lines)

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

────────────────────────────────────────────────────────────────────────────────
                                                                   // molecules
────────────────────────────────────────────────────────────────────────────────

## SpatialTangent

Direction and magnitude of motion path tangents (for position keyframes).

- `SpatialTangent` — { x, y, z :: Number }
- `mkSpatialTangent`, `defaultSpatialTangent`, `spatialTangentZero`

## BezierHandle

Control point for bezier curve interpolation.

- `BezierHandle` — { frame, value, enabled }
  - `frame`: Relative offset (negative for in-handle)
  - `value`: Influence amount
  - `enabled`: Is active?
- `mkBezierHandle`, `defaultInHandle` (-5.0), `defaultOutHandle` (+5.0)

## ControlMode

How in/out handles relate:

- `CMSymmetric` — Handles mirror exactly
- `CMSmooth` — Colinear but different lengths
- `CMCorner` — Independent handles

## ExtendedKeyframeData

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
                                                                // source files
────────────────────────────────────────────────────────────────────────────────

```
src/Hydrogen/Schema/Motion/
├── Easing.purs
└── Interpolation.purs
```

~1,021 lines total.

────────────────────────────────────────────────────────────────────────────────
