━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                   // 05 // motion // expression
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Animatable Properties and Evaluation

Property system for motion graphics layers with expression support.

────────────────────────────────────────────────────────────────────────────────
                                                                     // overview
────────────────────────────────────────────────────────────────────────────────

## Purpose

Motion graphics properties need two capabilities:

1. **Metadata** — What type of value, can it be animated, does it have an expression?
2. **Evaluation** — Given a frame number and keyframes, what's the interpolated value?

This module provides both:

**Property.purs** — Property definitions:
- PropertyValueType (number, position, color, etc.)
- ExpressionType (wiggle, noise, time, audio-reactive, etc.)
- AnimatableProperty with keyframe references and expression support
- PropertyPath for addressing nested properties

**Evaluate.purs** — Keyframe evaluation engine:
- Find bracketing keyframes for any frame
- Calculate interpolation progress
- Apply easing from tangent handles
- Return interpolated values

**Why this matters for autonomous agents:**

When agents generate motion graphics, they need to:
1. Define properties with correct types (position is spatial, opacity is numeric)
2. Apply expressions for procedural animation (wiggle, audio-reactive)
3. Evaluate keyframes at arbitrary frames for preview/scrubbing

The type system ensures valid property configurations. The evaluation engine
provides deterministic interpolation — same keyframes, same frame, same result.

## File Map

```
src/Hydrogen/Schema/Motion/
├── Property.purs    # 454 lines — Property definitions and expressions
└── Evaluate.purs    # 241 lines — Keyframe evaluation engine
```

**Total: 2 files, ~695 lines**

────────────────────────────────────────────────────────────────────────────────
                                                                   // properties
────────────────────────────────────────────────────────────────────────────────

## PropertyValueType (5 variants)

What kind of value a property holds — determines valid operations and UI.

| Constructor | String ID | Interpolation | Description |
|-------------|-----------|---------------|-------------|
| `PVTNumber` | `"number"` | Scalar lerp | Single numeric value (opacity, rotation) |
| `PVTPosition` | `"position"` | 2D/3D spatial | Position with motion path |
| `PVTColor` | `"color"` | Per-channel | RGBA color |
| `PVTEnum` | `"enum"` | None (stepped) | Enumerated value (blend mode) |
| `PVTVector3` | `"vector3"` | Per-component | 3D vector without motion path |

```purescript
data PropertyValueType
  = PVTNumber
  | PVTPosition
  | PVTColor
  | PVTEnum
  | PVTVector3
```

**Name Collision Warning:**

Two different `PropertyValueType` types exist in the codebase:

| Module | Variants | Purpose |
|--------|----------|---------|
| `Motion.Property.PropertyValueType` | 5 | Simplified type system for Hydrogen animation |
| `Motion.Professional.PropertyValue.Types.PropertyValueType` | 13 | Full motion graphics API parity |

Use explicit module qualification when both are in scope:

```purescript
import Hydrogen.Schema.Motion.Property as Property
import Hydrogen.Schema.Motion.Professional.PropertyValue.Types as MotionProp

-- Hydrogen simplified type
hydrogenType :: Property.PropertyValueType
hydrogenType = Property.PVTNumber

-- Full motion graphics parity type  
motionType :: MotionProp.PropertyValueType
motionType = MotionProp.OneD
```

### Serialization

```purescript
propertyValueTypeToString   :: PropertyValueType -> String
propertyValueTypeFromString :: String -> Maybe PropertyValueType
```

### Predicates

```purescript
isPropertyValueNumeric :: PropertyValueType -> Boolean
  -- True for PVTNumber only

isPropertyValueVector :: PropertyValueType -> Boolean
  -- True for PVTPosition, PVTVector3
```

## AnimatablePropertyId

Unique identifier for a property (NonEmptyString semantics).

```purescript
newtype AnimatablePropertyId = AnimatablePropertyId String

mkAnimatablePropertyId     :: String -> Maybe AnimatablePropertyId
  -- Returns Nothing for empty string

unwrapAnimatablePropertyId :: AnimatablePropertyId -> String
```

## AnimatableProperty

Complete property definition with value, keyframes, and expression.

```purescript
newtype AnimatableProperty = AnimatableProperty
  { id           :: String
  , name         :: String
  , propertyType :: PropertyValueType
  , value        :: String             -- JSON-encoded current value
  , animated     :: Boolean            -- Has keyframes
  , keyframeIds  :: Array String       -- References to keyframe objects
  , group        :: Maybe String       -- Group name for UI
  , expression   :: Maybe PropertyExpression
  , simplified   :: Boolean            -- Show simplified UI
  , locked       :: Boolean            -- Prevent editing
  , elided       :: Boolean            -- Hidden in UI
  }
```

### Constructor

```purescript
defaultAnimatableProperty 
  :: String              -- id
  -> String              -- name
  -> PropertyValueType   -- type
  -> AnimatableProperty
```

### Predicates

```purescript
propertyAnimated      :: AnimatableProperty -> Boolean
  -- True if animated flag is set

propertyHasKeyframes  :: AnimatableProperty -> Boolean
  -- True if animated AND has keyframe IDs

propertyHasExpression :: AnimatableProperty -> Boolean
  -- True if expression exists AND is enabled
```

## PropertyGroup

Organizational grouping for properties in UI.

```purescript
newtype PropertyGroup = PropertyGroup
  { id         :: String
  , name       :: String
  , properties :: Array AnimatableProperty
  , collapsed  :: Boolean
  }
```

### Accessors

```purescript
propertyGroupName       :: PropertyGroup -> String
propertyGroupProperties :: PropertyGroup -> Array AnimatableProperty
```

### Common Groups

| Group | Properties |
|-------|------------|
| Transform | Position, Scale, Rotation, Anchor, Opacity |
| Geometry | Path, Mask, UV |
| Appearance | Fill, Stroke, Effects |
| Audio | Volume, Pan, Tone |

## PropertyPath

Path to a property in a hierarchical property tree.

```purescript
newtype PropertyPath = PropertyPath (Array String)

-- Example: "Transform/Position/X" → PropertyPath ["Transform", "Position", "X"]
```

### Serialization

```purescript
propertyPathToString   :: PropertyPath -> String
  -- Joins segments with "/"

propertyPathFromString :: String -> PropertyPath
  -- Splits on "/"
```

### Common Paths

| Path | Property |
|------|----------|
| `"Transform/Position"` | Layer position |
| `"Transform/Scale"` | Layer scale |
| `"Transform/Rotation"` | Layer rotation |
| `"Transform/Opacity"` | Layer opacity |
| `"Contents/Fill/Color"` | Shape fill color |
| `"Effects/Blur/Radius"` | Blur effect radius |

────────────────────────────────────────────────────────────────────────────────
                                                                  // expressions
────────────────────────────────────────────────────────────────────────────────

## ExpressionType (24 variants)

Expressions allow procedural animation — values computed from time, other 
properties, or external data rather than keyframed.

### Time-Based Expressions

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `ETWiggle` | `"wiggle"` | Random oscillation with frequency/amplitude |
| `ETTime` | `"time"` | Current time value |
| `ETLoop` | `"loop"` | Loop animation segment |
| `ETLinear` | `"linear"` | Linear interpolation over time |
| `ETHold` | `"hold"` | Hold current value |
| `ETSmooth` | `"smooth"` | Smooth interpolation |

### Property References

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `ETThisProperty` | `"thisProperty"` | Reference to this property's keyframed value |
| `ETComp` | `"comp"` | Reference to composition |
| `ETLayer` | `"layer"` | Reference to another layer |
| `ETMarker` | `"marker"` | Reference to composition marker |

### Math Operations

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `ETAdd` | `"add"` | Addition |
| `ETSubtract` | `"subtract"` | Subtraction |
| `ETMultiply` | `"multiply"` | Multiplication |
| `ETDivide` | `"divide"` | Division |
| `ETModulo` | `"modulo"` | Modulo (remainder) |

### Vector Operations

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `ETLength` | `"length"` | Vector magnitude |
| `ETNormalize` | `"normalize"` | Unit vector |
| `ETDistance` | `"distance"` | Distance between points |
| `ETClamp` | `"clamp"` | Clamp value to range |
| `ETLerp` | `"lerp"` | Linear interpolation |

### Noise Functions

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `ETNoise` | `"noise"` | Perlin noise |
| `ETSimplexNoise` | `"simplexNoise"` | Simplex noise |

### Audio-Reactive

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `ETAudioSpectrum` | `"audioSpectrum"` | Audio frequency data |
| `ETAudioLevel` | `"audioLevel"` | Audio amplitude |

### Custom

| Constructor | String ID | Description |
|-------------|-----------|-------------|
| `ETCustom String` | `"custom:..."` | Custom expression code |

### Serialization

```purescript
expressionTypeToString   :: ExpressionType -> String
expressionTypeFromString :: String -> Maybe ExpressionType
```

### Predicates

```purescript
isExpressionTypeMath :: ExpressionType -> Boolean
  -- True for: Add, Subtract, Multiply, Divide, Modulo,
  --           Length, Normalize, Distance, Lerp

isExpressionTypeTime :: ExpressionType -> Boolean
  -- True for: Time, Wiggle, Loop, Smooth, Noise, SimplexNoise
```

## PropertyExpression

Expression attached to a property for procedural animation.

```purescript
newtype PropertyExpression = PropertyExpression
  { enabled        :: Boolean        -- Is expression active
  , expressionType :: ExpressionType -- Type of expression
  , expressionCode :: String         -- Raw expression code
  , parameters     :: String         -- JSON-encoded parameters
  }
```

### Constructor

```purescript
defaultPropertyExpression :: PropertyExpression
  -- Disabled, Hold type, empty code, empty parameters
```

### Accessor

```purescript
propertyExpressionEnabled :: PropertyExpression -> Boolean
```

### Common Expression Patterns

| Pattern | Expression Type | Parameters |
|---------|-----------------|------------|
| Wiggle | `ETWiggle` | `{ frequency: 2, amplitude: 10 }` |
| Loop | `ETLoop` | `{ startFrame: 0, endFrame: 30 }` |
| Audio-reactive scale | `ETAudioLevel` | `{ minScale: 1, maxScale: 2 }` |
| Noise position | `ETNoise` | `{ frequency: 0.5, amplitude: 50 }` |

────────────────────────────────────────────────────────────────────────────────
                                                                  // evaluation
────────────────────────────────────────────────────────────────────────────────

The evaluation engine takes a frame number and keyframe sequence, returning
the interpolated value. This is the core of animation playback.

## Bracket (5 variants)

Result of finding keyframes that bracket a given frame position.

| Constructor | Parameters | Meaning |
|-------------|------------|---------|
| `BeforeFirst` | `Keyframe` | Frame is before first keyframe |
| `AfterLast` | `Keyframe` | Frame is after last keyframe |
| `Between` | `Keyframe, Keyframe` | Frame is between two keyframes |
| `ExactMatch` | `Keyframe` | Frame exactly matches a keyframe |
| `NoKeyframes` | — | Sequence has no keyframes |

```purescript
data Bracket
  = BeforeFirst Keyframe
  | AfterLast Keyframe
  | Between Keyframe Keyframe
  | ExactMatch Keyframe
  | NoKeyframes
```

## findBracketingKeyframes

Find the keyframes that bracket a given frame position.

```purescript
findBracketingKeyframes :: Frames -> Array Keyframe -> Bracket
```

**Algorithm:**
1. Sort keyframes by frame number
2. If target < first keyframe → `BeforeFirst`
3. If target > last keyframe → `AfterLast`
4. If target == keyframe → `ExactMatch`
5. Otherwise → `Between prev next`

## calculateProgress

Calculate linear progress (0.0 to 1.0) between two keyframes.

```purescript
calculateProgress :: Frames -> Keyframe -> Keyframe -> Number
```

**Formula:**
```
progress = (target - startFrame) / (endFrame - startFrame)
```

- Returns 1.0 if duration <= 0 (prevents division by zero)
- Does not apply easing — returns raw linear interpolant

## applyEasing

Apply easing based on interpolation type and tangent.

```purescript
applyEasing :: InterpolationType -> Tangent -> Number -> Number
```

**Behavior by InterpolationType:**

| Type | Easing Applied |
|------|----------------|
| `Linear` | No easing (identity) |
| `Auto` | No easing (smooth tangents pre-computed) |
| `Hold` | Returns 0.0 (stays at previous value) |
| `Bezier` | Cubic bezier from tangent handles |

**Bezier evaluation:**
Tangent x/y values become control points for cubic bezier curve.
The easing module evaluates the curve at the linear progress to get
the eased progress.

## evaluateAt

**Primary evaluation function** — evaluates keyframe sequence at a frame.

```purescript
evaluateAt :: Frames -> Array Keyframe -> Maybe KeyframeValue
```

**Algorithm:**
1. Find bracketing keyframes
2. For `BeforeFirst`, `AfterLast`, `ExactMatch` → return keyframe value
3. For `Between`:
   - Calculate linear progress
   - Apply easing from outgoing keyframe's interpolation type
   - Lerp between values using eased progress
4. Return `Nothing` for empty sequences

**Example:**
```purescript
import Hydrogen.Schema.Motion.Evaluate as Eval
import Hydrogen.Schema.Motion.Keyframe as KF
import Hydrogen.Schema.Dimension.Temporal (frames)

-- Two keyframes: 0→100 over 30 frames
keyframes =
  [ KF.keyframe (frames 0.0) (KF.NumberValue 0.0)
  , KF.keyframe (frames 30.0) (KF.NumberValue 100.0)
  ]

Eval.evaluateAt (frames 15.0) keyframes
-- Returns: Just (NumberValue 50.0)
```

## evaluateAtWithEasing

Evaluate with explicit easing override — useful for spring animations.

```purescript
evaluateAtWithEasing :: Frames -> Easing -> Array Keyframe -> Maybe KeyframeValue
```

Ignores keyframe interpolation types; applies provided easing uniformly.

────────────────────────────────────────────────────────────────────────────────
                                                            // cross-references
────────────────────────────────────────────────────────────────────────────────

## Dependencies

**Property.purs:**
- `Prelude` — Eq, Ord, Show, basic operators
- `Data.Maybe` — Maybe for smart constructors
- `Data.Array` — Array operations
- `Data.String` — String splitting for paths

**Evaluate.purs:**
- `Data.Array` — head, last, sortBy, filter
- `Data.Maybe` — Maybe for results
- `Data.Ordering` — Ordering for sorting
- `Hydrogen.Schema.Dimension.Temporal` — Frames newtype
- `Hydrogen.Schema.Motion.Easing` — Easing curves
- `Hydrogen.Schema.Motion.Keyframe` — Keyframe, KeyframeValue, InterpolationType

## Related Modules

**Within Motion:**
- `Motion/Keyframe.purs` — Keyframe definitions used by Evaluate
- `Motion/Easing.purs` — Easing curves applied during evaluation
- `Motion/Interpolation.purs` — Value interpolation functions

**From LATTICE (Haskell backend):**
- `Lattice.Entities` — Mirrored property structure for backend rendering

## Usage Examples

### Creating a Property

```purescript
import Hydrogen.Schema.Motion.Property

-- Opacity property (numeric, 0-100)
opacityProp = defaultAnimatableProperty
  "layer-1-opacity"
  "Opacity"
  PVTNumber

-- Position property (2D spatial)
positionProp = defaultAnimatableProperty
  "layer-1-position"
  "Position"
  PVTPosition
```

### Adding an Expression

```purescript
import Hydrogen.Schema.Motion.Property

-- Wiggle expression for random motion
wiggleExpr = PropertyExpression
  { enabled: true
  , expressionType: ETWiggle
  , expressionCode: "wiggle(2, 10)"
  , parameters: """{"frequency": 2, "amplitude": 10}"""
  }

-- Apply to property
positionWithWiggle = AnimatableProperty
  { id: "layer-1-position"
  , name: "Position"
  , propertyType: PVTPosition
  , value: "[500, 500]"
  , animated: true
  , keyframeIds: ["kf-1", "kf-2"]
  , group: Just "Transform"
  , expression: Just wiggleExpr
  , simplified: false
  , locked: false
  , elided: false
  }
```

### Evaluating Keyframes

```purescript
import Hydrogen.Schema.Motion.Evaluate as Eval
import Hydrogen.Schema.Motion.Keyframe as KF
import Hydrogen.Schema.Dimension.Temporal (frames)

-- Define fade-in animation (0% to 100% opacity over 30 frames)
fadeInKeyframes =
  [ KF.keyframe (frames 0.0) (KF.NumberValue 0.0)
  , KF.keyframe (frames 30.0) (KF.NumberValue 100.0)
  ]

-- Evaluate at various frames
Eval.evaluateAt (frames 0.0) fadeInKeyframes   -- Just (NumberValue 0.0)
Eval.evaluateAt (frames 15.0) fadeInKeyframes  -- Just (NumberValue 50.0)
Eval.evaluateAt (frames 30.0) fadeInKeyframes  -- Just (NumberValue 100.0)
Eval.evaluateAt (frames 45.0) fadeInKeyframes  -- Just (NumberValue 100.0)
```

### Property Path Resolution

```purescript
import Hydrogen.Schema.Motion.Property (propertyPathFromString)

-- Parse path
path = propertyPathFromString "Transform/Position/X"
-- PropertyPath ["Transform", "Position", "X"]

-- Use for property lookup
findProperty :: PropertyPath -> Layer -> Maybe AnimatableProperty
findProperty path layer = 
  -- Walk property tree using path segments
  ...
```

### Audio-Reactive Animation

```purescript
import Hydrogen.Schema.Motion.Property

-- Scale responds to audio level
audioReactiveScale = PropertyExpression
  { enabled: true
  , expressionType: ETAudioLevel
  , expressionCode: ""
  , parameters: """{"minScale": 1.0, "maxScale": 1.5, "smoothing": 0.8}"""
  }

scaleProp = defaultAnimatableProperty "layer-1-scale" "Scale" PVTVector3
  # addExpression audioReactiveScale
```

────────────────────────────────────────────────────────────────────────────────

