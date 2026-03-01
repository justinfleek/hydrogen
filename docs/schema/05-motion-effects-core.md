# Motion Pillar: Effects Core

> Part of the Motion pillar documentation. See [05-motion.md](./05-motion.md) for index.

## Overview

The Effects Core module provides the foundational type system for all visual effects
in Hydrogen. This matches professional motion graphics effect architecture:

- **Parameter types** — Number, Color, Point, Angle, Checkbox, Dropdown, Layer, etc.
- **Effect categories** — Blur, Color Correction, Distort, Generate, Keying, etc.
- **Effect instances** — Applied effects with animatable parameters
- **Bounded primitives** — BlurRadius with UUID5 identity

Effects are applied to layers and evaluated per-frame. Parameters can be animated
with keyframes, driven by expressions, or linked to other properties.

## Source Files

```
src/Hydrogen/Schema/Motion/Effects/
├── Core.purs                           # Effect type system (516 lines)
└── Core/
    └── BlurRadius.purs                 # Bounded blur primitive (194 lines)
```

**Total: ~710 lines across 2 files**

## Effect Parameter Types

**Source**: `Core.purs` (lines 88-159)

Parameter types define what kind of value an effect parameter can hold.

```purescript
data EffectParameterType
  = EPTNumber      -- Numeric value (slider)
  | EPTColor       -- RGBA color picker
  | EPTPoint       -- 2D point (x, y)
  | EPTPoint3D     -- 3D point (x, y, z)
  | EPTAngle       -- Angle in degrees (circular slider)
  | EPTCheckbox    -- Boolean toggle
  | EPTDropdown    -- Selection from options
  | EPTLayer       -- Reference to another layer
  | EPTString      -- Text value
  | EPTCurve       -- Bezier curve (for curves adjustment)
  | EPTData        -- JSON-encoded data (extensible)

-- Enumeration and serialization
allEffectParameterTypes        :: Array EffectParameterType
effectParameterTypeToString    :: EffectParameterType -> String
effectParameterTypeFromString  :: String -> Maybe EffectParameterType
```

## Effect Animatable Types

**Source**: `Core.purs` (lines 161-200)

Animatable types are a subset of parameter types that can be keyframed.

```purescript
data EffectAnimatableType
  = EATNumber     -- Scalar number (most common)
  | EATPosition   -- 2D/3D position
  | EATColor      -- Color value
  | EATEnum       -- Enumerated value (discrete steps)
  | EATVector3    -- 3D vector

-- Enumeration and serialization
allEffectAnimatableTypes        :: Array EffectAnimatableType
effectAnimatableTypeToString    :: EffectAnimatableType -> String
effectAnimatableTypeFromString  :: String -> Maybe EffectAnimatableType
```

## Effect Categories

**Source**: `Core.purs` (lines 202-282)

Categories organize effects in the UI and define their purpose.

```purescript
data EffectCategory
  = ECBlurSharpen       -- Blur and sharpen effects
  | ECColorCorrection   -- Color adjustment effects
  | ECDistort           -- Distortion effects
  | ECGenerate          -- Generation effects (noise, patterns)
  | ECKeying            -- Keying/chroma key effects
  | ECMatte             -- Matte tools
  | ECNoiseGrain        -- Noise and grain effects
  | ECPerspective       -- 3D perspective effects
  | ECStylize           -- Stylization effects
  | ECTime              -- Time-based effects
  | ECTransition        -- Transition effects
  | ECUtility           -- Utility effects

-- Enumeration and serialization
allEffectCategories        :: Array EffectCategory
effectCategoryToString     :: EffectCategory -> String
effectCategoryFromString   :: String -> Maybe EffectCategory
```

## Parameter Value Types

**Source**: `Core.purs` (lines 284-366)

Concrete value types for effect parameters.

```purescript
-- 2D point
type EffectPoint2D = { x :: Number, y :: Number }
mkEffectPoint2D :: Number -> Number -> EffectPoint2D

-- 3D point
type EffectPoint3D = { x :: Number, y :: Number, z :: Number }
mkEffectPoint3D :: Number -> Number -> Number -> EffectPoint3D

-- RGBA color (RGB: 0-255, Alpha: 0.0-1.0)
type EffectRGBA = { r :: Int, g :: Int, b :: Int, a :: Number }
mkEffectRGBA     :: Int -> Int -> Int -> Number -> EffectRGBA
effectRGBAOpaque :: Int -> Int -> Int -> EffectRGBA  -- Alpha = 1.0

-- Curve point (for bezier parameters)
type CurvePoint = { x :: Number, y :: Number }
mkCurvePoint :: Number -> Number -> CurvePoint

-- Sum type for all parameter values
data EffectParameterValue
  = EPVNumber Number
  | EPVString String
  | EPVBoolean Boolean
  | EPVPoint2D EffectPoint2D
  | EPVPoint3D EffectPoint3D
  | EPVColor EffectRGBA
  | EPVCurve (Array CurvePoint)
  | EPVData String           -- JSON-encoded
  | EPVNull

-- Dropdown option
type EffectDropdownOption = { label :: String, value :: EffectParameterValue }
```

## Parameter Definitions

**Source**: `Core.purs` (lines 368-424)

Parameter definitions are templates; parameter instances hold actual values.

```purescript
-- Definition (template for parameter)
type EffectParameterDef =
  { name :: String
  , parameterType :: EffectParameterType
  , defaultValue :: EffectParameterValue
  , min :: Maybe Number           -- Minimum value (for sliders)
  , max :: Maybe Number           -- Maximum value
  , step :: Maybe Number          -- Step increment
  , options :: Maybe (Array EffectDropdownOption)  -- For dropdowns
  , animatable :: Boolean         -- Can be keyframed?
  , group :: Maybe String         -- UI grouping
  }

defaultEffectParameterDef 
  :: String -> EffectParameterType -> EffectParameterValue -> EffectParameterDef

-- Instance (actual parameter with value)
type EffectParameter =
  { id :: String
  , name :: String
  , parameterType :: EffectParameterType
  , value :: EffectParameterValue
  , defaultValue :: EffectParameterValue
  , min :: Maybe Number
  , max :: Maybe Number
  , step :: Maybe Number
  , options :: Maybe (Array EffectDropdownOption)
  , animatable :: Boolean
  , group :: Maybe String
  }

defaultEffectParameter 
  :: String -> String -> EffectParameterType -> EffectParameterValue -> EffectParameter
```

## Effect Types

**Source**: `Core.purs` (lines 426-516)

Effect identifiers, definitions, and instances.

```purescript
-- Unique effect identifier
newtype EffectId = EffectId String

mkEffectId :: String -> Maybe EffectId  -- Returns Nothing for empty string

-- Effect definition (applied to a layer)
type Effect =
  { id :: EffectId
  , name :: String
  , category :: EffectCategory
  , enabled :: Boolean
  , expanded :: Boolean           -- UI expanded state
  , parameters :: Array EffectParameter
  , fragmentShader :: Maybe String  -- Custom GLSL shader
  }

defaultEffect :: EffectId -> String -> EffectCategory -> Effect
effectEnabled :: Effect -> Boolean
```

## Effect Instances

**Source**: `Core.purs` (lines 471-516)

Effect instances are effects applied to a layer with animatable properties.

```purescript
-- Instance on a layer
type EffectInstance =
  { id :: EffectId
  , effectKey :: String           -- Reference to effect definition
  , name :: String
  , category :: EffectCategory
  , enabled :: Boolean
  , expanded :: Boolean
  , parameters :: Array AnimatablePropertyId  -- Property IDs for animation
  }

defaultEffectInstance 
  :: EffectId -> String -> String -> EffectCategory -> EffectInstance

-- Mesh deformation effect (uses warp pins)
type MeshDeformEffectInstance =
  { instance :: EffectInstance
  , pins :: Array WarpPin         -- From MeshWarp module
  , cachedMeshId :: Maybe String
  , meshDirty :: Boolean
  }

-- Effect type definition (template)
type EffectDefinition =
  { name :: String
  , category :: EffectCategory
  , description :: String
  , parameters :: Array EffectParameterDef
  , fragmentShader :: Maybe String
  }

-- Category info for UI
type EffectCategoryInfo =
  { label :: String
  , icon :: String
  , description :: String
  }
```

## BlurRadius Bounded Type

**Source**: `Core/BlurRadius.purs` (194 lines)

BlurRadius is a bounded primitive for blur amounts, demonstrating Hydrogen's
approach to type-safe effect parameters.

### Invariants

- Value ALWAYS in [0.0, 1000.0] pixels
- Smart constructor returns Maybe (validation)
- Clamping constructor always succeeds
- UUID5 identity from value (deterministic across agents)

```purescript
newtype BlurRadius = BlurRadius Number

-- Constructors
blurRadius       :: Number -> Maybe BlurRadius  -- Validates
blurRadiusUnsafe :: Number -> BlurRadius        -- No validation
clampBlurRadius  :: Number -> BlurRadius        -- Clamps to bounds

-- Accessors
unwrapBlurRadius  :: BlurRadius -> Number
blurRadiusPixels  :: BlurRadius -> Number  -- Alias

-- Constants
blurRadiusZero :: BlurRadius  -- 0.0
blurRadiusMin  :: BlurRadius  -- 0.0
blurRadiusMax  :: BlurRadius  -- 1000.0

-- Operations
scaleBlurRadius :: Number -> BlurRadius -> BlurRadius  -- Clamped
addBlurRadius   :: BlurRadius -> BlurRadius -> BlurRadius
lerpBlurRadius  :: Number -> BlurRadius -> BlurRadius -> BlurRadius  -- t clamped to [0,1]

-- Bounds metadata
blurRadiusBounds :: NumberBounds  -- 0.0 to 250.0 (professional image editor max)

-- UUID5 identity
blurRadiusUUID :: BlurRadius -> UUID5  -- Deterministic from value
```

### Why Bounded Types Matter

At billion-agent scale:
- **No defensive clamping needed** — Type guarantees validity
- **Deterministic identity** — Same value = same UUID across all agents
- **Type prevents mixing** — BlurRadius is not interchangeable with other pixels

Two agents creating `BlurRadius(50.0)` get the same UUID5. This enables:
- Deduplication in distributed systems
- Cache hits across agent sessions
- Proof that two agents computed the same result

