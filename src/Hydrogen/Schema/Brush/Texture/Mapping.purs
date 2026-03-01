-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                      // hydrogen // schema // brush // texture // mapping
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Texture Depth Mapping — Configuration for input-to-depth modulation.
-- |
-- | ## Design Philosophy
-- |
-- | TextureDepthMapping defines how input signals (pressure, tilt, velocity)
-- | control texture depth. This enables expressive texture behavior where
-- | light pressure barely shows the canvas grain, while heavy pressure digs
-- | deep into the surface texture.
-- |
-- | ## The Mapping Pattern
-- |
-- | Following the established pattern from Pressure, Tilt, and Velocity
-- | mappings, TextureDepthMapping provides:
-- |
-- | - `depthControl`: What input type controls depth (or Off)
-- | - `depthAtMinInput`: Texture depth when input is at minimum
-- | - `depthAtMaxInput`: Texture depth when input is at maximum
-- | - `curve`: Transfer function for non-linear mapping
-- |
-- | ## Input Sources
-- |
-- | - **Pressure**: Light touch = shallow depth, heavy press = deep texture
-- | - **Tilt**: Perpendicular pen = shallow, tilted = deep (pencil shading)
-- | - **Velocity**: Slow strokes = deep texture, fast = skims surface
-- | - **Random**: Per-dab random depth variation
-- | - **Off**: Constant depth (uses the static depth value from config)
-- |
-- | ## Why This Matters
-- |
-- | Without proper depth mapping, an agent cannot express:
-- | "Light pressure barely shows the paper grain, heavy pressure reveals
-- | every bump in the cold press watercolor paper."
-- |
-- | The depth range (min/max) makes this explicit and composable.
-- |
-- | ## Dependencies
-- |
-- | - Prelude
-- | - Texture.Types (TextureDepthControl)

module Hydrogen.Schema.Brush.Texture.Mapping
  ( -- * TextureDepthCurve ADT
    TextureDepthCurve
      ( DepthLinear
      , DepthSoft
      , DepthFirm
      , DepthSCurve
      , DepthLogarithmic
      , DepthExponential
      )
  , allTextureDepthCurves
  , textureDepthCurveDescription
  , textureDepthCurveFormula
  , textureDepthCurveMaxSensitivity
  , textureDepthCurveToId
  , textureDepthCurveDebugInfo
  
  -- * TextureDepthMapping Record
  , TextureDepthMapping
  , defaultTextureDepthMapping
  , textureDepthMappingDebugInfo
  
  -- * Presets
  , noDepthMapping
  , pressureDepthMapping
  , tiltDepthMapping
  , velocityDepthMapping
  , randomDepthMapping
  , gentlePressureMapping
  , dramaticPressureMapping
  
  -- * Queries
  , isDepthMappingEnabled
  , isDynamicDepth
  , getDepthRange
  , depthMappingComplexity
  
  -- * Debug Utilities
  , showWithDepthMapping
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , (+)
  , (-)
  , (*)
  , not
  , (==)
  )

import Hydrogen.Schema.Brush.Texture.Types
  ( TextureDepthControl
      ( DepthOff
      , DepthByPressure
      , DepthByTilt
      , DepthByVelocity
      , DepthByRandom
      )
  , textureDepthControlToId
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // texture depth curve
-- ═════════════════════════════════════════════════════════════════════════════

-- | Transfer function for texture depth mapping.
-- |
-- | Controls how input values (0-1) map to depth values (0-1).
-- | Same curve vocabulary as PressureCurve and VelocityCurve.
-- |
-- | - **Linear**: Direct 1:1 mapping, f(t) = t
-- | - **Soft**: Sensitive to light input, f(t) = sqrt(t)
-- | - **Firm**: Requires more input, f(t) = t²
-- | - **SCurve**: Smooth middle region, f(t) = 3t² - 2t³
-- | - **Logarithmic**: Quick ramp then plateau, f(t) = log(1+9t)/log(10)
-- | - **Exponential**: Slow start rapid finish, f(t) = (e^t-1)/(e-1)
data TextureDepthCurve
  = DepthLinear       -- ^ Direct 1:1 mapping: f(t) = t
  | DepthSoft         -- ^ Light input sensitive: f(t) = sqrt(t)
  | DepthFirm         -- ^ Requires input: f(t) = t²
  | DepthSCurve       -- ^ Smooth S-curve: f(t) = 3t² - 2t³
  | DepthLogarithmic  -- ^ Quick ramp, plateau: f(t) = log(1+9t)/log(10)
  | DepthExponential  -- ^ Slow start, fast end: f(t) = (e^t-1)/(e-1)

derive instance eqTextureDepthCurve :: Eq TextureDepthCurve
derive instance ordTextureDepthCurve :: Ord TextureDepthCurve

instance showTextureDepthCurve :: Show TextureDepthCurve where
  show DepthLinear = "(TextureDepthCurve Linear)"
  show DepthSoft = "(TextureDepthCurve Soft)"
  show DepthFirm = "(TextureDepthCurve Firm)"
  show DepthSCurve = "(TextureDepthCurve SCurve)"
  show DepthLogarithmic = "(TextureDepthCurve Logarithmic)"
  show DepthExponential = "(TextureDepthCurve Exponential)"

-- | All available texture depth curve types.
allTextureDepthCurves :: Array TextureDepthCurve
allTextureDepthCurves =
  [ DepthLinear
  , DepthSoft
  , DepthFirm
  , DepthSCurve
  , DepthLogarithmic
  , DepthExponential
  ]

-- | Human-readable description of each texture depth curve.
textureDepthCurveDescription :: TextureDepthCurve -> String
textureDepthCurveDescription DepthLinear = "Linear 1:1 response, direct input mapping"
textureDepthCurveDescription DepthSoft = "Soft response, sensitive to light input"
textureDepthCurveDescription DepthFirm = "Firm response, requires stronger input"
textureDepthCurveDescription DepthSCurve = "S-curve response, smooth middle region"
textureDepthCurveDescription DepthLogarithmic = "Logarithmic response, quick ramp then plateau"
textureDepthCurveDescription DepthExponential = "Exponential response, slow start then rapid finish"

-- | Mathematical formula for each texture depth curve.
textureDepthCurveFormula :: TextureDepthCurve -> String
textureDepthCurveFormula DepthLinear = "f(t) = t"
textureDepthCurveFormula DepthSoft = "f(t) = sqrt(t)"
textureDepthCurveFormula DepthFirm = "f(t) = t^2"
textureDepthCurveFormula DepthSCurve = "f(t) = 3t^2 - 2t^3"
textureDepthCurveFormula DepthLogarithmic = "f(t) = log(1+9t)/log(10)"
textureDepthCurveFormula DepthExponential = "f(t) = (e^t - 1)/(e - 1)"

-- | Maximum sensitivity (derivative bound) for each texture depth curve.
-- |
-- | Bounds how rapidly the output changes with input.
-- | Important for smooth texture transitions.
-- |
-- | | Curve       | Derivative           | Max on [0,1] or [ε,1] |
-- | |-------------|----------------------|------------------------|
-- | | Linear      | 1                    | 1.0                    |
-- | | Soft        | 1/(2√t)             | 8.0 (at t = 1/256)     |
-- | | Firm        | 2t                   | 2.0                    |
-- | | SCurve      | 6t - 6t²            | 1.5 (at t = 0.5)       |
-- | | Logarithmic | 9/((1+9t)·ln(10))   | 3.91 (at t = 0)        |
-- | | Exponential | e^t/(e-1)           | 1.58 (at t = 1)        |
textureDepthCurveMaxSensitivity :: TextureDepthCurve -> Number
textureDepthCurveMaxSensitivity DepthLinear = 1.0
textureDepthCurveMaxSensitivity DepthSoft = 8.0
textureDepthCurveMaxSensitivity DepthFirm = 2.0
textureDepthCurveMaxSensitivity DepthSCurve = 1.5
textureDepthCurveMaxSensitivity DepthLogarithmic = 3.91
textureDepthCurveMaxSensitivity DepthExponential = 1.58

-- | Convert curve to string ID for serialization.
textureDepthCurveToId :: TextureDepthCurve -> String
textureDepthCurveToId DepthLinear = "linear"
textureDepthCurveToId DepthSoft = "soft"
textureDepthCurveToId DepthFirm = "firm"
textureDepthCurveToId DepthSCurve = "s-curve"
textureDepthCurveToId DepthLogarithmic = "logarithmic"
textureDepthCurveToId DepthExponential = "exponential"

-- | Debug info string for texture depth curve.
textureDepthCurveDebugInfo :: TextureDepthCurve -> String
textureDepthCurveDebugInfo curve =
  show curve <> " formula:" <> textureDepthCurveFormula curve
    <> " maxSensitivity:" <> show (textureDepthCurveMaxSensitivity curve)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // texture depth mapping
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for how input signals modulate texture depth.
-- |
-- | ## Field Descriptions
-- |
-- | - `depthControl`: What input type controls depth (Pressure, Tilt, etc.)
-- | - `depthAtMinInput`: Texture depth when input is at minimum (0-100%)
-- | - `depthAtMaxInput`: Texture depth when input is at maximum (0-100%)
-- | - `curve`: Transfer function for non-linear response
-- | - `jitter`: Additional random variation on top of dynamic depth (0-100%)
-- |
-- | ## Semantics
-- |
-- | When `depthControl = DepthByPressure`:
-- | - Input pressure 0.0 → depth = depthAtMinInput
-- | - Input pressure 1.0 → depth = depthAtMaxInput
-- | - Values between interpolated through curve
-- |
-- | When `depthControl = DepthOff`:
-- | - The mapping is ignored
-- | - Texture uses static depth from TextureConfig.depth
type TextureDepthMapping =
  { depthControl :: TextureDepthControl  -- What controls depth
  , depthAtMinInput :: Number            -- Depth at minimum input (0-100%)
  , depthAtMaxInput :: Number            -- Depth at maximum input (0-100%)
  , curve :: TextureDepthCurve           -- Transfer function
  , jitter :: Number                     -- Additional random variation (0-100%)
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // default
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default texture depth mapping: no dynamic control.
-- |
-- | Depth is constant, determined by TextureConfig.depth field.
-- | Min/max values are sensible defaults for when mapping is enabled.
defaultTextureDepthMapping :: TextureDepthMapping
defaultTextureDepthMapping =
  { depthControl: DepthOff              -- No dynamic control
  , depthAtMinInput: 20.0               -- Sensible default if enabled
  , depthAtMaxInput: 100.0              -- Sensible default if enabled
  , curve: DepthLinear                  -- Direct mapping
  , jitter: 0.0                         -- No random variation
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | No depth mapping (static depth).
-- |
-- | Texture depth is constant throughout the stroke.
-- | Used for: consistent texture feel, technical work.
noDepthMapping :: TextureDepthMapping
noDepthMapping = defaultTextureDepthMapping

-- | Pressure-controlled depth with standard range.
-- |
-- | Light pressure = subtle texture, heavy pressure = full texture.
-- | Most common configuration for natural media simulation.
-- | Used for: painting, sketching, general brush work.
pressureDepthMapping :: TextureDepthMapping
pressureDepthMapping =
  { depthControl: DepthByPressure
  , depthAtMinInput: 10.0               -- Subtle at light touch
  , depthAtMaxInput: 100.0              -- Full depth at heavy press
  , curve: DepthSoft                    -- Sensitive to light pressure
  , jitter: 0.0                         -- No additional variation
  }

-- | Tilt-controlled depth for pencil-like shading.
-- |
-- | Perpendicular pen = minimal texture, tilted = deep texture.
-- | Simulates pencil side-shading where texture is more visible.
-- | Used for: graphite simulation, charcoal, shading.
tiltDepthMapping :: TextureDepthMapping
tiltDepthMapping =
  { depthControl: DepthByTilt
  , depthAtMinInput: 15.0               -- Light texture when perpendicular
  , depthAtMaxInput: 100.0              -- Full texture when tilted flat
  , curve: DepthLinear                  -- Direct altitude mapping
  , jitter: 5.0                         -- Slight variation for organic feel
  }

-- | Velocity-controlled depth for expressive strokes.
-- |
-- | Slow strokes = deep texture (paint settles), fast = skims surface.
-- | Natural behavior for wet media simulation.
-- | Used for: watercolor, wet media, expressive painting.
velocityDepthMapping :: TextureDepthMapping
velocityDepthMapping =
  { depthControl: DepthByVelocity
  , depthAtMinInput: 100.0              -- Full depth when slow
  , depthAtMaxInput: 20.0               -- Shallow when fast
  , curve: DepthSCurve                  -- Smooth transition
  , jitter: 0.0                         -- No additional variation
  }

-- | Random depth for organic texture variation.
-- |
-- | Each dab gets random depth within range.
-- | Creates natural, varied texture appearance.
-- | Used for: organic brushes, natural media, textured effects.
randomDepthMapping :: TextureDepthMapping
randomDepthMapping =
  { depthControl: DepthByRandom
  , depthAtMinInput: 30.0               -- Minimum random depth
  , depthAtMaxInput: 100.0              -- Maximum random depth
  , curve: DepthLinear                  -- Direct (random already varied)
  , jitter: 0.0                         -- Random IS the jitter here
  }

-- | Gentle pressure mapping with narrow range.
-- |
-- | Light pressure has noticeable texture, heavy adds more.
-- | Less dramatic variation than standard pressure mapping.
-- | Used for: subtle texture, controlled variation.
gentlePressureMapping :: TextureDepthMapping
gentlePressureMapping =
  { depthControl: DepthByPressure
  , depthAtMinInput: 40.0               -- Already visible at light touch
  , depthAtMaxInput: 80.0               -- Doesn't max out
  , curve: DepthSoft                    -- Responsive to light pressure
  , jitter: 5.0                         -- Slight organic variation
  }

-- | Dramatic pressure mapping with full range.
-- |
-- | Light pressure = nearly invisible texture, heavy = maximum.
-- | Creates dramatic difference between light and heavy strokes.
-- | Used for: expressive work, dramatic texture control.
dramaticPressureMapping :: TextureDepthMapping
dramaticPressureMapping =
  { depthControl: DepthByPressure
  , depthAtMinInput: 0.0                -- No texture at light touch
  , depthAtMaxInput: 100.0              -- Full texture at heavy press
  , curve: DepthFirm                    -- Requires firm pressure
  , jitter: 0.0                         -- No additional variation
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if depth mapping is enabled (not Off).
isDepthMappingEnabled :: TextureDepthMapping -> Boolean
isDepthMappingEnabled m = not (m.depthControl == DepthOff)

-- | Check if depth has any dynamic behavior.
-- | Returns true if controlled by input or has jitter.
isDynamicDepth :: TextureDepthMapping -> Boolean
isDynamicDepth m = 
  isDepthMappingEnabled m

-- | Get the depth range (max - min).
-- | Useful for understanding the dynamic range of the mapping.
getDepthRange :: TextureDepthMapping -> Number
getDepthRange m = m.depthAtMaxInput - m.depthAtMinInput

-- | Calculate mapping complexity score (0-100).
-- | Higher values indicate more complex/expensive computation.
depthMappingComplexity :: TextureDepthMapping -> Number
depthMappingComplexity m =
  controlScore + rangeScore + jitterScore
  where
    -- Base score for control type
    controlScore :: Number
    controlScore = case m.depthControl of
      DepthOff -> 0.0
      DepthByPressure -> 10.0
      DepthByTilt -> 15.0        -- Tilt requires more processing
      DepthByVelocity -> 20.0    -- Velocity requires smoothing
      DepthByRandom -> 5.0       -- Random is cheap
    
    -- Score for dynamic range
    rangeScore :: Number
    rangeScore = (m.depthAtMaxInput - m.depthAtMinInput) * 0.3
    
    -- Score for jitter
    jitterScore :: Number
    jitterScore = m.jitter * 0.2

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // debug utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate debug info string for TextureDepthMapping.
-- |
-- | Produces a parseable, unambiguous representation.
-- | Format: "(TextureDepthMapping { control: pressure, range: 10→100, curve: soft })"
textureDepthMappingDebugInfo :: TextureDepthMapping -> String
textureDepthMappingDebugInfo m =
  "(TextureDepthMapping { " <>
  "control: " <> textureDepthControlToId m.depthControl <> ", " <>
  "range: " <> show m.depthAtMinInput <> "→" <> show m.depthAtMaxInput <> "%, " <>
  "curve: " <> textureDepthCurveToId m.curve <>
  showJitter m <>
  " })"
  where
    showJitter :: TextureDepthMapping -> String
    showJitter mapping =
      if mapping.jitter == 0.0
        then ""
        else ", jitter: " <> show mapping.jitter <> "%"

-- | Combine a label with its depth mapping debug info.
-- |
-- | Useful for logging preset configurations with identifying names.
showWithDepthMapping :: String -> TextureDepthMapping -> String
showWithDepthMapping label mapping =
  label <> ": " <> textureDepthMappingDebugInfo mapping
