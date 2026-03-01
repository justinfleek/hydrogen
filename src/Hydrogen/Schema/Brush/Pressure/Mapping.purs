-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // schema // brush // pressure // mapping
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pressure Mapping — Configuration for pressure-to-parameter modulation.
-- |
-- | ## Design Philosophy
-- |
-- | PressureMapping defines which brush parameters respond to stylus pressure
-- | and how. Each mappable parameter has enable flag, min/max range, and
-- | inherits the curve from Types.PressureCurve.
-- |
-- | ## Key Properties
-- |
-- | - **affectsSize**: Diameter scales with pressure
-- | - **affectsOpacity**: Opacity scales with pressure
-- | - **affectsFlow**: Flow rate scales with pressure
-- | - **affectsHardness**: Edge hardness scales with pressure
-- | - **affectsScatter**: Scatter amount scales with pressure
-- |
-- | ## Dependencies
-- |
-- | - Prelude
-- | - Pressure.Types (PressureCurve)

module Hydrogen.Schema.Brush.Pressure.Mapping
  ( -- * PressureMapping Record
    PressureMapping
  , defaultPressureMapping
  , pressureMappingDebugInfo
  
  -- * Presets
  , sizeOnlyMapping
  , opacityOnlyMapping
  , flowOnlyMapping
  , fullDynamicsMapping
  , noMapping
  
  -- * Queries
  , isFullyEnabled
  , isDisabled
  , affectsGeometry
  , affectsAppearance
  , countAffected
  
  -- * Debug Utilities
  , showWithMapping
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Show
  , show
  , (<>)
  , (&&)
  , (||)
  , not
  , (+)
  )

import Hydrogen.Schema.Brush.Pressure.Types
  ( PressureCurve(Linear, Soft)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // pressure mapping
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for how pressure modulates brush parameters.
-- |
-- | ## Field Descriptions
-- |
-- | - `affectsSize`: When true, brush diameter scales with pressure
-- | - `sizeMin`: Minimum diameter as percentage of base (0-100)
-- | - `sizeMax`: Maximum diameter as percentage of base (0-100)
-- | - `affectsOpacity`: When true, stroke opacity scales with pressure
-- | - `opacityMin`: Minimum opacity (0.0-1.0)
-- | - `opacityMax`: Maximum opacity (0.0-1.0)
-- | - `affectsFlow`: When true, paint flow per dab scales with pressure
-- | - `flowMin`: Minimum flow (0.0-1.0)
-- | - `flowMax`: Maximum flow (0.0-1.0)
-- | - `affectsHardness`: When true, edge hardness scales with pressure
-- | - `hardnessMin`: Minimum hardness percentage (0-100)
-- | - `hardnessMax`: Maximum hardness percentage (0-100)
-- | - `affectsScatter`: When true, scatter amount scales with pressure
-- | - `curve`: Transfer function from raw to effective pressure
type PressureMapping =
  { affectsSize :: Boolean
  , sizeMin :: Number        -- 0-100 percentage
  , sizeMax :: Number        -- 0-100 percentage
  , affectsOpacity :: Boolean
  , opacityMin :: Number     -- 0.0-1.0
  , opacityMax :: Number     -- 0.0-1.0
  , affectsFlow :: Boolean
  , flowMin :: Number        -- 0.0-1.0
  , flowMax :: Number        -- 0.0-1.0
  , affectsHardness :: Boolean
  , hardnessMin :: Number    -- 0-100 percentage
  , hardnessMax :: Number    -- 0-100 percentage
  , affectsScatter :: Boolean
  , curve :: PressureCurve
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // default
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default pressure mapping: size varies with pressure.
-- |
-- | This is the most common configuration for digital brushes.
-- | Light pressure = small brush, heavy pressure = large brush.
defaultPressureMapping :: PressureMapping
defaultPressureMapping =
  { affectsSize: true
  , sizeMin: 10.0
  , sizeMax: 100.0
  , affectsOpacity: false
  , opacityMin: 1.0
  , opacityMax: 1.0
  , affectsFlow: false
  , flowMin: 1.0
  , flowMax: 1.0
  , affectsHardness: false
  , hardnessMin: 0.0
  , hardnessMax: 100.0
  , affectsScatter: false
  , curve: Linear
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Size-only mapping with soft curve (sketching).
-- |
-- | Light touch gives fine lines, pressure gives bold strokes.
sizeOnlyMapping :: PressureMapping
sizeOnlyMapping =
  { affectsSize: true
  , sizeMin: 5.0
  , sizeMax: 100.0
  , affectsOpacity: false
  , opacityMin: 1.0
  , opacityMax: 1.0
  , affectsFlow: false
  , flowMin: 1.0
  , flowMax: 1.0
  , affectsHardness: false
  , hardnessMin: 0.0
  , hardnessMax: 100.0
  , affectsScatter: false
  , curve: Soft
  }

-- | Opacity-only mapping (airbrush style).
-- |
-- | Size stays constant, pressure builds up opacity.
-- | Light pressure = transparent, heavy pressure = opaque.
opacityOnlyMapping :: PressureMapping
opacityOnlyMapping =
  { affectsSize: false
  , sizeMin: 10.0      -- Sensible default range if enabled
  , sizeMax: 100.0
  , affectsOpacity: true
  , opacityMin: 0.1    -- Nearly transparent at light pressure
  , opacityMax: 1.0    -- Fully opaque at heavy pressure
  , affectsFlow: false
  , flowMin: 0.1       -- Sensible default range if enabled
  , flowMax: 1.0
  , affectsHardness: false
  , hardnessMin: 0.0
  , hardnessMax: 100.0
  , affectsScatter: false
  , curve: Linear
  }

-- | Flow-only mapping (paint buildup).
-- |
-- | Size and opacity constant, pressure controls paint deposit rate.
-- | Light pressure = thin paint deposit, heavy pressure = full flow.
flowOnlyMapping :: PressureMapping
flowOnlyMapping =
  { affectsSize: false
  , sizeMin: 10.0      -- Sensible default range if enabled
  , sizeMax: 100.0
  , affectsOpacity: false
  , opacityMin: 0.1    -- Sensible default range if enabled
  , opacityMax: 1.0
  , affectsFlow: true
  , flowMin: 0.05      -- Very light at minimum pressure
  , flowMax: 1.0       -- Full flow at maximum pressure
  , affectsHardness: false
  , hardnessMin: 0.0
  , hardnessMax: 100.0
  , affectsScatter: false
  , curve: Linear
  }

-- | Full dynamics: size, opacity, and flow all respond to pressure.
-- |
-- | Maximum expressiveness, mimics natural media most closely.
fullDynamicsMapping :: PressureMapping
fullDynamicsMapping =
  { affectsSize: true
  , sizeMin: 10.0
  , sizeMax: 100.0
  , affectsOpacity: true
  , opacityMin: 0.2
  , opacityMax: 1.0
  , affectsFlow: true
  , flowMin: 0.1
  , flowMax: 1.0
  , affectsHardness: true
  , hardnessMin: 20.0
  , hardnessMax: 100.0
  , affectsScatter: false
  , curve: Soft
  }

-- | No pressure mapping (mouse/trackpad mode).
-- |
-- | All parameters stay at their base values regardless of input.
-- | The min/max ranges are set to sensible defaults if user later enables them.
noMapping :: PressureMapping
noMapping =
  { affectsSize: false
  , sizeMin: 10.0      -- Sensible default range if enabled
  , sizeMax: 100.0
  , affectsOpacity: false
  , opacityMin: 0.1    -- Sensible default range if enabled
  , opacityMax: 1.0
  , affectsFlow: false
  , flowMin: 0.1       -- Sensible default range if enabled
  , flowMax: 1.0
  , affectsHardness: false
  , hardnessMin: 0.0   -- Sensible default range if enabled
  , hardnessMax: 100.0
  , affectsScatter: false
  , curve: Linear
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // debug
-- ═════════════════════════════════════════════════════════════════════════════

-- | Debug info string for pressure mapping.
-- |
-- | Shows which parameters are affected and the curve type.
pressureMappingDebugInfo :: PressureMapping -> String
pressureMappingDebugInfo m =
  "(PressureMapping"
    <> " size:" <> showAffects m.affectsSize m.sizeMin m.sizeMax
    <> " opacity:" <> showAffects m.affectsOpacity m.opacityMin m.opacityMax
    <> " flow:" <> showAffects m.affectsFlow m.flowMin m.flowMax
    <> " hardness:" <> showAffects m.affectsHardness m.hardnessMin m.hardnessMax
    <> " scatter:" <> showEnabled m.affectsScatter
    <> " curve:" <> show m.curve
    <> ")"
  where
    showAffects :: Boolean -> Number -> Number -> String
    showAffects enabled minVal maxVal =
      if enabled
        then show minVal <> "-" <> show maxVal
        else "off"
    
    showEnabled :: Boolean -> String
    showEnabled enabled = if not enabled then "off" else "on"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if all pressure effects are enabled.
-- |
-- | Returns true only when size, opacity, flow, hardness, AND scatter
-- | are all active. Used to identify "maximum pressure responsiveness"
-- | configurations.
isFullyEnabled :: PressureMapping -> Boolean
isFullyEnabled m =
  m.affectsSize
    && m.affectsOpacity
    && m.affectsFlow
    && m.affectsHardness
    && m.affectsScatter

-- | Check if all pressure effects are disabled.
-- |
-- | Returns true when no pressure modulation is active. Stylus force has
-- | no effect on brush output — equivalent to mouse/trackpad mode.
isDisabled :: PressureMapping -> Boolean
isDisabled m =
  not m.affectsSize
    && not m.affectsOpacity
    && not m.affectsFlow
    && not m.affectsHardness
    && not m.affectsScatter

-- | Check if pressure affects brush geometry (size or scatter).
-- |
-- | Geometry effects change the physical footprint of the brush.
-- | Size affects diameter, scatter affects dab placement.
affectsGeometry :: PressureMapping -> Boolean
affectsGeometry m = m.affectsSize || m.affectsScatter

-- | Check if pressure affects brush appearance (opacity, flow, or hardness).
-- |
-- | Appearance effects change how paint is deposited, not brush geometry.
-- | These control the "look" of strokes rather than their shape.
affectsAppearance :: PressureMapping -> Boolean
affectsAppearance m = m.affectsOpacity || m.affectsFlow || m.affectsHardness

-- | Count how many parameters are affected by pressure.
-- |
-- | Returns 0-5 indicating the number of active pressure modulations.
-- | Useful for UI indicators showing "pressure sensitivity level".
countAffected :: PressureMapping -> Int
countAffected m =
  boolToInt m.affectsSize
    + boolToInt m.affectsOpacity
    + boolToInt m.affectsFlow
    + boolToInt m.affectsHardness
    + boolToInt m.affectsScatter
  where
    boolToInt :: Boolean -> Int
    boolToInt b = if b then 1 else 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // debug utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Show any value alongside its pressure mapping context.
-- |
-- | Useful for debugging when you need to see both the input value
-- | and the mapping configuration that will be applied to it.
showWithMapping :: forall a. Show a => a -> PressureMapping -> String
showWithMapping value mapping =
  show value <> " with " <> pressureMappingDebugInfo mapping
