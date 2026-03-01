-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // brush // velocity // mapping
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Velocity Mapping — Configuration for velocity-to-parameter modulation.
-- |
-- | ## Design Philosophy
-- |
-- | Velocity mapping defines how stroke speed affects brush appearance.
-- | Fast strokes can produce thinner lines (ink pen), more transparent
-- | marks (watercolor), or no effect at all (technical marker).
-- |
-- | ## Key Properties
-- |
-- | - **affectsSize**: Fast strokes thin/thicken lines
-- | - **affectsOpacity**: Fast strokes fade/intensify marks
-- | - **affectsFlow**: Fast strokes reduce/increase paint flow
-- | - **affectsSpacing**: Fast strokes spread/cluster dabs
-- | - **affectsScatter**: Fast strokes increase/decrease randomness
-- |
-- | ## Dependencies
-- |
-- | - Prelude
-- | - Velocity.Types

module Hydrogen.Schema.Brush.Velocity.Mapping
  ( -- * VelocityMapping Record
    VelocityMapping
  , defaultVelocityMapping
  , velocityMappingDebugInfo
  
  -- * Presets
  , inkPenMapping
  , markerMapping
  , watercolorMapping
  , dryBrushMapping
  , disabledMapping
  
  -- * Queries
  , isFullyEnabled
  , isDisabled
  , affectsAppearance
  , affectsPlacement
  , countAffected
  
  -- * Debug Utilities
  , showWithMapping
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , (<>)
  , (&&)
  , (||)
  , not
  , (+)
  )

import Hydrogen.Schema.Brush.Velocity.Types
  ( VelocityCurve(..)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // velocity mapping
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for how velocity modulates brush parameters.
-- |
-- | ## Field Descriptions
-- |
-- | - `affectsSize`: When true, stroke speed affects brush diameter
-- | - `sizeAtMinVelocity`: Diameter when slow (0-100%)
-- | - `sizeAtMaxVelocity`: Diameter when fast (0-100%)
-- | - `affectsOpacity`: When true, stroke speed affects opacity
-- | - `opacityAtMinVelocity`: Opacity when slow (0-1)
-- | - `opacityAtMaxVelocity`: Opacity when fast (0-1)
-- | - `affectsFlow`: When true, stroke speed affects paint flow
-- | - `flowAtMinVelocity`: Flow when slow (0-1)
-- | - `flowAtMaxVelocity`: Flow when fast (0-1)
-- | - `affectsSpacing`: When true, stroke speed affects dab spacing
-- | - `spacingAtMinVelocity`: Spacing when slow (0-100%)
-- | - `spacingAtMaxVelocity`: Spacing when fast (0-100%)
-- | - `affectsScatter`: When true, stroke speed affects scatter amount
-- | - `curve`: Transfer function for velocity mapping
-- | - `smoothingWindow`: Samples to average (1-10)
type VelocityMapping =
  { affectsSize :: Boolean
  , sizeAtMinVelocity :: Number        -- 0-100 percentage
  , sizeAtMaxVelocity :: Number        -- 0-100 percentage
  , affectsOpacity :: Boolean
  , opacityAtMinVelocity :: Number     -- 0-1
  , opacityAtMaxVelocity :: Number     -- 0-1
  , affectsFlow :: Boolean
  , flowAtMinVelocity :: Number        -- 0-1
  , flowAtMaxVelocity :: Number        -- 0-1
  , affectsSpacing :: Boolean
  , spacingAtMinVelocity :: Number     -- 0-100 percentage
  , spacingAtMaxVelocity :: Number     -- 0-100 percentage
  , affectsScatter :: Boolean
  , curve :: VelocityCurve
  , smoothingWindow :: Int             -- 1-10
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // default
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default velocity mapping: no velocity effects.
-- |
-- | Stroke speed has no effect on brush output. Suitable for
-- | technical drawing where consistency is desired.
-- | Min/max values are sensible defaults for if effects are enabled.
defaultVelocityMapping :: VelocityMapping
defaultVelocityMapping =
  { affectsSize: false
  , sizeAtMinVelocity: 100.0         -- Full size when slow
  , sizeAtMaxVelocity: 50.0          -- Sensible default if enabled
  , affectsOpacity: false
  , opacityAtMinVelocity: 1.0        -- Full opacity when slow
  , opacityAtMaxVelocity: 0.5        -- Sensible default if enabled
  , affectsFlow: false
  , flowAtMinVelocity: 1.0           -- Full flow when slow
  , flowAtMaxVelocity: 0.5           -- Sensible default if enabled
  , affectsSpacing: false
  , spacingAtMinVelocity: 25.0       -- Standard spacing when slow
  , spacingAtMaxVelocity: 50.0       -- Sensible default if enabled
  , affectsScatter: false
  , curve: VelocityLinear
  , smoothingWindow: 3
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ink pen: fast strokes produce thin, faint lines.
-- |
-- | Simulates traditional ink pen/brush behavior where quick
-- | strokes deposit less ink and create thinner marks.
-- | Used for: expressive calligraphy, gesture drawing.
inkPenMapping :: VelocityMapping
inkPenMapping =
  { affectsSize: true
  , sizeAtMinVelocity: 100.0         -- Full size when slow
  , sizeAtMaxVelocity: 30.0          -- Thin when fast
  , affectsOpacity: true
  , opacityAtMinVelocity: 1.0        -- Full opacity when slow
  , opacityAtMaxVelocity: 0.4        -- Faint when fast
  , affectsFlow: false
  , flowAtMinVelocity: 1.0           -- Sensible default if enabled
  , flowAtMaxVelocity: 0.5           -- Sensible default if enabled
  , affectsSpacing: false
  , spacingAtMinVelocity: 20.0       -- Sensible default if enabled
  , spacingAtMaxVelocity: 40.0       -- Sensible default if enabled
  , affectsScatter: false
  , curve: VelocitySCurve
  , smoothingWindow: 3
  }

-- | Marker: consistent strokes regardless of speed.
-- |
-- | Velocity has no effect on output. Technical markers and
-- | pens that deposit uniform marks at any speed.
-- | Used for: technical drawing, comics, uniform line work.
markerMapping :: VelocityMapping
markerMapping =
  { affectsSize: false
  , sizeAtMinVelocity: 100.0         -- Sensible default if enabled
  , sizeAtMaxVelocity: 60.0          -- Sensible default if enabled
  , affectsOpacity: false
  , opacityAtMinVelocity: 1.0        -- Sensible default if enabled
  , opacityAtMaxVelocity: 0.7        -- Sensible default if enabled
  , affectsFlow: false
  , flowAtMinVelocity: 1.0           -- Sensible default if enabled
  , flowAtMaxVelocity: 0.8           -- Sensible default if enabled
  , affectsSpacing: false
  , spacingAtMinVelocity: 25.0       -- Sensible default if enabled
  , spacingAtMaxVelocity: 35.0       -- Sensible default if enabled
  , affectsScatter: false
  , curve: VelocityLinear
  , smoothingWindow: 1
  }

-- | Watercolor: fast strokes produce thin, faint, dry marks.
-- |
-- | Simulates watercolor where quick strokes don't allow
-- | paint to flow fully onto the surface.
-- | Used for: wet media simulation, loose painting.
watercolorMapping :: VelocityMapping
watercolorMapping =
  { affectsSize: true
  , sizeAtMinVelocity: 100.0         -- Full size when slow
  , sizeAtMaxVelocity: 50.0          -- Thinner when fast
  , affectsOpacity: true
  , opacityAtMinVelocity: 1.0        -- Full opacity when slow
  , opacityAtMaxVelocity: 0.3        -- Very faint when fast
  , affectsFlow: true
  , flowAtMinVelocity: 1.0           -- Full flow when slow
  , flowAtMaxVelocity: 0.2           -- Little paint when fast
  , affectsSpacing: false
  , spacingAtMinVelocity: 20.0       -- Sensible default if enabled
  , spacingAtMaxVelocity: 45.0       -- Sensible default if enabled
  , affectsScatter: false
  , curve: VelocitySoft
  , smoothingWindow: 5
  }

-- | Dry brush: fast strokes produce thick, dry, textured marks.
-- |
-- | Opposite of typical ink behavior - fast strokes create
-- | bolder marks with less paint flow, revealing texture.
-- | Used for: textured strokes, expressive painting.
dryBrushMapping :: VelocityMapping
dryBrushMapping =
  { affectsSize: true
  , sizeAtMinVelocity: 80.0          -- Slightly smaller when slow
  , sizeAtMaxVelocity: 120.0         -- Larger when fast
  , affectsOpacity: false
  , opacityAtMinVelocity: 1.0        -- Sensible default if enabled
  , opacityAtMaxVelocity: 0.6        -- Sensible default if enabled
  , affectsFlow: true
  , flowAtMinVelocity: 1.0           -- Full flow when slow
  , flowAtMaxVelocity: 0.3           -- Dry when fast
  , affectsSpacing: true
  , spacingAtMinVelocity: 15.0       -- Dense when slow
  , spacingAtMaxVelocity: 50.0       -- Sparse when fast
  , affectsScatter: false
  , curve: VelocityFirm
  , smoothingWindow: 2
  }

-- | Disabled: velocity has no effect.
-- |
-- | All velocity data is ignored. Brush behaves identically
-- | regardless of stroke speed. Sensible defaults for all
-- | parameters in case effects are later enabled.
disabledMapping :: VelocityMapping
disabledMapping =
  { affectsSize: false
  , sizeAtMinVelocity: 100.0         -- Sensible default if enabled
  , sizeAtMaxVelocity: 40.0          -- Sensible default if enabled
  , affectsOpacity: false
  , opacityAtMinVelocity: 1.0        -- Sensible default if enabled
  , opacityAtMaxVelocity: 0.4        -- Sensible default if enabled
  , affectsFlow: false
  , flowAtMinVelocity: 1.0           -- Sensible default if enabled
  , flowAtMaxVelocity: 0.5           -- Sensible default if enabled
  , affectsSpacing: false
  , spacingAtMinVelocity: 20.0       -- Sensible default if enabled
  , spacingAtMaxVelocity: 60.0       -- Sensible default if enabled
  , affectsScatter: false
  , curve: VelocityLinear
  , smoothingWindow: 3
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if all velocity effects are enabled.
-- |
-- | Returns true when size, opacity, flow, spacing, and scatter
-- | are all affected by velocity. This is the maximum sensitivity.
isFullyEnabled :: VelocityMapping -> Boolean
isFullyEnabled m =
  m.affectsSize && m.affectsOpacity && m.affectsFlow && 
  m.affectsSpacing && m.affectsScatter

-- | Check if all velocity effects are disabled.
-- |
-- | Returns true when no parameters are affected by velocity.
-- | Brush behaves identically regardless of stroke speed.
isDisabled :: VelocityMapping -> Boolean
isDisabled m =
  not m.affectsSize && not m.affectsOpacity && not m.affectsFlow &&
  not m.affectsSpacing && not m.affectsScatter

-- | Check if velocity affects visual appearance.
-- |
-- | Returns true when velocity modulates any visual property
-- | (size, opacity, or flow). Does not include spacing/scatter.
affectsAppearance :: VelocityMapping -> Boolean
affectsAppearance m =
  m.affectsSize || m.affectsOpacity || m.affectsFlow

-- | Check if velocity affects dab placement.
-- |
-- | Returns true when velocity modulates spacing or scatter.
-- | These affect WHERE dabs are placed, not how they look.
affectsPlacement :: VelocityMapping -> Boolean
affectsPlacement m = m.affectsSpacing || m.affectsScatter

-- | Count how many parameters are affected by velocity.
-- |
-- | Returns 0-5 indicating the number of active velocity modulations.
-- | Useful for UI indicators showing "velocity sensitivity level".
countAffected :: VelocityMapping -> Int
countAffected m =
  boolToInt m.affectsSize
    + boolToInt m.affectsOpacity
    + boolToInt m.affectsFlow
    + boolToInt m.affectsSpacing
    + boolToInt m.affectsScatter
  where
    boolToInt :: Boolean -> Int
    boolToInt b = if b then 1 else 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // debug utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate debug info string for VelocityMapping.
-- |
-- | Produces a parseable, unambiguous representation.
-- | Format: "(VelocityMapping { size: on 100→30, opacity: off, ... })"
velocityMappingDebugInfo :: VelocityMapping -> String
velocityMappingDebugInfo m =
  "(VelocityMapping { " <>
  "size: " <> showToggle m.affectsSize m.sizeAtMinVelocity m.sizeAtMaxVelocity <> ", " <>
  "opacity: " <> showToggle m.affectsOpacity m.opacityAtMinVelocity m.opacityAtMaxVelocity <> ", " <>
  "flow: " <> showToggle m.affectsFlow m.flowAtMinVelocity m.flowAtMaxVelocity <> ", " <>
  "spacing: " <> showToggle m.affectsSpacing m.spacingAtMinVelocity m.spacingAtMaxVelocity <> ", " <>
  "scatter: " <> showBool m.affectsScatter <> ", " <>
  "curve: " <> show m.curve <> ", " <>
  "smoothing: " <> show m.smoothingWindow <>
  " })"
  where
    showToggle :: Boolean -> Number -> Number -> String
    showToggle enabled minVal maxVal =
      if enabled
        then "on " <> show minVal <> "→" <> show maxVal
        else "off"
    
    showBool :: Boolean -> String
    showBool b = if b then "on" else "off"

-- | Combine a label with its velocity mapping debug info.
-- |
-- | Useful for logging preset configurations with identifying names.
-- | Example: showWithMapping "inkPen" inkPenMapping
showWithMapping :: String -> VelocityMapping -> String
showWithMapping label mapping =
  label <> ": " <> velocityMappingDebugInfo mapping
