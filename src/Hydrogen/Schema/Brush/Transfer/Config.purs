-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // brush // transfer // config
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Transfer Configuration — How paint is deposited onto the canvas.
-- |
-- | ## Design Philosophy
-- |
-- | Transfer settings control the fundamental interaction between brush
-- | and canvas. Opacity sets the ceiling, Flow determines how quickly
-- | you reach it, and options like Buildup and Wet Edges add natural
-- | media behavior to digital strokes.
-- |
-- | ## Key Properties
-- |
-- | - **opacity**: Maximum darkness achievable in a single stroke
-- | - **flow**: How quickly opacity builds per dab
-- | - **buildup**: Whether overlapping dabs accumulate opacity
-- | - **wetEdges**: Whether paint pools at stroke edges
-- | - **airbrushMode**: Continuous spray while stylus held still
-- |
-- | ## Dependencies
-- |
-- | - Prelude
-- | - Transfer.Atoms

module Hydrogen.Schema.Brush.Transfer.Config
  ( -- * TransferConfig Record
    TransferConfig
  , defaultTransferConfig
  , transferConfigDebugInfo
  
  -- * Presets
  , opaqueBrush
  , glazingBrush
  , watercolorBrush
  , airbrushTransfer
  , inkBrush
  , markerBrush
  
  -- * Queries
  , hasWetMediaFeatures
  , hasAirbrushFeatures
  , willBuildUp
  , isFullyOpaque
  , isTransparent
  
  -- * Debug Utilities
  , showWithConfig
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
  , (>=)
  , (<=)
  )

import Hydrogen.Schema.Brush.Transfer.Atoms
  ( Opacity
  , Flow
  , opacity
  , flow
  , unwrapOpacity
  , unwrapFlow
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // transfer config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for paint transfer from brush to canvas.
-- |
-- | ## Field Descriptions
-- |
-- | - `transferOpacity`: Maximum opacity achievable in a single stroke (0-100%)
-- | - `transferFlow`: Paint deposited per dab, how quickly you reach opacity (0-100%)
-- | - `buildup`: When true, overlapping dabs accumulate beyond single-dab opacity
-- | - `wetEdges`: When true, paint pools at stroke edges (watercolor effect)
-- | - `wetEdgeThickness`: Width of the wet edge pool effect (0-100%)
-- | - `smoothing`: Stroke path smoothing amount (0-100%)
-- | - `airbrushMode`: When true, paint sprays continuously while stylus held
-- | - `airbrushRate`: Speed of paint accumulation in airbrush mode (0-100%)
type TransferConfig =
  { transferOpacity :: Opacity           -- Max stroke opacity
  , transferFlow :: Flow                 -- Paint per dab
  , buildup :: Boolean                   -- Overlapping dabs accumulate
  , wetEdges :: Boolean                  -- Paint pools at edges
  , wetEdgeThickness :: Number           -- Edge pool width (0-100)
  , smoothing :: Number                  -- Stroke smoothing (0-100)
  , airbrushMode :: Boolean              -- Continuous spray while held
  , airbrushRate :: Number               -- Spray accumulation rate (0-100)
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // default
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default transfer configuration: fully opaque, full flow, no special effects.
-- |
-- | Standard brush behavior with solid, consistent coverage.
-- | Suitable for general-purpose digital painting.
defaultTransferConfig :: TransferConfig
defaultTransferConfig =
  { transferOpacity: opacity 100.0       -- Fully opaque
  , transferFlow: flow 100.0             -- Full paint per dab
  , buildup: false                       -- No opacity accumulation
  , wetEdges: false                      -- No edge pooling
  , wetEdgeThickness: 25.0               -- Sensible default if enabled
  , smoothing: 0.0                       -- No path smoothing
  , airbrushMode: false                  -- Not airbrush
  , airbrushRate: 50.0                   -- Sensible default if enabled
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Opaque brush: solid, full coverage strokes.
-- |
-- | Maximum opacity and flow with no special effects.
-- | Every stroke completely covers what's beneath it.
-- | Used for: blocking in shapes, solid fills, opaque painting.
opaqueBrush :: TransferConfig
opaqueBrush =
  { transferOpacity: opacity 100.0       -- Fully opaque
  , transferFlow: flow 100.0             -- Immediate full coverage
  , buildup: false                       -- No accumulation
  , wetEdges: false                      -- No edge pooling
  , wetEdgeThickness: 20.0               -- Sensible default if enabled
  , smoothing: 0.0                       -- No smoothing
  , airbrushMode: false                  -- Not airbrush
  , airbrushRate: 40.0                   -- Sensible default if enabled
  }

-- | Glazing brush: transparent layers that build up.
-- |
-- | Low opacity with buildup enabled allows gradual layering.
-- | Multiple strokes create rich, deep colors through accumulation.
-- | Used for: glazing, subtle shading, color blending.
glazingBrush :: TransferConfig
glazingBrush =
  { transferOpacity: opacity 30.0        -- Transparent
  , transferFlow: flow 50.0              -- Moderate flow
  , buildup: true                        -- Layers accumulate
  , wetEdges: false                      -- No edge pooling
  , wetEdgeThickness: 15.0               -- Sensible default if enabled
  , smoothing: 10.0                      -- Slight smoothing
  , airbrushMode: false                  -- Not airbrush
  , airbrushRate: 30.0                   -- Sensible default if enabled
  }

-- | Watercolor brush: wet media with edge pooling.
-- |
-- | Moderate opacity with wet edges creates natural watercolor look.
-- | Paint pools at stroke edges, darker at boundaries.
-- | Used for: watercolor simulation, wet media effects.
watercolorBrush :: TransferConfig
watercolorBrush =
  { transferOpacity: opacity 60.0        -- Semi-transparent
  , transferFlow: flow 40.0              -- Lower flow for wet look
  , buildup: true                        -- Layers blend
  , wetEdges: true                       -- Paint pools at edges
  , wetEdgeThickness: 50.0               -- Prominent wet edge
  , smoothing: 20.0                      -- Smooth fluid strokes
  , airbrushMode: false                  -- Not airbrush
  , airbrushRate: 25.0                   -- Sensible default if enabled
  }

-- | Airbrush transfer: continuous gradual spray.
-- |
-- | Low flow with airbrush mode creates soft gradual buildup.
-- | Paint accumulates while stylus held in place.
-- | Used for: soft gradients, spray effects, subtle shading.
airbrushTransfer :: TransferConfig
airbrushTransfer =
  { transferOpacity: opacity 50.0        -- Semi-opaque maximum
  , transferFlow: flow 10.0              -- Very gradual buildup
  , buildup: true                        -- Continuous accumulation
  , wetEdges: false                      -- No wet edges
  , wetEdgeThickness: 10.0               -- Sensible default if enabled
  , smoothing: 30.0                      -- Smooth spray path
  , airbrushMode: true                   -- Continuous spray
  , airbrushRate: 20.0                   -- Slow accumulation
  }

-- | Ink brush: sharp, solid strokes.
-- |
-- | Maximum opacity and flow with no buildup.
-- | Clean, crisp marks like a technical pen.
-- | Used for: inking, line art, technical drawing.
inkBrush :: TransferConfig
inkBrush =
  { transferOpacity: opacity 100.0       -- Fully opaque
  , transferFlow: flow 100.0             -- Immediate full ink
  , buildup: false                       -- No accumulation
  , wetEdges: false                      -- Clean edges
  , wetEdgeThickness: 0.0                -- No wet edge
  , smoothing: 15.0                      -- Slight stabilization
  , airbrushMode: false                  -- Not airbrush
  , airbrushRate: 50.0                   -- Sensible default if enabled
  }

-- | Marker brush: semi-opaque with overlap darkening.
-- |
-- | High opacity with buildup simulates alcohol marker behavior.
-- | Overlapping strokes create darker areas.
-- | Used for: marker rendering, comic coloring, sketching.
markerBrush :: TransferConfig
markerBrush =
  { transferOpacity: opacity 80.0        -- Slightly transparent
  , transferFlow: flow 100.0             -- Full coverage per stroke
  , buildup: true                        -- Overlap darkens
  , wetEdges: false                      -- No wet pooling
  , wetEdgeThickness: 5.0                -- Sensible default if enabled
  , smoothing: 5.0                       -- Minimal smoothing
  , airbrushMode: false                  -- Not airbrush
  , airbrushRate: 60.0                   -- Sensible default if enabled
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if config has wet media features enabled.
-- |
-- | Returns true when wet edges are enabled and have visible thickness.
hasWetMediaFeatures :: TransferConfig -> Boolean
hasWetMediaFeatures c = c.wetEdges && c.wetEdgeThickness >= 1.0

-- | Check if config has airbrush features enabled.
-- |
-- | Returns true when airbrush mode is on with a positive spray rate.
hasAirbrushFeatures :: TransferConfig -> Boolean
hasAirbrushFeatures c = c.airbrushMode && c.airbrushRate >= 1.0

-- | Check if overlapping strokes will build up.
-- |
-- | Returns true when buildup is enabled and opacity is below 100%,
-- | meaning there's room for accumulated darkening.
willBuildUp :: TransferConfig -> Boolean
willBuildUp c = c.buildup && unwrapOpacity c.transferOpacity <= 99.0

-- | Check if the brush produces fully opaque strokes.
-- |
-- | Returns true when opacity is at or near maximum (>= 99%).
isFullyOpaque :: TransferConfig -> Boolean
isFullyOpaque c = unwrapOpacity c.transferOpacity >= 99.0

-- | Check if the brush produces very transparent strokes.
-- |
-- | Returns true when opacity is very low (<= 20%).
isTransparent :: TransferConfig -> Boolean
isTransparent c = unwrapOpacity c.transferOpacity <= 20.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // debug utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate debug info string for TransferConfig.
-- |
-- | Produces a parseable, unambiguous representation.
-- | Format: "(TransferConfig { opacity: 100%, flow: 50%, buildup: on, ... })"
transferConfigDebugInfo :: TransferConfig -> String
transferConfigDebugInfo c =
  "(TransferConfig { " <>
  "opacity: " <> show (unwrapOpacity c.transferOpacity) <> "%, " <>
  "flow: " <> show (unwrapFlow c.transferFlow) <> "%, " <>
  "buildup: " <> showBool c.buildup <> ", " <>
  "wetEdges: " <> showWetEdges c <> ", " <>
  "smoothing: " <> show c.smoothing <> "%, " <>
  "airbrush: " <> showAirbrush c <>
  " })"
  where
    showBool :: Boolean -> String
    showBool b = if b then "on" else "off"
    
    showWetEdges :: TransferConfig -> String
    showWetEdges cfg =
      if cfg.wetEdges
        then "on " <> show cfg.wetEdgeThickness <> "%"
        else "off"
    
    showAirbrush :: TransferConfig -> String
    showAirbrush cfg =
      if cfg.airbrushMode
        then "on @" <> show cfg.airbrushRate <> "%"
        else "off"

-- | Combine a label with its transfer config debug info.
-- |
-- | Useful for logging preset configurations with identifying names.
-- | Example: showWithConfig "watercolor" watercolorBrush
showWithConfig :: String -> TransferConfig -> String
showWithConfig label config =
  label <> ": " <> transferConfigDebugInfo config
