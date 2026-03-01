-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // brush // transfer
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Transfer — Paint deposition from brush to canvas.
-- |
-- | ## Overview
-- |
-- | Transfer settings control how paint moves from the brush tip to the
-- | canvas surface. This includes opacity (maximum darkness), flow (rate
-- | of deposition), buildup behavior, wet media effects, and airbrush
-- | simulation.
-- |
-- | ## Module Structure
-- |
-- | - **Atoms**: Opacity, Flow, Wetness, Mix — bounded numeric primitives
-- | - **Config**: TransferConfig record with presets and queries
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Brush.Transfer
-- |   ( opacity, flow, watercolorBrush, hasWetMediaFeatures )
-- |
-- | myBrush = watercolorBrush
-- | hasWet = hasWetMediaFeatures myBrush  -- true
-- | ```
-- |
-- | ## Dependencies
-- |
-- | - Transfer.Atoms
-- | - Transfer.Config

module Hydrogen.Schema.Brush.Transfer
  ( -- * Re-exports from Transfer.Atoms
    -- ** Opacity (0 to 100)
    module AtomsExports
    
    -- * Re-exports from Transfer.Config
    -- ** TransferConfig Record
  , module ConfigExports
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Brush.Transfer.Atoms
  ( Opacity(Opacity)
  , opacity
  , opacityBounds
  , unwrapOpacity
  , noOpacity
  , halfOpacity
  , fullOpacity
  , opacityDebugInfo
  , Flow(Flow)
  , flow
  , flowBounds
  , unwrapFlow
  , noFlow
  , lowFlow
  , standardFlow
  , fullFlow
  , flowDebugInfo
  , Wetness(Wetness)
  , wetness
  , wetnessBounds
  , unwrapWetness
  , dry
  , damp
  , wet
  , soaking
  , wetnessDebugInfo
  , Mix(Mix)
  , mix
  , mixBounds
  , unwrapMix
  , noMix
  , subtleMix
  , moderateMix
  , heavyMix
  , mixDebugInfo
  , opacityInRange
  , flowInRange
  , wetnessInRange
  , mixInRange
  , isWetMediaCompatible
  , willProduceOutput
  ) as AtomsExports

import Hydrogen.Schema.Brush.Transfer.Config
  ( TransferConfig
  , defaultTransferConfig
  , transferConfigDebugInfo
  , opaqueBrush
  , glazingBrush
  , watercolorBrush
  , airbrushTransfer
  , inkBrush
  , markerBrush
  , hasWetMediaFeatures
  , hasAirbrushFeatures
  , willBuildUp
  , isFullyOpaque
  , isTransparent
  , showWithConfig
  ) as ConfigExports
