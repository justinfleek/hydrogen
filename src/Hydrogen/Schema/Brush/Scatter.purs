-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // brush // scatter
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Scatter & Jitter — Randomization for organic brush behavior.
-- |
-- | ## Overview
-- |
-- | Scatter displaces brush dabs perpendicular to the stroke path. Jitter
-- | randomizes individual dab parameters (size, angle, roundness, opacity,
-- | flow). Together they create the natural variation essential for organic
-- | brushes — foliage, spray paint, star fields, confetti.
-- |
-- | ## The Physics of Natural Marks
-- |
-- | When a physical brush touches paper, each bristle leaves a slightly
-- | different mark. Paint splatter doesn't land in perfect rows. Leaves
-- | don't grow at uniform intervals. Scatter and jitter simulate this
-- | natural randomness within bounded, deterministic parameters.
-- |
-- | ## Key Concepts
-- |
-- | **Scatter** (positional displacement):
-- | - Perpendicular to stroke path by default
-- | - `bothAxes` enables parallel displacement too
-- | - Measured as percentage of brush diameter (0-1000%)
-- | - 100% = dabs can displace up to one brush width
-- |
-- | **Jitter** (per-dab parameter randomization):
-- | - Each dab gets randomized values within bounds
-- | - Size jitter: diameter varies per dab
-- | - Angle jitter: rotation varies per dab
-- | - Roundness jitter: ellipse ratio varies per dab
-- | - Opacity/flow jitter: transfer varies per dab
-- |
-- | **Count** (multiple dabs per interval):
-- | - Places multiple dabs at each spacing position
-- | - Combined with scatter creates dense spray effects
-- | - Count jitter randomizes how many dabs per position
-- |
-- | ## Module Structure
-- |
-- | - **Atoms**: Bounded numeric primitives (Scatter, ScatterCount, jitters)
-- | - **Config**: ScatterConfig record with presets and queries
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Brush.Scatter
-- |   ( scatter, scatterCount, sizeJitter, foliageConfig, isOrganic )
-- |
-- | -- Create a foliage brush
-- | myConfig = foliageConfig  -- 200% scatter, 3 dabs, full angle jitter
-- | isNatural = isOrganic myConfig  -- true
-- | ```
-- |
-- | ## Relationship to Other Modules
-- |
-- | - **Tip**: Scatter displaces the tip shape defined in Tip
-- | - **Transfer**: Opacity/flow jitter works with Transfer settings
-- | - **Color Dynamics**: Color jitter (hue/sat/brightness) in Color module
-- | - **Pressure**: Pressure can modulate scatter amount
-- |
-- | ## Dependencies
-- |
-- | - Scatter.Atoms
-- | - Scatter.Config

module Hydrogen.Schema.Brush.Scatter
  ( -- * Re-exports from Scatter.Atoms
    -- ** Scatter (0 to 1000)
    module AtomsExports
    
    -- * Re-exports from Scatter.Config
    -- ** ScatterConfig Record
  , module ConfigExports
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Brush.Scatter.Atoms
  ( -- Scatter (perpendicular displacement)
    Scatter(Scatter)
  , scatter
  , scatterBounds
  , unwrapScatter
  , noScatter
  , lightScatter
  , heavyScatter
  , extremeScatter
  , scatterDebugInfo
  
  -- ScatterCount (dabs per interval)
  , ScatterCount(ScatterCount)
  , scatterCount
  , scatterCountBounds
  , unwrapScatterCount
  , singleDab
  , fewDabs
  , manyDabs
  , maxDabs
  , scatterCountDebugInfo
  
  -- SizeJitter (diameter randomization)
  , SizeJitter(SizeJitter)
  , sizeJitter
  , sizeJitterBounds
  , unwrapSizeJitter
  , noSizeJitter
  , subtleSizeJitter
  , moderateSizeJitter
  , extremeSizeJitter
  , sizeJitterDebugInfo
  
  -- AngleJitter (rotation randomization)
  , AngleJitter(AngleJitter)
  , angleJitter
  , angleJitterBounds
  , unwrapAngleJitter
  , noAngleJitter
  , subtleAngleJitter
  , moderateAngleJitter
  , fullAngleJitter
  , angleJitterDebugInfo
  
  -- RoundnessJitter (aspect ratio randomization)
  , RoundnessJitter(RoundnessJitter)
  , roundnessJitter
  , roundnessJitterBounds
  , unwrapRoundnessJitter
  , noRoundnessJitter
  , subtleRoundnessJitter
  , roundnessJitterDebugInfo
  
  -- OpacityJitter (transparency randomization)
  , OpacityJitter(OpacityJitter)
  , opacityJitter
  , opacityJitterBounds
  , unwrapOpacityJitter
  , noOpacityJitter
  , subtleOpacityJitter
  , opacityJitterDebugInfo
  
  -- FlowJitter (flow rate randomization)
  , FlowJitter(FlowJitter)
  , flowJitter
  , flowJitterBounds
  , unwrapFlowJitter
  , noFlowJitter
  , subtleFlowJitter
  , flowJitterDebugInfo
  
  -- MinimumSize (floor for size jitter)
  , MinimumSize(MinimumSize)
  , minimumSize
  , minimumSizeBounds
  , unwrapMinimumSize
  , noMinimumSize
  , quarterMinimumSize
  , halfMinimumSize
  , minimumSizeDebugInfo
  
  -- MinimumRoundness (floor for roundness jitter)
  , MinimumRoundness(MinimumRoundness)
  , minimumRoundness
  , minimumRoundnessBounds
  , unwrapMinimumRoundness
  , noMinimumRoundness
  , minimumRoundnessDebugInfo
  
  -- Range queries
  , scatterInRange
  , hasSignificantScatter
  , hasSignificantJitter
  ) as AtomsExports

import Hydrogen.Schema.Brush.Scatter.Config
  ( -- ScatterConfig record
    ScatterConfig
  , defaultScatterConfig
  , scatterConfigDebugInfo
  
  -- Presets
  , noScatterConfig
  , lightScatterConfig
  , foliageConfig
  , starsConfig
  , confettiConfig
  , sprayConfig
  
  -- Queries
  , hasScatter
  , hasJitter
  , isOrganic
  , isDense
  , hasFlipJitter
  
  -- Debug utilities
  , showWithScatterConfig
  ) as ConfigExports
