-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // brush // scatter // config
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Scatter Configuration — Randomization settings for organic brush behavior.
-- |
-- | ## Design Philosophy
-- |
-- | ScatterConfig combines scatter (positional displacement) with jitter
-- | (per-dab parameter randomization) to create natural, varied brush marks.
-- | These settings are essential for organic brushes like foliage, spray,
-- | and textured strokes.
-- |
-- | ## Key Properties
-- |
-- | - **scatter**: Perpendicular displacement from stroke path
-- | - **bothAxes**: Also scatter along stroke direction
-- | - **count**: Multiple dabs per spacing interval
-- | - **sizeJitter/angleJitter**: Per-dab randomization
-- |
-- | ## Dependencies
-- |
-- | - Prelude
-- | - Scatter.Atoms

module Hydrogen.Schema.Brush.Scatter.Config
  ( -- * ScatterConfig Record
    ScatterConfig
  , defaultScatterConfig
  , scatterConfigDebugInfo
  
  -- * Presets
  , noScatterConfig
  , lightScatterConfig
  , foliageConfig
  , starsConfig
  , confettiConfig
  , sprayConfig
  
  -- * Queries
  , hasScatter
  , hasJitter
  , isOrganic
  , isDense
  , hasFlipJitter
  
  -- * Debug Utilities
  , showWithScatterConfig
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , (<>)
  , (&&)
  , (||)
  , (>=)
  )

import Hydrogen.Schema.Brush.Scatter.Atoms
  ( Scatter(Scatter)
  , ScatterCount(ScatterCount)
  , SizeJitter(SizeJitter)
  , AngleJitter(AngleJitter)
  , RoundnessJitter(RoundnessJitter)
  , MinimumSize(MinimumSize)
  , MinimumRoundness(MinimumRoundness)
  , scatter
  , scatterCount
  , sizeJitter
  , angleJitter
  , roundnessJitter
  , minimumSize
  , minimumRoundness
  , unwrapScatter
  , unwrapScatterCount
  , unwrapSizeJitter
  , unwrapAngleJitter
  , unwrapRoundnessJitter
  , unwrapMinimumSize
  , unwrapMinimumRoundness
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // scatter config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for scatter and jitter behavior.
-- |
-- | ## Field Descriptions
-- |
-- | - `scatterAmount`: Perpendicular displacement from stroke path (0-1000%)
-- | - `bothAxes`: When true, scatter along stroke direction too
-- | - `dabCount`: Dabs placed per spacing interval (1-16)
-- | - `countJitter`: Random variation in dab count (0-100%)
-- | - `sizeJitterAmount`: Random size variation per dab (0-100%)
-- | - `minSize`: Floor for size jitter (0-100%)
-- | - `angleJitterAmount`: Random rotation per dab (0-100%)
-- | - `roundnessJitterAmount`: Random roundness variation (0-100%)
-- | - `minRoundness`: Floor for roundness jitter (0-100%)
-- | - `flipXJitter`: Random horizontal flip
-- | - `flipYJitter`: Random vertical flip
type ScatterConfig =
  { scatterAmount :: Scatter             -- Displacement amount
  , bothAxes :: Boolean                  -- Scatter in both directions
  , dabCount :: ScatterCount             -- Dabs per interval
  , countJitter :: Number                -- Count randomization (0-100)
  , sizeJitterAmount :: SizeJitter       -- Size randomization
  , minSize :: MinimumSize               -- Floor for size jitter
  , angleJitterAmount :: AngleJitter     -- Rotation randomization
  , roundnessJitterAmount :: RoundnessJitter  -- Shape randomization
  , minRoundness :: MinimumRoundness     -- Floor for roundness jitter
  , flipXJitter :: Boolean               -- Random horizontal flip
  , flipYJitter :: Boolean               -- Random vertical flip
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // default
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default scatter configuration: no scatter or jitter.
-- |
-- | Precise, consistent strokes with no randomization.
-- | Suitable for technical drawing and clean line work.
defaultScatterConfig :: ScatterConfig
defaultScatterConfig =
  { scatterAmount: scatter 0.0           -- No displacement
  , bothAxes: false                      -- Single axis
  , dabCount: scatterCount 1             -- One dab per interval
  , countJitter: 0.0                     -- No count variation
  , sizeJitterAmount: sizeJitter 0.0     -- No size variation
  , minSize: minimumSize 25.0            -- Sensible default if enabled
  , angleJitterAmount: angleJitter 0.0   -- No rotation variation
  , roundnessJitterAmount: roundnessJitter 0.0  -- No roundness variation
  , minRoundness: minimumRoundness 25.0  -- Sensible default if enabled
  , flipXJitter: false                   -- No horizontal flip
  , flipYJitter: false                   -- No vertical flip
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | No scatter: precise, consistent strokes.
-- |
-- | Identical to default. No randomization whatsoever.
-- | Used for: technical drawing, clean lines, precise work.
noScatterConfig :: ScatterConfig
noScatterConfig = defaultScatterConfig

-- | Light scatter: subtle natural variation.
-- |
-- | Small displacement and jitter for organic feel without chaos.
-- | Used for: pencil strokes, subtle texture, handwritten feel.
lightScatterConfig :: ScatterConfig
lightScatterConfig =
  { scatterAmount: scatter 50.0          -- Light displacement
  , bothAxes: false                      -- Perpendicular only
  , dabCount: scatterCount 1             -- Single dab
  , countJitter: 0.0                     -- No count variation
  , sizeJitterAmount: sizeJitter 10.0    -- Subtle size variation
  , minSize: minimumSize 80.0            -- Keep most of size
  , angleJitterAmount: angleJitter 10.0  -- Subtle rotation
  , roundnessJitterAmount: roundnessJitter 0.0  -- No roundness variation
  , minRoundness: minimumRoundness 50.0  -- Sensible default if enabled
  , flipXJitter: false                   -- No flipping
  , flipYJitter: false
  }

-- | Foliage: scattered leaves and grass.
-- |
-- | High scatter with multiple dabs and full rotation.
-- | Used for: leaves, grass, natural textures, organic patterns.
foliageConfig :: ScatterConfig
foliageConfig =
  { scatterAmount: scatter 200.0         -- Wide scatter
  , bothAxes: true                       -- Both directions
  , dabCount: scatterCount 3             -- Multiple dabs
  , countJitter: 30.0                    -- Some count variation
  , sizeJitterAmount: sizeJitter 50.0    -- Varied sizes
  , minSize: minimumSize 20.0            -- Can get quite small
  , angleJitterAmount: angleJitter 100.0 -- Full rotation
  , roundnessJitterAmount: roundnessJitter 20.0  -- Some shape variation
  , minRoundness: minimumRoundness 30.0  -- Limit flatness
  , flipXJitter: true                    -- Random flips
  , flipYJitter: true
  }

-- | Stars: widely scattered points.
-- |
-- | Very high scatter with size variation but no rotation.
-- | Used for: star fields, sparkles, scattered dots.
starsConfig :: ScatterConfig
starsConfig =
  { scatterAmount: scatter 500.0         -- Very wide scatter
  , bothAxes: true                       -- Full 2D scatter
  , dabCount: scatterCount 5             -- Multiple points
  , countJitter: 50.0                    -- Variable density
  , sizeJitterAmount: sizeJitter 80.0    -- Very varied sizes
  , minSize: minimumSize 5.0             -- Can be tiny
  , angleJitterAmount: angleJitter 0.0   -- No rotation (dots)
  , roundnessJitterAmount: roundnessJitter 0.0  -- Stay round
  , minRoundness: minimumRoundness 100.0 -- Always round
  , flipXJitter: false                   -- No flipping needed
  , flipYJitter: false
  }

-- | Confetti: scattered colorful shapes.
-- |
-- | High scatter with full rotation for party effect.
-- | Used for: confetti, scattered shapes, celebration effects.
confettiConfig :: ScatterConfig
confettiConfig =
  { scatterAmount: scatter 300.0         -- Wide scatter
  , bothAxes: true                       -- Full 2D
  , dabCount: scatterCount 4             -- Multiple shapes
  , countJitter: 40.0                    -- Variable count
  , sizeJitterAmount: sizeJitter 60.0    -- Varied sizes
  , minSize: minimumSize 30.0            -- Not too small
  , angleJitterAmount: angleJitter 100.0 -- Full random rotation
  , roundnessJitterAmount: roundnessJitter 30.0  -- Some shape variation
  , minRoundness: minimumRoundness 20.0  -- Can be quite flat
  , flipXJitter: true                    -- Random orientations
  , flipYJitter: true
  }

-- | Spray: airbrush spray pattern.
-- |
-- | Dense scatter with many dabs for spray paint effect.
-- | Used for: spray paint, airbrush, diffuse textures.
sprayConfig :: ScatterConfig
sprayConfig =
  { scatterAmount: scatter 100.0         -- Moderate scatter
  , bothAxes: true                       -- Full 2D spread
  , dabCount: scatterCount 8             -- Dense spray
  , countJitter: 20.0                    -- Some density variation
  , sizeJitterAmount: sizeJitter 30.0    -- Moderate size variation
  , minSize: minimumSize 40.0            -- Keep reasonable size
  , angleJitterAmount: angleJitter 0.0   -- No rotation (round dots)
  , roundnessJitterAmount: roundnessJitter 0.0  -- Stay round
  , minRoundness: minimumRoundness 100.0 -- Always round dots
  , flipXJitter: false                   -- No flipping
  , flipYJitter: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if scatter is enabled (amount >= 1%).
hasScatter :: ScatterConfig -> Boolean
hasScatter c = unwrapScatter c.scatterAmount >= 1.0

-- | Check if any jitter is enabled.
-- | Returns true if size, angle, or roundness jitter is >= 1%.
hasJitter :: ScatterConfig -> Boolean
hasJitter c = 
  unwrapSizeJitter c.sizeJitterAmount >= 1.0 ||
  unwrapAngleJitter c.angleJitterAmount >= 1.0 ||
  unwrapRoundnessJitter c.roundnessJitterAmount >= 1.0

-- | Check if configuration produces organic, varied strokes.
-- | Returns true if both scatter and jitter are significant.
isOrganic :: ScatterConfig -> Boolean
isOrganic c = hasScatter c && hasJitter c

-- | Check if configuration produces dense output.
-- | Returns true if dab count is >= 3.
isDense :: ScatterConfig -> Boolean
isDense c = unwrapScatterCount c.dabCount >= 3

-- | Check if flip jitter is enabled.
hasFlipJitter :: ScatterConfig -> Boolean
hasFlipJitter c = c.flipXJitter || c.flipYJitter

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // debug utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate debug info string for ScatterConfig.
-- |
-- | Produces a parseable, unambiguous representation.
scatterConfigDebugInfo :: ScatterConfig -> String
scatterConfigDebugInfo c =
  "(ScatterConfig { " <>
  "scatter: " <> show (unwrapScatter c.scatterAmount) <> "%" <>
  showBothAxes c <> ", " <>
  "count: " <> show (unwrapScatterCount c.dabCount) <>
  showCountJitter c <> ", " <>
  "sizeJitter: " <> show (unwrapSizeJitter c.sizeJitterAmount) <> "%" <>
  " min:" <> show (unwrapMinimumSize c.minSize) <> "%, " <>
  "angleJitter: " <> show (unwrapAngleJitter c.angleJitterAmount) <> "%, " <>
  "roundnessJitter: " <> show (unwrapRoundnessJitter c.roundnessJitterAmount) <> "%" <>
  " min:" <> show (unwrapMinimumRoundness c.minRoundness) <> "%" <>
  showFlips c <>
  " })"
  where
    showBothAxes :: ScatterConfig -> String
    showBothAxes cfg = if cfg.bothAxes then " (both axes)" else ""
    
    showCountJitter :: ScatterConfig -> String
    showCountJitter cfg = 
      if cfg.countJitter >= 1.0 
        then " ±" <> show cfg.countJitter <> "%"
        else ""
    
    showFlips :: ScatterConfig -> String
    showFlips cfg =
      case cfg.flipXJitter, cfg.flipYJitter of
        true, true -> ", flip: XY"
        true, false -> ", flip: X"
        false, true -> ", flip: Y"
        false, false -> ""

-- | Combine a label with its scatter config debug info.
showWithScatterConfig :: String -> ScatterConfig -> String
showWithScatterConfig label config =
  label <> ": " <> scatterConfigDebugInfo config
