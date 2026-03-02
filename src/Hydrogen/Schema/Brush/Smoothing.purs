-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // brush // smoothing
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Brush Smoothing — Stroke smoothing and stabilization.
-- |
-- | ## Design Philosophy
-- |
-- | Stroke smoothing reduces input jitter for cleaner lines. This module
-- | provides smoothing algorithms, bounded parameters, and configuration
-- | presets for various use cases from raw sketching to technical drawing.
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from submodules:
-- |
-- | - **Types**: SmoothingMode ADT
-- | - **Atoms**: Bounded smoothing parameters
-- | - **Config**: SmoothingConfig record and presets
-- |
-- | ## Dependencies
-- |
-- | - Smoothing.Types
-- | - Smoothing.Atoms
-- | - Smoothing.Config

module Hydrogen.Schema.Brush.Smoothing
  ( module Types
  , module Atoms
  , module Config
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Brush.Smoothing.Types
  ( SmoothingMode
      ( NoSmoothing
      , BasicSmoothing
      , PulledString
      , MovingAverage
      , ExponentialSmoothing
      , OneEuroFilter
      )
  , allSmoothingModes
  , isAdaptiveMode
  , requiresHistory
  , sameSmoothingModeKind
  , smoothingModeDebugInfo
  , smoothingModeDescription
  , smoothingModeLatency
  , smoothingModeToId
  ) as Types

import Hydrogen.Schema.Brush.Smoothing.Atoms
  ( Beta(Beta)
  , CatchUpSpeed(CatchUpSpeed)
  , MinCutoff(MinCutoff)
  , SmoothingStrength(SmoothingStrength)
  , StringLength(StringLength)
  , WindowSize(WindowSize)
  , beta
  , betaBounds
  , betaDebugInfo
  , catchUpSpeed
  , catchUpSpeedBounds
  , catchUpSpeedDebugInfo
  , defaultBeta
  , defaultCutoff
  , fastCatchUp
  , heavyStrength
  , highBeta
  , highCutoff
  , instantCatchUp
  , largeWindow
  , lightStrength
  , longString
  , lowBeta
  , lowCutoff
  , maxStrength
  , mediumString
  , mediumWindow
  , minCutoff
  , minCutoffBounds
  , minCutoffDebugInfo
  , minimalWindow
  , moderateStrength
  , noStrength
  , noString
  , normalCatchUp
  , shortString
  , slowCatchUp
  , smallWindow
  , smoothingStrength
  , smoothingStrengthBounds
  , smoothingStrengthDebugInfo
  , stringLength
  , stringLengthBounds
  , stringLengthDebugInfo
  , unwrapBeta
  , unwrapCatchUpSpeed
  , unwrapMinCutoff
  , unwrapSmoothingStrength
  , unwrapStringLength
  , unwrapWindowSize
  , windowSize
  , windowSizeBounds
  , windowSizeDebugInfo
  ) as Atoms

import Hydrogen.Schema.Brush.Smoothing.Config
  ( OneEuroConfig
  , SmoothingConfig
  , adaptiveSmoothing
  , defaultOneEuroConfig
  , defaultSmoothingConfig
  , estimatedLatency
  , hasSmoothing
  , isAdaptive
  , isPulledString
  , moderateSmoothing
  , oneEuroConfigDebugInfo
  , rawInput
  , showWithConfig
  , slightSmoothing
  , smoothingConfigDebugInfo
  , stabilizedDrawing
  , technicalDrawing
  , usesHistory
  ) as Config
