-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                      // hydrogen // schema // brush // smoothing // config
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Smoothing Configuration — Complete stroke smoothing settings.
-- |
-- | ## Design Philosophy
-- |
-- | SmoothingConfig combines the smoothing algorithm with its parameters
-- | into a cohesive configuration. Different presets balance latency and
-- | smoothness for various use cases.
-- |
-- | ## Key Properties
-- |
-- | - **mode**: Smoothing algorithm
-- | - **strength**: How much smoothing (0-100%)
-- | - **stringLength**: Distance for pulled-string stabilizer
-- | - **windowSize**: Sample count for averaging modes
-- | - **catchUp**: Whether cursor catches up on release
-- | - **catchUpSpeed**: How fast cursor catches up
-- | - **minCutoff**: One Euro Filter minimum cutoff
-- | - **beta**: One Euro Filter speed coefficient
-- |
-- | ## Dependencies
-- |
-- | - Prelude
-- | - Smoothing.Types
-- | - Smoothing.Atoms

module Hydrogen.Schema.Brush.Smoothing.Config
  ( -- * SmoothingConfig Record
    SmoothingConfig
  , defaultSmoothingConfig
  , smoothingConfigDebugInfo
  
  -- * Presets
  , rawInput
  , slightSmoothing
  , moderateSmoothing
  , stabilizedDrawing
  , technicalDrawing
  , adaptiveSmoothing
  
  -- * One Euro Filter Config
  , OneEuroConfig
  , defaultOneEuroConfig
  , oneEuroConfigDebugInfo
  
  -- * Queries
  , hasSmoothing
  , isPulledString
  , isAdaptive
  , usesHistory
  , estimatedLatency
  
  -- * Debug Utilities
  , showWithConfig
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , not
  , (<>)
  , (==)
  , (>=)
  )

import Hydrogen.Schema.Brush.Smoothing.Types
  ( SmoothingMode
      ( NoSmoothing
      , BasicSmoothing
      , PulledString
      , MovingAverage
      , ExponentialSmoothing
      , OneEuroFilter
      )
  , isAdaptiveMode
  , requiresHistory
  , smoothingModeToId
  )

import Hydrogen.Schema.Brush.Smoothing.Atoms
  ( SmoothingStrength
  , StringLength
  , WindowSize
  , CatchUpSpeed
  , MinCutoff
  , Beta
  , smoothingStrength
  , stringLength
  , windowSize
  , catchUpSpeed
  , unwrapSmoothingStrength
  , unwrapStringLength
  , unwrapWindowSize
  , unwrapCatchUpSpeed
  , unwrapMinCutoff
  , unwrapBeta
  , noStrength
  , lightStrength
  , moderateStrength
  , heavyStrength
  , maxStrength
  , noString
  , shortString
  , mediumString
  , longString
  , minimalWindow
  , smallWindow
  , mediumWindow
  , normalCatchUp
  , fastCatchUp
  , instantCatchUp
  , lowCutoff
  , defaultCutoff
  , defaultBeta
  , highBeta
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // one euro config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for One Euro Filter.
-- |
-- | The One Euro Filter is an adaptive low-pass filter that smooths
-- | slow movements while preserving fast, intentional strokes.
-- |
-- | ## Parameters
-- |
-- | - `minCutoff`: Minimum cutoff frequency (lower = more smoothing)
-- | - `beta`: Speed coefficient (higher = more responsive to speed)
-- | - `derivativeCutoff`: Derivative cutoff for stability
type OneEuroConfig =
  { minCutoff :: MinCutoff
  , beta :: Beta
  , derivativeCutoff :: Number
  }

-- | Default One Euro Filter configuration.
-- |
-- | Balanced settings suitable for most drawing applications.
defaultOneEuroConfig :: OneEuroConfig
defaultOneEuroConfig =
  { minCutoff: defaultCutoff
  , beta: defaultBeta
  , derivativeCutoff: 1.0
  }

-- | Debug info for One Euro config.
oneEuroConfigDebugInfo :: OneEuroConfig -> String
oneEuroConfigDebugInfo c =
  "(OneEuroConfig { minCutoff: " <> show (unwrapMinCutoff c.minCutoff) <>
  "Hz, beta: " <> show (unwrapBeta c.beta) <>
  ", dcutoff: " <> show c.derivativeCutoff <> " })"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // smoothing config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete smoothing configuration.
-- |
-- | ## Field Descriptions
-- |
-- | - `mode`: Smoothing algorithm to use
-- | - `strength`: Smoothing intensity (0-100%)
-- | - `stringLength`: Distance for pulled-string (when mode is PulledString)
-- | - `windowSize`: Sample window for averaging modes
-- | - `catchUp`: Whether cursor catches up on stroke end
-- | - `catchUpSpeed`: Rate of catch-up animation
-- | - `oneEuro`: Configuration for One Euro Filter mode
type SmoothingConfig =
  { mode :: SmoothingMode
  , strength :: SmoothingStrength
  , stringLength :: StringLength
  , windowSize :: WindowSize
  , catchUp :: Boolean
  , catchUpSpeed :: CatchUpSpeed
  , oneEuro :: OneEuroConfig
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // default
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default smoothing configuration: light basic smoothing.
-- |
-- | Balanced settings with minimal latency impact.
defaultSmoothingConfig :: SmoothingConfig
defaultSmoothingConfig =
  { mode: BasicSmoothing
  , strength: lightStrength
  , stringLength: noString
  , windowSize: smallWindow
  , catchUp: true
  , catchUpSpeed: normalCatchUp
  , oneEuro: defaultOneEuroConfig
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Raw input: No smoothing at all.
-- |
-- | Zero latency, maximum responsiveness.
-- | Best for: Sketchy, expressive work.
rawInput :: SmoothingConfig
rawInput =
  { mode: NoSmoothing
  , strength: noStrength
  , stringLength: noString
  , windowSize: minimalWindow
  , catchUp: false
  , catchUpSpeed: instantCatchUp
  , oneEuro: defaultOneEuroConfig
  }

-- | Slight smoothing: Minimal processing.
-- |
-- | Natural feel with just enough smoothing to reduce jitter.
-- | Best for: General drawing, natural media emulation.
slightSmoothing :: SmoothingConfig
slightSmoothing =
  { mode: BasicSmoothing
  , strength: lightStrength
  , stringLength: shortString
  , windowSize: smallWindow
  , catchUp: true
  , catchUpSpeed: fastCatchUp
  , oneEuro: defaultOneEuroConfig
  }

-- | Moderate smoothing: Balanced settings.
-- |
-- | Good compromise between smoothness and responsiveness.
-- | Best for: Digital illustration, clean linework.
moderateSmoothing :: SmoothingConfig
moderateSmoothing =
  { mode: MovingAverage
  , strength: moderateStrength
  , stringLength: mediumString
  , windowSize: mediumWindow
  , catchUp: true
  , catchUpSpeed: normalCatchUp
  , oneEuro: defaultOneEuroConfig
  }

-- | Stabilized drawing: Pulled-string stabilizer.
-- |
-- | High control with visible lag. Cursor follows at a distance.
-- | Best for: Precise curves, inking, vector work.
stabilizedDrawing :: SmoothingConfig
stabilizedDrawing =
  { mode: PulledString
  , strength: heavyStrength
  , stringLength: longString
  , windowSize: mediumWindow
  , catchUp: true
  , catchUpSpeed: normalCatchUp
  , oneEuro: defaultOneEuroConfig
  }

-- | Technical drawing: Maximum stabilization.
-- |
-- | Very deliberate strokes with significant lag.
-- | Best for: Technical illustration, architectural drawing.
technicalDrawing :: SmoothingConfig
technicalDrawing =
  { mode: PulledString
  , strength: maxStrength
  , stringLength: stringLength 200.0
  , windowSize: windowSize 16
  , catchUp: true
  , catchUpSpeed: catchUpSpeed 0.3
  , oneEuro: defaultOneEuroConfig
  }

-- | Adaptive smoothing: One Euro Filter.
-- |
-- | Smooth when slow, responsive when fast.
-- | Best for: Best of both worlds, professional use.
adaptiveSmoothing :: SmoothingConfig
adaptiveSmoothing =
  { mode: OneEuroFilter
  , strength: moderateStrength
  , stringLength: noString
  , windowSize: smallWindow
  , catchUp: true
  , catchUpSpeed: normalCatchUp
  , oneEuro:
      { minCutoff: lowCutoff
      , beta: highBeta
      , derivativeCutoff: 1.0
      }
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if config has any smoothing enabled.
hasSmoothing :: SmoothingConfig -> Boolean
hasSmoothing c = not (smoothingModeToId c.mode == "none")

-- | Check if config uses pulled-string stabilizer.
isPulledString :: SmoothingConfig -> Boolean
isPulledString c = smoothingModeToId c.mode == "pulled-string"

-- | Check if config uses adaptive (One Euro) smoothing.
isAdaptive :: SmoothingConfig -> Boolean
isAdaptive c = isAdaptiveMode c.mode

-- | Check if config requires sample history.
usesHistory :: SmoothingConfig -> Boolean
usesHistory c = requiresHistory c.mode

-- | Estimate relative latency of the config.
-- |
-- | Returns a qualitative latency descriptor.
estimatedLatency :: SmoothingConfig -> String
estimatedLatency c = latencyFromMode (smoothingModeToId c.mode) (unwrapSmoothingStrength c.strength)

-- | Helper to determine latency from mode and strength.
latencyFromMode :: String -> Number -> String
latencyFromMode modeId strength
  | modeId == "none" = "zero"
  | modeId == "pulled-string" = "high"
  | modeId == "one-euro" = "adaptive"
  | strength >= 70.0 = "high"
  | strength >= 40.0 = "medium"
  | true = "low"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // debug utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate debug info string for SmoothingConfig.
smoothingConfigDebugInfo :: SmoothingConfig -> String
smoothingConfigDebugInfo c =
  "(SmoothingConfig { " <>
  "mode: " <> smoothingModeToId c.mode <> ", " <>
  "strength: " <> show (unwrapSmoothingStrength c.strength) <> "%, " <>
  "string: " <> show (unwrapStringLength c.stringLength) <> "px, " <>
  "window: " <> show (unwrapWindowSize c.windowSize) <> ", " <>
  "catchUp: " <> showBool c.catchUp <> " @" <>
    show (unwrapCatchUpSpeed c.catchUpSpeed) <>
  " })"
  where
    showBool :: Boolean -> String
    showBool b = if b then "on" else "off"

-- | Combine a label with its smoothing config debug info.
showWithConfig :: String -> SmoothingConfig -> String
showWithConfig label config =
  label <> ": " <> smoothingConfigDebugInfo config
