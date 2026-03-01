-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // schema // brush // smoothing // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Smoothing Types — ADTs for stroke smoothing and stabilization.
-- |
-- | ## Design Philosophy
-- |
-- | Stroke smoothing reduces input jitter for cleaner lines. Different
-- | algorithms trade off between latency and smoothness. The SmoothingMode
-- | enum provides industry-standard approaches from raw input to adaptive
-- | filtering.
-- |
-- | ## Smoothing Modes
-- |
-- | - **NoSmoothing**: Raw input, zero latency
-- | - **BasicSmoothing**: Simple moving average
-- | - **PulledString**: Lazy cursor follows at a distance
-- | - **MovingAverage**: Weighted average over window
-- | - **ExponentialSmoothing**: Exponential decay weighting
-- | - **OneEuroFilter**: Adaptive filter (smooth when slow, responsive when fast)
-- |
-- | ## Dependencies
-- |
-- | - Prelude

module Hydrogen.Schema.Brush.Smoothing.Types
  ( -- * SmoothingMode ADT
    SmoothingMode
      ( NoSmoothing
      , BasicSmoothing
      , PulledString
      , MovingAverage
      , ExponentialSmoothing
      , OneEuroFilter
      )
  , allSmoothingModes
  , smoothingModeDescription
  , smoothingModeLatency
  , isAdaptiveMode
  , requiresHistory
  
  -- * Debug & Serialization Helpers
  , smoothingModeDebugInfo
  , smoothingModeToId
  , sameSmoothingModeKind
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (<>)
  , (==)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // smoothing mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Smoothing algorithm for stroke input.
-- |
-- | Different algorithms provide varying trade-offs between
-- | responsiveness (low latency) and smoothness (clean lines).
data SmoothingMode
  = NoSmoothing          -- ^ Raw input, no processing, lowest latency
  | BasicSmoothing       -- ^ Simple average of recent points
  | PulledString         -- ^ Lazy cursor follows at fixed distance
  | MovingAverage        -- ^ Weighted average over sample window
  | ExponentialSmoothing -- ^ Exponentially decaying weights
  | OneEuroFilter        -- ^ Adaptive: smooth when slow, responsive when fast

derive instance eqSmoothingMode :: Eq SmoothingMode
derive instance ordSmoothingMode :: Ord SmoothingMode

instance showSmoothingMode :: Show SmoothingMode where
  show NoSmoothing = "(SmoothingMode NoSmoothing)"
  show BasicSmoothing = "(SmoothingMode BasicSmoothing)"
  show PulledString = "(SmoothingMode PulledString)"
  show MovingAverage = "(SmoothingMode MovingAverage)"
  show ExponentialSmoothing = "(SmoothingMode ExponentialSmoothing)"
  show OneEuroFilter = "(SmoothingMode OneEuroFilter)"

-- | All smoothing mode variants.
allSmoothingModes :: Array SmoothingMode
allSmoothingModes =
  [ NoSmoothing
  , BasicSmoothing
  , PulledString
  , MovingAverage
  , ExponentialSmoothing
  , OneEuroFilter
  ]

-- | Human-readable description of each smoothing mode.
smoothingModeDescription :: SmoothingMode -> String
smoothingModeDescription NoSmoothing =
  "Raw input with no processing, lowest possible latency"
smoothingModeDescription BasicSmoothing =
  "Simple average of recent input points"
smoothingModeDescription PulledString =
  "Lazy cursor follows input at a fixed distance (stabilizer)"
smoothingModeDescription MovingAverage =
  "Weighted average over a sliding window of samples"
smoothingModeDescription ExponentialSmoothing =
  "Exponentially decaying weights favor recent input"
smoothingModeDescription OneEuroFilter =
  "Adaptive filter: smooth when slow, responsive when fast"

-- | Relative latency of each smoothing mode.
-- |
-- | Returns a qualitative latency descriptor for UI display.
smoothingModeLatency :: SmoothingMode -> String
smoothingModeLatency NoSmoothing = "zero"
smoothingModeLatency BasicSmoothing = "low"
smoothingModeLatency PulledString = "high"
smoothingModeLatency MovingAverage = "medium"
smoothingModeLatency ExponentialSmoothing = "low"
smoothingModeLatency OneEuroFilter = "adaptive"

-- | Check if mode adapts to input speed.
isAdaptiveMode :: SmoothingMode -> Boolean
isAdaptiveMode OneEuroFilter = true
isAdaptiveMode _ = false

-- | Check if mode requires sample history.
-- |
-- | Modes that need history must maintain a buffer of past points.
requiresHistory :: SmoothingMode -> Boolean
requiresHistory NoSmoothing = false
requiresHistory BasicSmoothing = true
requiresHistory PulledString = false
requiresHistory MovingAverage = true
requiresHistory ExponentialSmoothing = true
requiresHistory OneEuroFilter = true

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // debug helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate debug info for smoothing mode.
smoothingModeDebugInfo :: SmoothingMode -> String
smoothingModeDebugInfo mode =
  "SmoothingMode: " <> smoothingModeToId mode <>
  " — " <> smoothingModeDescription mode

-- | Convert smoothing mode to string ID.
smoothingModeToId :: SmoothingMode -> String
smoothingModeToId NoSmoothing = "none"
smoothingModeToId BasicSmoothing = "basic"
smoothingModeToId PulledString = "pulled-string"
smoothingModeToId MovingAverage = "moving-average"
smoothingModeToId ExponentialSmoothing = "exponential"
smoothingModeToId OneEuroFilter = "one-euro"

-- | Check if two smoothing modes are the same kind.
sameSmoothingModeKind :: SmoothingMode -> SmoothingMode -> Boolean
sameSmoothingModeKind a b = smoothingModeToId a == smoothingModeToId b
