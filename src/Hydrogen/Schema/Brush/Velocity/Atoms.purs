-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // schema // brush // velocity // atoms
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Velocity Atoms — Bounded numeric parameters for velocity dynamics.
-- |
-- | ## Design Philosophy
-- |
-- | Velocity describes stroke speed and its effect on brush behavior.
-- | Two representations are supported:
-- |
-- | 1. **Normalized (Velocity)**: 0-1 range for parameter mapping
-- | 2. **Raw (VelocityRaw)**: Pixels per second for calculations
-- |
-- | Thresholds (VelocityMin, VelocityMax) define the range of speeds
-- | that map to the 0-1 normalized range.
-- |
-- | ## Key Properties
-- |
-- | - **Velocity**: Normalized speed (0=still, 1=max speed, clamps)
-- | - **VelocityRaw**: Pixels per second (0-10000, clamps)
-- | - **VelocityMin**: Lower threshold for normalization (0-1, clamps)
-- | - **VelocityMax**: Upper threshold for normalization (0-1, clamps)
-- | - **SmoothingWindow**: Samples to average for smoothing (1-10, clamps)
-- |
-- | ## Dependencies
-- |
-- | - Prelude
-- | - Schema.Bounded

module Hydrogen.Schema.Brush.Velocity.Atoms
  ( -- * Velocity (0 to 1)
    Velocity(Velocity)
  , velocity
  , velocityBounds
  , unwrapVelocity
  , noVelocity
  , halfVelocity
  , fullVelocity
  , velocityDebugInfo
  
  -- * VelocityRaw (0 to 10000 pixels/second)
  , VelocityRaw(VelocityRaw)
  , velocityRaw
  , velocityRawBounds
  , unwrapVelocityRaw
  , stillVelocityRaw
  , slowVelocityRaw
  , mediumVelocityRaw
  , fastVelocityRaw
  , velocityRawDebugInfo
  
  -- * VelocityMin (0 to 1)
  , VelocityMin(VelocityMin)
  , velocityMin
  , velocityMinBounds
  , unwrapVelocityMin
  , defaultVelocityMin
  , velocityMinDebugInfo
  
  -- * VelocityMax (0 to 1)
  , VelocityMax(VelocityMax)
  , velocityMax
  , velocityMaxBounds
  , unwrapVelocityMax
  , defaultVelocityMax
  , velocityMaxDebugInfo
  
  -- * SmoothingWindow (1 to 10)
  , SmoothingWindow(SmoothingWindow)
  , smoothingWindow
  , smoothingWindowBounds
  , unwrapSmoothingWindow
  , noSmoothing
  , lightSmoothing
  , heavySmoothing
  , smoothingWindowDebugInfo
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
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // velocity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Normalized velocity (0 to 1).
-- | 0 = no movement (still)
-- | 1 = maximum speed
-- |
-- | This is the value used for parameter mapping after normalization
-- | from raw pixel-per-second values.
newtype Velocity = Velocity Number

derive instance eqVelocity :: Eq Velocity
derive instance ordVelocity :: Ord Velocity

instance showVelocity :: Show Velocity where
  show (Velocity v) = "(Velocity " <> show v <> ")"

-- | Bounded specification for Velocity.
velocityBounds :: Bounded.NumberBounds
velocityBounds = Bounded.numberBounds 0.0 1.0 Bounded.Clamps
  "velocity" "Normalized stroke velocity (0=still, 1=max)"

-- | Create a Velocity value (clamped to 0-1).
velocity :: Number -> Velocity
velocity n = Velocity (Bounded.clampNumber 0.0 1.0 n)

-- | Extract the raw Velocity value.
unwrapVelocity :: Velocity -> Number
unwrapVelocity (Velocity v) = v

-- | No movement (0).
noVelocity :: Velocity
noVelocity = Velocity 0.0

-- | Half speed (0.5).
halfVelocity :: Velocity
halfVelocity = Velocity 0.5

-- | Maximum speed (1).
fullVelocity :: Velocity
fullVelocity = Velocity 1.0

-- | Debug info string for Velocity.
velocityDebugInfo :: Velocity -> String
velocityDebugInfo v = show v <> " raw:" <> show (unwrapVelocity v)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // velocity raw
-- ═════════════════════════════════════════════════════════════════════════════

-- | Raw velocity in pixels per second (0 to 10000).
-- |
-- | This is the direct measurement from input events before normalization.
-- | Used for calculations and debugging; parameter mapping uses Velocity.
newtype VelocityRaw = VelocityRaw Number

derive instance eqVelocityRaw :: Eq VelocityRaw
derive instance ordVelocityRaw :: Ord VelocityRaw

instance showVelocityRaw :: Show VelocityRaw where
  show (VelocityRaw v) = "(VelocityRaw " <> show v <> "px/s)"

-- | Bounded specification for VelocityRaw.
velocityRawBounds :: Bounded.NumberBounds
velocityRawBounds = Bounded.numberBounds 0.0 10000.0 Bounded.Clamps
  "velocityRaw" "Raw stroke velocity in pixels per second (0-10000)"

-- | Create a VelocityRaw value (clamped to 0-10000).
velocityRaw :: Number -> VelocityRaw
velocityRaw n = VelocityRaw (Bounded.clampNumber 0.0 10000.0 n)

-- | Extract the raw VelocityRaw value.
unwrapVelocityRaw :: VelocityRaw -> Number
unwrapVelocityRaw (VelocityRaw v) = v

-- | No movement (0 px/s).
stillVelocityRaw :: VelocityRaw
stillVelocityRaw = VelocityRaw 0.0

-- | Slow movement (100 px/s).
slowVelocityRaw :: VelocityRaw
slowVelocityRaw = VelocityRaw 100.0

-- | Medium movement (500 px/s).
mediumVelocityRaw :: VelocityRaw
mediumVelocityRaw = VelocityRaw 500.0

-- | Fast movement (2000 px/s).
fastVelocityRaw :: VelocityRaw
fastVelocityRaw = VelocityRaw 2000.0

-- | Debug info string for VelocityRaw.
velocityRawDebugInfo :: VelocityRaw -> String
velocityRawDebugInfo v = show v <> " raw:" <> show (unwrapVelocityRaw v)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // velocity min
-- ═════════════════════════════════════════════════════════════════════════════

-- | Minimum velocity threshold (0 to 1).
-- |
-- | Speeds below this threshold are treated as 0 in the normalized range.
-- | This allows filtering out very slow movements.
newtype VelocityMin = VelocityMin Number

derive instance eqVelocityMin :: Eq VelocityMin
derive instance ordVelocityMin :: Ord VelocityMin

instance showVelocityMin :: Show VelocityMin where
  show (VelocityMin v) = "(VelocityMin " <> show v <> ")"

-- | Bounded specification for VelocityMin.
velocityMinBounds :: Bounded.NumberBounds
velocityMinBounds = Bounded.numberBounds 0.0 1.0 Bounded.Clamps
  "velocityMin" "Minimum velocity threshold (0-1)"

-- | Create a VelocityMin value (clamped to 0-1).
velocityMin :: Number -> VelocityMin
velocityMin n = VelocityMin (Bounded.clampNumber 0.0 1.0 n)

-- | Extract the raw VelocityMin value.
unwrapVelocityMin :: VelocityMin -> Number
unwrapVelocityMin (VelocityMin v) = v

-- | Default minimum threshold (0, no filtering).
defaultVelocityMin :: VelocityMin
defaultVelocityMin = VelocityMin 0.0

-- | Debug info string for VelocityMin.
velocityMinDebugInfo :: VelocityMin -> String
velocityMinDebugInfo v = show v <> " raw:" <> show (unwrapVelocityMin v)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // velocity max
-- ═════════════════════════════════════════════════════════════════════════════

-- | Maximum velocity threshold (0 to 1).
-- |
-- | Speeds above this threshold are treated as 1 in the normalized range.
-- | This allows capping very fast movements.
newtype VelocityMax = VelocityMax Number

derive instance eqVelocityMax :: Eq VelocityMax
derive instance ordVelocityMax :: Ord VelocityMax

instance showVelocityMax :: Show VelocityMax where
  show (VelocityMax v) = "(VelocityMax " <> show v <> ")"

-- | Bounded specification for VelocityMax.
velocityMaxBounds :: Bounded.NumberBounds
velocityMaxBounds = Bounded.numberBounds 0.0 1.0 Bounded.Clamps
  "velocityMax" "Maximum velocity threshold (0-1)"

-- | Create a VelocityMax value (clamped to 0-1).
velocityMax :: Number -> VelocityMax
velocityMax n = VelocityMax (Bounded.clampNumber 0.0 1.0 n)

-- | Extract the raw VelocityMax value.
unwrapVelocityMax :: VelocityMax -> Number
unwrapVelocityMax (VelocityMax v) = v

-- | Default maximum threshold (1, no capping).
defaultVelocityMax :: VelocityMax
defaultVelocityMax = VelocityMax 1.0

-- | Debug info string for VelocityMax.
velocityMaxDebugInfo :: VelocityMax -> String
velocityMaxDebugInfo v = show v <> " raw:" <> show (unwrapVelocityMax v)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // smoothing window
-- ═════════════════════════════════════════════════════════════════════════════

-- | Smoothing window size (1 to 10 samples).
-- |
-- | Number of velocity samples to average for smoothing. Higher values
-- | produce smoother velocity curves but increase latency.
newtype SmoothingWindow = SmoothingWindow Int

derive instance eqSmoothingWindow :: Eq SmoothingWindow
derive instance ordSmoothingWindow :: Ord SmoothingWindow

instance showSmoothingWindow :: Show SmoothingWindow where
  show (SmoothingWindow w) = "(SmoothingWindow " <> show w <> ")"

-- | Bounded specification for SmoothingWindow.
smoothingWindowBounds :: Bounded.IntBounds
smoothingWindowBounds = Bounded.intBounds 1 10 Bounded.Clamps
  "smoothingWindow" "Velocity smoothing samples (1-10)"

-- | Create a SmoothingWindow value (clamped to 1-10).
smoothingWindow :: Int -> SmoothingWindow
smoothingWindow n = SmoothingWindow (Bounded.clampInt 1 10 n)

-- | Extract the raw SmoothingWindow value.
unwrapSmoothingWindow :: SmoothingWindow -> Int
unwrapSmoothingWindow (SmoothingWindow w) = w

-- | No smoothing (1 sample).
noSmoothing :: SmoothingWindow
noSmoothing = SmoothingWindow 1

-- | Light smoothing (3 samples).
lightSmoothing :: SmoothingWindow
lightSmoothing = SmoothingWindow 3

-- | Heavy smoothing (10 samples).
heavySmoothing :: SmoothingWindow
heavySmoothing = SmoothingWindow 10

-- | Debug info string for SmoothingWindow.
smoothingWindowDebugInfo :: SmoothingWindow -> String
smoothingWindowDebugInfo w = show w <> " raw:" <> show (unwrapSmoothingWindow w)
