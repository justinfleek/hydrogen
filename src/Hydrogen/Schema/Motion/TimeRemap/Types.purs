-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // motion // timeremap
--                                                                      // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core types for time remapping.
-- |
-- | ## Types
-- |
-- | - `RemapMode`: Mode of time remapping (linear, curve, keyframe, etc.)
-- | - `SpeedKeyframe`: Keyframe for variable speed control
-- | - `TimeRemap`: Complete time remap configuration
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Motion.Easing (Easing type)

module Hydrogen.Schema.Motion.TimeRemap.Types
  ( -- * Types
    RemapMode(LinearRemap, CurveRemap, KeyframeRemap, FreezeRemap, PingPongRemap, LoopRemap)
  , SpeedKeyframe(SpeedKeyframe)
  , TimeRemap(TimeRemap)
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Hydrogen.Schema.Motion.Easing (Easing)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // remap mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mode of time remapping.
data RemapMode
  = LinearRemap              -- Constant speed factor
  | CurveRemap Easing        -- Speed follows easing curve
  | KeyframeRemap            -- Speed defined by keyframes
  | FreezeRemap Number       -- Frozen at specific time
  | PingPongRemap            -- Forward then backward
  | LoopRemap Number         -- Loop every n frames

derive instance eqRemapMode :: Eq RemapMode

instance showRemapMode :: Show RemapMode where
  show LinearRemap = "LinearRemap"
  show (CurveRemap _) = "CurveRemap"
  show KeyframeRemap = "KeyframeRemap"
  show (FreezeRemap t) = "(FreezeRemap " <> show t <> ")"
  show PingPongRemap = "PingPongRemap"
  show (LoopRemap n) = "(LoopRemap " <> show n <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // speed keyframe
-- ═════════════════════════════════════════════════════════════════════════════

-- | Speed keyframe for variable speed control.
-- |
-- | speed = 1.0 is normal, 0.5 is half speed, 2.0 is double, 0.0 is freeze.
newtype SpeedKeyframe = SpeedKeyframe
  { frame :: Number
  , speed :: Number
  , easing :: Easing  -- Transition to next keyframe
  }

derive instance eqSpeedKeyframe :: Eq SpeedKeyframe

instance showSpeedKeyframe :: Show SpeedKeyframe where
  show (SpeedKeyframe kf) = "(SpeedKeyframe frame:" <> show kf.frame 
    <> " speed:" <> show kf.speed <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // time remap
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete time remap configuration.
newtype TimeRemap = TimeRemap
  { mode :: RemapMode
  , speedFactor :: Number           -- Base speed multiplier
  , startSpeed :: Number            -- Speed at start (for ramps)
  , endSpeed :: Number              -- Speed at end (for ramps)
  , originalDuration :: Number      -- Duration of source material (frames)
  , keyframes :: Array SpeedKeyframe
  }

derive instance eqTimeRemap :: Eq TimeRemap

instance showTimeRemap :: Show TimeRemap where
  show (TimeRemap tr) = "(TimeRemap mode:" <> show tr.mode 
    <> " speed:" <> show tr.speedFactor <> ")"
