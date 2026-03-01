-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // motion // timeremap
--                                                               // construction
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Construction functions for time remapping.
-- |
-- | ## Contents
-- |
-- | - Basic constructors (identity, uniformSpeed, reverse, freezeAt)
-- | - Time stretch
-- | - Speed ramps (speedRamp, speedRampIn, speedRampOut, speedRampInOut)
-- | - Keyframe-based construction
-- |
-- | ## Dependencies
-- |
-- | - Types: TimeRemap, SpeedKeyframe, RemapMode
-- | - Internal: sortKeyframes, epsilon
-- | - Easing: easeIn, easeOut, easeInOut

module Hydrogen.Schema.Motion.TimeRemap.Construction
  ( -- * Basic Construction
    identity
  , uniformSpeed
  , reverse
  , freezeAt
  , timeStretch
  
  -- * Speed Ramps
  , speedRamp
  , speedRampIn
  , speedRampOut
  , speedRampInOut
  
  -- * Keyframe-Based
  , fromSpeedKeyframes
  , addSpeedKeyframe
  , removeSpeedKeyframe
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (+)
  , (/)
  , (<)
  , (/=)
  , negate
  )

import Data.Array (snoc, filter)

import Hydrogen.Schema.Motion.Easing (Easing, easeIn, easeOut, easeInOut)
import Hydrogen.Schema.Motion.TimeRemap.Types 
  ( TimeRemap(TimeRemap)
  , SpeedKeyframe(SpeedKeyframe)
  , RemapMode(LinearRemap, FreezeRemap, CurveRemap, KeyframeRemap)
  )
import Hydrogen.Schema.Motion.TimeRemap.Internal (sortKeyframes, epsilon)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // basic construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Identity remap (no change).
identity :: Number -> TimeRemap
identity dur = TimeRemap
  { mode: LinearRemap
  , speedFactor: 1.0
  , startSpeed: 1.0
  , endSpeed: 1.0
  , originalDuration: dur
  , keyframes: []
  }

-- | Uniform speed change.
-- |
-- | speed = 0.5 is slow motion, 2.0 is fast forward.
uniformSpeed :: Number -> Number -> TimeRemap
uniformSpeed speed dur = TimeRemap
  { mode: LinearRemap
  , speedFactor: speed
  , startSpeed: speed
  , endSpeed: speed
  , originalDuration: dur
  , keyframes: []
  }

-- | Reverse playback.
reverse :: Number -> TimeRemap
reverse dur = TimeRemap
  { mode: LinearRemap
  , speedFactor: negate 1.0
  , startSpeed: negate 1.0
  , endSpeed: negate 1.0
  , originalDuration: dur
  , keyframes: []
  }

-- | Freeze at specific frame.
freezeAt :: Number -> Number -> TimeRemap
freezeAt freezeFrame dur = TimeRemap
  { mode: FreezeRemap freezeFrame
  , speedFactor: 0.0
  , startSpeed: 0.0
  , endSpeed: 0.0
  , originalDuration: dur
  , keyframes: []
  }

-- | Time stretch (uniform speed to achieve target duration).
-- |
-- | targetDuration: how long you want the animation to last.
timeStretch :: Number -> Number -> TimeRemap
timeStretch targetDuration originalDur =
  let speed = if targetDuration < epsilon then 1.0 else originalDur / targetDuration
  in uniformSpeed speed originalDur

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // speed ramps
-- ═════════════════════════════════════════════════════════════════════════════

-- | Speed ramp with custom easing.
-- |
-- | Transitions from startSpeed to endSpeed following the easing curve.
speedRamp :: Easing -> Number -> Number -> Number -> TimeRemap
speedRamp eas startSpd endSpd dur = TimeRemap
  { mode: CurveRemap eas
  , speedFactor: (startSpd + endSpd) / 2.0  -- Average for reference
  , startSpeed: startSpd
  , endSpeed: endSpd
  , originalDuration: dur
  , keyframes: []
  }

-- | Speed ramp in (slow start).
speedRampIn :: Number -> Number -> Number -> TimeRemap
speedRampIn startSpd endSpd = speedRamp easeIn startSpd endSpd

-- | Speed ramp out (slow end).
speedRampOut :: Number -> Number -> Number -> TimeRemap
speedRampOut startSpd endSpd = speedRamp easeOut startSpd endSpd

-- | Speed ramp in-out (slow start and end).
speedRampInOut :: Number -> Number -> Number -> TimeRemap
speedRampInOut startSpd endSpd = speedRamp easeInOut startSpd endSpd

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // keyframe-based
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create time remap from array of speed keyframes.
fromSpeedKeyframes :: Array SpeedKeyframe -> Number -> TimeRemap
fromSpeedKeyframes kfs dur = TimeRemap
  { mode: KeyframeRemap
  , speedFactor: 1.0
  , startSpeed: 1.0
  , endSpeed: 1.0
  , originalDuration: dur
  , keyframes: sortKeyframes kfs
  }

-- | Add a speed keyframe.
addSpeedKeyframe :: SpeedKeyframe -> TimeRemap -> TimeRemap
addSpeedKeyframe kf (TimeRemap tr) = TimeRemap
  (tr { keyframes = sortKeyframes (snoc tr.keyframes kf), mode = KeyframeRemap })

-- | Remove speed keyframe at frame.
removeSpeedKeyframe :: Number -> TimeRemap -> TimeRemap
removeSpeedKeyframe frame (TimeRemap tr) = TimeRemap
  (tr { keyframes = filter (\(SpeedKeyframe k) -> k.frame /= frame) tr.keyframes })
