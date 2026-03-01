-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // motion // timeremap
--                                                                  // utilities
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Utility functions for time remapping.
-- |
-- | ## Contents
-- |
-- | - Validation (isValidRemap)
-- | - Normalization (normalizeRemap)
-- | - Keyframe helpers (speedKeyframe)
-- | - Combination (combineRemaps)
-- | - Speed utilities (speedMagnitude)
-- | - Predicates (hasSpeedChange)
-- |
-- | ## Dependencies
-- |
-- | - Types: TimeRemap, SpeedKeyframe, RemapMode
-- | - Construction: identity
-- | - Composition: averageSpeed
-- | - Internal: epsilon, infinity

module Hydrogen.Schema.Motion.TimeRemap.Utilities
  ( -- * Constants
    defaultSpeed
  
  -- * Validation
  , isValidRemap
  
  -- * Normalization
  , normalizeRemap
  
  -- * Keyframe Helpers
  , speedKeyframe
  
  -- * Combination
  , combineRemaps
  
  -- * Speed Utilities
  , speedMagnitude
  
  -- * Predicates
  , hasSpeedChange
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (==)
  , (&&)
  , (||)
  , map
  , max
  )

import Data.Array (length, index, foldl)
import Data.Maybe (fromMaybe)
import Data.Number (sqrt, abs)
import Data.Int (toNumber) as Int

import Hydrogen.Schema.Motion.Easing (linear)
import Hydrogen.Schema.Motion.TimeRemap.Types 
  ( TimeRemap(TimeRemap)
  , SpeedKeyframe(SpeedKeyframe)
  , RemapMode(LinearRemap, CurveRemap, KeyframeRemap, FreezeRemap, PingPongRemap, LoopRemap)
  )
import Hydrogen.Schema.Motion.TimeRemap.Construction (identity)
import Hydrogen.Schema.Motion.TimeRemap.Composition (averageSpeed)
import Hydrogen.Schema.Motion.TimeRemap.Internal (epsilon, infinity)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default speed (normal playback).
defaultSpeed :: Number
defaultSpeed = 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if time remap is valid.
-- |
-- | A remap is valid if duration is positive and speeds are reasonable.
isValidRemap :: TimeRemap -> Boolean
isValidRemap (TimeRemap tr) =
  tr.originalDuration > 0.0 &&
  abs tr.speedFactor < infinity &&
  abs tr.startSpeed < infinity &&
  abs tr.endSpeed < infinity

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // normalization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Normalize remap to have average speed of 1.0.
normalizeRemap :: TimeRemap -> TimeRemap
normalizeRemap remap =
  let 
    avg = averageSpeed remap
    (TimeRemap tr) = remap
    scaleFactor = if avg < epsilon then 1.0 else 1.0 / avg
  in TimeRemap
    { mode: tr.mode
    , speedFactor: tr.speedFactor * scaleFactor
    , startSpeed: tr.startSpeed * scaleFactor
    , endSpeed: tr.endSpeed * scaleFactor
    , originalDuration: tr.originalDuration
    , keyframes: map (\(SpeedKeyframe k) -> 
        SpeedKeyframe (k { speed = k.speed * scaleFactor })) tr.keyframes
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // keyframe helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a speed keyframe with linear easing.
speedKeyframe :: Number -> Number -> SpeedKeyframe
speedKeyframe frame spd = SpeedKeyframe
  { frame: frame
  , speed: spd
  , easing: linear
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // combination
-- ═════════════════════════════════════════════════════════════════════════════

-- | Combine multiple remaps by averaging their effects.
combineRemaps :: Array TimeRemap -> TimeRemap
combineRemaps remaps =
  let 
    n = length remaps
    nNum = Int.toNumber n
  in
    if n == 0 then identity 100.0
    else if n == 1 then fromMaybe (identity 100.0) (index remaps 0)
    else
      let
        sumSpeeds = foldl (\acc (TimeRemap tr) -> 
          { start: acc.start + tr.startSpeed
          , end: acc.end + tr.endSpeed
          , factor: acc.factor + tr.speedFactor
          , dur: max acc.dur tr.originalDuration
          }) { start: 0.0, end: 0.0, factor: 0.0, dur: 0.0 } remaps
      in TimeRemap
        { mode: LinearRemap
        , speedFactor: sumSpeeds.factor / nNum
        , startSpeed: sumSpeeds.start / nNum
        , endSpeed: sumSpeeds.end / nNum
        , originalDuration: sumSpeeds.dur
        , keyframes: []
        }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // speed utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Square root for speed calculations (2D speed vector magnitude).
speedMagnitude :: Number -> Number -> Number
speedMagnitude sx sy = sqrt (sx * sx + sy * sy)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if remap has any speed change (not identity).
hasSpeedChange :: TimeRemap -> Boolean
hasSpeedChange (TimeRemap tr) = case tr.mode of
  FreezeRemap _ -> true
  PingPongRemap -> true
  LoopRemap _ -> false  -- Speed is constant in loop
  LinearRemap -> abs (tr.speedFactor - 1.0) > epsilon || tr.speedFactor < 0.0
  CurveRemap _ -> abs (tr.startSpeed - 1.0) > epsilon || abs (tr.endSpeed - 1.0) > epsilon
  KeyframeRemap -> length tr.keyframes > 0
