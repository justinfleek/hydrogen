-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // motion // timeremap
--                                                                // composition
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Composition, presets, and analysis for time remapping.
-- |
-- | ## Contents
-- |
-- | - Composition (compose, chain, blend)
-- | - Presets (slowMotion, fastForward, pingPong, loop, hold, bounce)
-- | - Analysis (averageSpeed, minSpeed, maxSpeed, isConstantSpeed)
-- | - Sampling (sampleRemap, sampleSpeed)
-- |
-- | ## Dependencies
-- |
-- | - Types: TimeRemap, SpeedKeyframe, RemapMode
-- | - Construction: identity, uniformSpeed, speedRampInOut
-- | - Evaluation: apply, speedAt
-- | - Internal: clamp01, epsilon, infinity, buildArray

module Hydrogen.Schema.Motion.TimeRemap.Composition
  ( -- * Composition
    compose
  , chain
  , blend
  
  -- * Presets
  , slowMotion
  , fastForward
  , pingPong
  , loop
  , hold
  , bounce
  
  -- * Analysis
  , averageSpeed
  , minSpeed
  , maxSpeed
  , isConstantSpeed
  
  -- * Sampling
  , sampleRemap
  , sampleSpeed
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
  , (<=)
  , (==)
  , map
  , min
  , max
  )

import Data.Array (length, foldl)
import Data.Maybe (Maybe(..))
import Data.Number (abs)
import Data.Int (toNumber) as Int

import Hydrogen.Schema.Motion.TimeRemap.Types 
  ( TimeRemap(TimeRemap)
  , SpeedKeyframe(SpeedKeyframe)
  , RemapMode(LinearRemap, CurveRemap, KeyframeRemap, FreezeRemap, PingPongRemap, LoopRemap)
  )
import Hydrogen.Schema.Motion.TimeRemap.Construction 
  ( uniformSpeed
  , speedRampInOut
  )
import Hydrogen.Schema.Motion.TimeRemap.Evaluation 
  ( apply
  , speedAt
  )
import Hydrogen.Schema.Motion.TimeRemap.Internal 
  ( clamp01
  , clampSpeed
  , epsilon
  , infinity
  , buildArray
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // composition
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compose two remaps (apply first, then second).
-- |
-- | **BOUNDED**: All speed values are clamped after multiplication to prevent
-- | exponential compounding at billion-agent scale. Without this, repeated
-- | composition could overflow numeric bounds.
compose :: TimeRemap -> TimeRemap -> TimeRemap
compose first second =
  -- Multiply speed factors with clamping for swarm safety
  let (TimeRemap f) = first
      (TimeRemap s) = second
  in TimeRemap
    { mode: LinearRemap
    , speedFactor: clampSpeed (f.speedFactor * s.speedFactor)
    , startSpeed: clampSpeed (f.startSpeed * s.startSpeed)
    , endSpeed: clampSpeed (f.endSpeed * s.endSpeed)
    , originalDuration: f.originalDuration
    , keyframes: []
    }

-- | Chain remaps (first plays, then second).
chain :: TimeRemap -> TimeRemap -> TimeRemap
chain first second =
  let (TimeRemap f) = first
      (TimeRemap s) = second
  in TimeRemap
    { mode: f.mode  -- Keep first's mode
    , speedFactor: f.speedFactor
    , startSpeed: f.startSpeed
    , endSpeed: f.endSpeed
    , originalDuration: f.originalDuration + s.originalDuration
    , keyframes: f.keyframes
    }

-- | Blend two remaps with weight.
-- |
-- | weight = 0.0 gives first, weight = 1.0 gives second.
blend :: Number -> TimeRemap -> TimeRemap -> TimeRemap
blend weight first second =
  let 
    w = clamp01 weight
    mw = 1.0 - w
    (TimeRemap f) = first
    (TimeRemap s) = second
  in TimeRemap
    { mode: LinearRemap
    , speedFactor: mw * f.speedFactor + w * s.speedFactor
    , startSpeed: mw * f.startSpeed + w * s.startSpeed
    , endSpeed: mw * f.endSpeed + w * s.endSpeed
    , originalDuration: f.originalDuration
    , keyframes: []
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Slow motion preset (50% speed).
slowMotion :: Number -> TimeRemap
slowMotion = uniformSpeed 0.5

-- | Fast forward preset (2x speed).
fastForward :: Number -> TimeRemap
fastForward = uniformSpeed 2.0

-- | Ping-pong preset (forward then reverse).
pingPong :: Number -> TimeRemap
pingPong dur = TimeRemap
  { mode: PingPongRemap
  , speedFactor: 1.0
  , startSpeed: 1.0
  , endSpeed: 1.0
  , originalDuration: dur
  , keyframes: []
  }

-- | Loop preset.
loop :: Number -> Number -> TimeRemap
loop loopLen dur = TimeRemap
  { mode: LoopRemap loopLen
  , speedFactor: 1.0
  , startSpeed: 1.0
  , endSpeed: 1.0
  , originalDuration: dur
  , keyframes: []
  }

-- | Hold preset (freeze at end).
hold :: Number -> TimeRemap
hold dur = TimeRemap
  { mode: FreezeRemap dur
  , speedFactor: 0.0
  , startSpeed: 0.0
  , endSpeed: 0.0
  , originalDuration: dur
  , keyframes: []
  }

-- | Bounce preset (ease in-out with brief hold at extremes).
bounce :: Number -> TimeRemap
bounce dur = speedRampInOut 0.0 2.0 dur

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // analysis
-- ═════════════════════════════════════════════════════════════════════════════

-- | Average speed over duration.
averageSpeed :: TimeRemap -> Number
averageSpeed (TimeRemap tr) = case tr.mode of
  FreezeRemap _ -> 0.0
  PingPongRemap -> 1.0
  LoopRemap _ -> 1.0
  LinearRemap -> abs tr.speedFactor
  CurveRemap _ -> (abs tr.startSpeed + abs tr.endSpeed) / 2.0
  KeyframeRemap ->
    let speeds = map (\(SpeedKeyframe k) -> abs k.speed) tr.keyframes
        n = length speeds
    in if n == 0 then 1.0 else foldl (+) 0.0 speeds / Int.toNumber n

-- | Minimum speed in remap.
minSpeed :: TimeRemap -> Number
minSpeed (TimeRemap tr) = case tr.mode of
  FreezeRemap _ -> 0.0
  PingPongRemap -> 1.0
  LoopRemap _ -> 1.0
  LinearRemap -> abs tr.speedFactor
  CurveRemap _ -> min (abs tr.startSpeed) (abs tr.endSpeed)
  KeyframeRemap -> 
    foldl (\acc (SpeedKeyframe k) -> min acc (abs k.speed)) infinity tr.keyframes

-- | Maximum speed in remap.
maxSpeed :: TimeRemap -> Number
maxSpeed (TimeRemap tr) = case tr.mode of
  FreezeRemap _ -> 0.0
  PingPongRemap -> 1.0
  LoopRemap _ -> 1.0
  LinearRemap -> abs tr.speedFactor
  CurveRemap _ -> max (abs tr.startSpeed) (abs tr.endSpeed)
  KeyframeRemap ->
    foldl (\acc (SpeedKeyframe k) -> max acc (abs k.speed)) 0.0 tr.keyframes

-- | Check if speed is constant.
isConstantSpeed :: TimeRemap -> Boolean
isConstantSpeed (TimeRemap tr) = case tr.mode of
  FreezeRemap _ -> true
  LinearRemap -> true
  LoopRemap _ -> true
  PingPongRemap -> false
  CurveRemap _ -> abs (tr.startSpeed - tr.endSpeed) < epsilon
  KeyframeRemap -> length tr.keyframes <= 1

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // sampling
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sample remap at n evenly-spaced frames.
sampleRemap :: Int -> TimeRemap -> Array Number
sampleRemap n remap =
  let (TimeRemap tr) = remap
  in buildArray (n + 1) (\i ->
       let frame = Int.toNumber i / Int.toNumber n * tr.originalDuration
       in Just (apply frame remap)
     )

-- | Sample speed at n evenly-spaced frames.
sampleSpeed :: Int -> TimeRemap -> Array Number
sampleSpeed n remap =
  let (TimeRemap tr) = remap
  in buildArray (n + 1) (\i ->
       let frame = Int.toNumber i / Int.toNumber n * tr.originalDuration
       in Just (speedAt frame remap)
     )
