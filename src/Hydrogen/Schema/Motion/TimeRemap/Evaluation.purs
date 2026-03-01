-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // motion // timeremap
--                                                                 // evaluation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Evaluation functions for time remapping.
-- |
-- | ## Contents
-- |
-- | - Core evaluation (apply, applyInverse, applyToProgress)
-- | - Speed evaluation (speedAt, derivativeAt)
-- | - Duration functions (remappedDuration, originalDuration, setOriginalDuration)
-- |
-- | ## Dependencies
-- |
-- | - Types: TimeRemap, SpeedKeyframe, RemapMode
-- | - Internal: clamp01, clampNumber, floorNum, floorInt, mod, epsilon
-- | - Internal: integrateSpeed, integrateKeyframes, speedAtKeyframes
-- | - Easing: evaluate

module Hydrogen.Schema.Motion.TimeRemap.Evaluation
  ( -- * Evaluation
    apply
  , applyInverse
  , applyToProgress
  , speedAt
  , derivativeAt
  
  -- * Duration
  , remappedDuration
  , originalDuration
  , setOriginalDuration
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
  , negate
  )

import Data.Number (abs)

import Hydrogen.Schema.Motion.Easing (Easing, evaluate) as E
import Hydrogen.Schema.Motion.TimeRemap.Types 
  ( TimeRemap(TimeRemap)
  , SpeedKeyframe
  , RemapMode(LinearRemap, CurveRemap, KeyframeRemap, FreezeRemap, PingPongRemap, LoopRemap)
  )
import Hydrogen.Schema.Motion.TimeRemap.Internal 
  ( clamp01
  , clampNumber
  , floorNum
  , floorInt
  , mod
  , epsilon
  , integrateSpeed
  , integrateKeyframes
  , speedAtKeyframes
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // evaluation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Apply time remap to input frame.
-- |
-- | Returns the output time (which frame of the source to display).
apply :: Number -> TimeRemap -> Number
apply inputFrame (TimeRemap tr) = case tr.mode of
  FreezeRemap freezeFrame -> freezeFrame
  
  PingPongRemap ->
    let 
      cycle = inputFrame / tr.originalDuration
      cycleInt = floorNum cycle
      frac = cycle - cycleInt
      isReverse = mod (floorInt cycleInt) 2 == 1
    in
      if isReverse then tr.originalDuration * (1.0 - frac)
      else tr.originalDuration * frac
  
  LoopRemap loopLen ->
    let normalizedFrame = inputFrame - loopLen * floorNum (inputFrame / loopLen)
    in clampNumber 0.0 tr.originalDuration normalizedFrame
  
  LinearRemap ->
    inputFrame * tr.speedFactor
  
  CurveRemap eas ->
    let
      -- Progress through animation
      progress = clamp01 (inputFrame / tr.originalDuration)
      -- Integrate speed to get position using trapezoidal approximation
    in
      integrateSpeed progress tr.startSpeed tr.endSpeed eas tr.originalDuration
  
  KeyframeRemap ->
    integrateKeyframes inputFrame tr.keyframes

-- | Apply inverse time remap: given output frame, find input frame.
-- |
-- | This is the inverse of `apply`: `applyInverse (apply x remap) remap ≈ x`
-- |
-- | **Limitations:**
-- | - FreezeRemap: Returns the freeze frame (not truly invertible)
-- | - KeyframeRemap: Uses linear approximation (may have error for complex curves)
-- | - CurveRemap: Uses Newton-Raphson iteration (may have numerical error)
-- |
-- | For modes where many inputs map to one output (freeze, loop), this returns
-- | a single representative input.
applyInverse :: Number -> TimeRemap -> Number
applyInverse outputFrame (TimeRemap tr) = case tr.mode of
  FreezeRemap _ -> 
    -- Not invertible: any input maps to freezeFrame
    -- Return 0 as representative input
    0.0
  
  LinearRemap ->
    -- output = input * speed → input = output / speed
    if abs tr.speedFactor < epsilon then 0.0
    else outputFrame / tr.speedFactor
  
  PingPongRemap ->
    -- Forward: output = progress * duration
    -- Reverse: output = (1 - progress) * duration
    -- Invert by determining which phase and inverting
    let normalizedOutput = outputFrame / tr.originalDuration
    in if normalizedOutput <= 1.0
       then outputFrame  -- Forward phase: input = output
       else tr.originalDuration * 2.0 - outputFrame  -- Reverse phase
  
  LoopRemap _ ->
    -- output = input mod loopLen
    -- Inverse: just return the output (within one loop)
    outputFrame
  
  CurveRemap eas ->
    -- Use Newton-Raphson to solve: apply(x) = outputFrame
    invertCurveRemap outputFrame tr.startSpeed tr.endSpeed eas tr.originalDuration
  
  KeyframeRemap ->
    -- Approximate inverse using binary search
    invertKeyframeRemap outputFrame tr.keyframes tr.originalDuration

-- | Invert curve remap using Newton-Raphson iteration.
-- |
-- | Solves: integrateSpeed(x) = target for x
invertCurveRemap :: Number -> Number -> Number -> E.Easing -> Number -> Number
invertCurveRemap target startSpd endSpd eas dur =
  let
    -- Initial guess: assume average speed
    avgSpeed = (startSpd + endSpd) / 2.0
    initialGuess = if abs avgSpeed < epsilon then 0.0 else target / avgSpeed
    
    -- Newton-Raphson iteration
    iterate :: Int -> Number -> Number
    iterate 0 x = x
    iterate n x =
      let
        progress = clamp01 (x / dur)
        fx = integrateSpeed progress startSpd endSpd eas dur
        dfx = speedAtProgress progress startSpd endSpd eas
        newX = if abs dfx < epsilon then x else x - (fx - target) / dfx
      in
        if abs (fx - target) < epsilon then x
        else iterate (n - 1) (clamp01 newX * dur)
  in
    iterate 10 (clamp01 (initialGuess / dur) * dur)

-- | Speed at normalized progress for curve remap
speedAtProgress :: Number -> Number -> Number -> E.Easing -> Number
speedAtProgress progress startSpd endSpd eas =
  let easedProgress = E.evaluate eas progress
  in startSpd + easedProgress * (endSpd - startSpd)

-- | Invert keyframe remap using binary search.
invertKeyframeRemap :: Number -> Array SpeedKeyframe -> Number -> Number
invertKeyframeRemap target keyframes dur =
  let
    -- Binary search for input that produces target output
    search :: Number -> Number -> Int -> Number
    search lo hi 0 = (lo + hi) / 2.0
    search lo hi n =
      let mid = (lo + hi) / 2.0
          midOutput = integrateKeyframes mid keyframes
      in if abs (midOutput - target) < epsilon then mid
         else if midOutput < target then search mid hi (n - 1)
         else search lo mid (n - 1)
  in
    search 0.0 dur 20

-- | Apply remap to normalized progress (0-1).
applyToProgress :: Number -> TimeRemap -> Number
applyToProgress progress (TimeRemap tr) =
  let frame = progress * tr.originalDuration
      remappedFrame = apply frame (TimeRemap tr)
  in clamp01 (remappedFrame / tr.originalDuration)

-- | Get speed at specific frame.
speedAt :: Number -> TimeRemap -> Number
speedAt frame (TimeRemap tr) = case tr.mode of
  FreezeRemap _ -> 0.0
  PingPongRemap -> 
    let 
      cycle = frame / tr.originalDuration
      cycleInt = floorNum cycle
      isReverse = mod (floorInt cycleInt) 2 == 1
    in if isReverse then negate 1.0 else 1.0
  LoopRemap _ -> 1.0
  LinearRemap -> tr.speedFactor
  CurveRemap eas ->
    let progress = clamp01 (frame / tr.originalDuration)
        easedProgress = E.evaluate eas progress
    in tr.startSpeed + easedProgress * (tr.endSpeed - tr.startSpeed)
  KeyframeRemap -> speedAtKeyframes frame tr.keyframes

-- | Derivative of remap function (rate of time change).
derivativeAt :: Number -> TimeRemap -> Number
derivativeAt = speedAt

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // duration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get remapped (output) duration.
remappedDuration :: TimeRemap -> Number
remappedDuration (TimeRemap tr) = case tr.mode of
  FreezeRemap _ -> tr.originalDuration  -- Input duration unchanged
  PingPongRemap -> tr.originalDuration * 2.0
  LoopRemap _ -> tr.originalDuration  -- Each loop
  LinearRemap -> 
    if abs tr.speedFactor < epsilon then tr.originalDuration
    else tr.originalDuration / abs tr.speedFactor
  CurveRemap _ ->
    -- Approximate by average speed
    let avgSpeed = (abs tr.startSpeed + abs tr.endSpeed) / 2.0
    in if avgSpeed < epsilon then tr.originalDuration
       else tr.originalDuration / avgSpeed
  KeyframeRemap -> tr.originalDuration  -- Complex, use original

-- | Get original duration.
originalDuration :: TimeRemap -> Number
originalDuration (TimeRemap tr) = tr.originalDuration

-- | Set original duration.
setOriginalDuration :: Number -> TimeRemap -> TimeRemap
setOriginalDuration dur (TimeRemap tr) = TimeRemap (tr { originalDuration = dur })
