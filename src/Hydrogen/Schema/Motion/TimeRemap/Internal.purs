-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // motion // timeremap
--                                                                   // internal
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Internal helper functions for time remapping.
-- |
-- | ## Contents
-- |
-- | - Numeric helpers (clamp, floor, mod)
-- | - Array building utilities
-- | - Integration functions for speed curves
-- | - Keyframe interpolation
-- |
-- | ## Dependencies
-- |
-- | - Types: SpeedKeyframe
-- | - Easing: evaluate

module Hydrogen.Schema.Motion.TimeRemap.Internal
  ( -- * Numeric Helpers
    clamp01
  , clampNumber
  , floorNum
  , floorInt
  , truncateToInt
  , mod
  , epsilon
  , infinity
  
  -- * Speed Bounds (CRITICAL for billion-agent scale)
  , maxSpeedFactor
  , minSpeedFactor
  , clampSpeed
  
  -- * Array Utilities
  , buildArray
  , buildIntArray
  
  -- * Integration
  , integrateSpeed
  , integrateKeyframes
  
  -- * Keyframe Helpers
  , speedAtKeyframes
  , findSurroundingKeyframes
  , sortKeyframes
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
  , (<=)
  , (>=)
  , (==)
  , (&&)
  , otherwise
  , min
  , max
  , negate
  )

import Data.Array (length, index, snoc, foldl, sortBy)
import Data.Maybe (Maybe(..))
import Data.Int (toNumber) as Int
import Data.Ordering (Ordering(..))

import Hydrogen.Schema.Motion.Easing (Easing, evaluate)
import Hydrogen.Schema.Motion.TimeRemap.Types (SpeedKeyframe(SpeedKeyframe))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // numeric helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp to [0, 1]
clamp01 :: Number -> Number
clamp01 n
  | n < 0.0 = 0.0
  | n > 1.0 = 1.0
  | otherwise = n

-- | Clamp to range
-- | Named clampNumber to avoid shadowing Prelude.clamp
clampNumber :: Number -> Number -> Number -> Number
clampNumber lo hi n
  | n < lo = lo
  | n > hi = hi
  | otherwise = n

-- | Floor
floorNum :: Number -> Number
floorNum n = Int.toNumber (floorInt n)

floorInt :: Number -> Int
floorInt n = 
  if n >= 0.0 then truncateToInt n
  else truncateToInt n - 1

truncateToInt :: Number -> Int
truncateToInt n = truncateImpl n 0

truncateImpl :: Number -> Int -> Int
truncateImpl n acc =
  if n < 1.0 then acc
  else truncateImpl (n - 1.0) (acc + 1)

-- | Integer modulo
mod :: Int -> Int -> Int
mod a b = a - (a / b) * b

-- | Small epsilon
epsilon :: Number
epsilon = 1.0e-10

-- | Large number for min comparisons
infinity :: Number
infinity = 1.0e308

-- ═════════════════════════════════════════════════════════════════════════════
--                                              // speed bounds // billion agent
-- ═════════════════════════════════════════════════════════════════════════════

-- | Maximum speed value to prevent exponential blowup at billion-agent scale.
-- |
-- | At 1000x playback, a 1-hour video plays in 3.6 seconds.
-- | At 10000x, it's 360ms — beyond useful. Clamp here.
maxSpeedFactor :: Number
maxSpeedFactor = 1000.0

-- | Minimum speed value (prevents division-by-zero and near-infinite durations).
-- |
-- | At 0.001x speed, a 1-second clip takes 1000 seconds (16+ minutes).
-- | Below this is effectively a freeze frame — use FreezeRemap instead.
minSpeedFactor :: Number
minSpeedFactor = 0.001

-- | Clamp a speed value to valid bounds.
-- |
-- | **CRITICAL**: All speed multiplications MUST go through this function.
-- | Without clamping, repeated normalizations can compound exponentially,
-- | causing numeric overflow at swarm scale.
clampSpeed :: Number -> Number
clampSpeed s
  | s > maxSpeedFactor = maxSpeedFactor
  | s < negate maxSpeedFactor = negate maxSpeedFactor
  | s > 0.0 && s < minSpeedFactor = minSpeedFactor
  | s < 0.0 && s > negate minSpeedFactor = negate minSpeedFactor
  | otherwise = s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // array utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Build array from function
buildArray :: forall a. Int -> (Int -> Maybe a) -> Array a
buildArray n f = buildArrayImpl 0 n f []

buildArrayImpl :: forall a. Int -> Int -> (Int -> Maybe a) -> Array a -> Array a
buildArrayImpl i n f acc =
  if i >= n then acc
  else case f i of
    Nothing -> buildArrayImpl (i + 1) n f acc
    Just x -> buildArrayImpl (i + 1) n f (snoc acc x)

-- | Build integer array
buildIntArray :: Int -> Array Int
buildIntArray n = buildArray n Just

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // integration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Integrate speed curve to get position.
integrateSpeed :: Number -> Number -> Number -> Easing -> Number -> Number
integrateSpeed progress startSpd endSpd eas dur =
  -- Trapezoidal integration over the speed curve
  let 
    numSamples = 20
    dt = dur / Int.toNumber numSamples
    sumResult = foldl (\acc i ->
      let 
        t = Int.toNumber i / Int.toNumber numSamples
        -- Only integrate up to progress point
        contributionT = min t progress
        easedT = evaluate eas contributionT
        speed = startSpd + easedT * (endSpd - startSpd)
      in 
        if t <= progress then acc + speed * dt
        else acc
    ) 0.0 (buildIntArray (numSamples + 1))
  in sumResult

-- | Integrate keyframes to get time.
integrateKeyframes :: Number -> Array SpeedKeyframe -> Number
integrateKeyframes frame kfs =
  let n = length kfs
  in if n == 0 then frame  -- No keyframes = identity
     else
       -- Sum contributions from each keyframe segment
       foldl (\acc i ->
         case { k1: index kfs i, k2: index kfs (i + 1) } of
           { k1: Just (SpeedKeyframe kb), k2: Just (SpeedKeyframe ka) } ->
             if frame < kb.frame then acc
             else if frame >= ka.frame then
               -- Full segment
               let avgSpeed = (kb.speed + ka.speed) / 2.0
                   segDur = ka.frame - kb.frame
               in acc + avgSpeed * segDur
             else
               -- Partial segment
               let 
                 t = (frame - kb.frame) / (ka.frame - kb.frame)
                 easedT = evaluate kb.easing t
                 currentSpeed = kb.speed + easedT * (ka.speed - kb.speed)
                 avgSpeed = (kb.speed + currentSpeed) / 2.0
                 segDur = frame - kb.frame
               in acc + avgSpeed * segDur
           _ -> acc
       ) 0.0 (buildIntArray (max 0 (n - 1)))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // keyframe helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get speed at frame from keyframes.
speedAtKeyframes :: Number -> Array SpeedKeyframe -> Number
speedAtKeyframes frame kfs =
  let n = length kfs
  in if n == 0 then 1.0
     else
       case findSurroundingKeyframes frame kfs of
         { before: Just (SpeedKeyframe kb), after: Just (SpeedKeyframe ka) } ->
           if ka.frame == kb.frame then kb.speed
           else
             let 
               t = (frame - kb.frame) / (ka.frame - kb.frame)
               easedT = evaluate kb.easing t
             in kb.speed + easedT * (ka.speed - kb.speed)
         { before: Just (SpeedKeyframe kb), after: Nothing } -> kb.speed
         { before: Nothing, after: Just (SpeedKeyframe ka) } -> ka.speed
         _ -> 1.0

-- | Find keyframes surrounding a frame.
findSurroundingKeyframes :: Number -> Array SpeedKeyframe 
  -> { before :: Maybe SpeedKeyframe, after :: Maybe SpeedKeyframe }
findSurroundingKeyframes frame kfs =
  let n = length kfs
  in foldl (\acc i ->
       case index kfs i of
         Nothing -> acc
         Just kf@(SpeedKeyframe k) ->
           if k.frame <= frame then
             case acc.before of
               Nothing -> acc { before = Just kf }
               Just (SpeedKeyframe prev) -> 
                 if k.frame > prev.frame then acc { before = Just kf }
                 else acc
           else
             case acc.after of
               Nothing -> acc { after = Just kf }
               Just (SpeedKeyframe next) ->
                 if k.frame < next.frame then acc { after = Just kf }
                 else acc
     ) { before: Nothing, after: Nothing } (buildIntArray n)

-- | Sort keyframes by frame.
sortKeyframes :: Array SpeedKeyframe -> Array SpeedKeyframe
sortKeyframes = sortBy (\(SpeedKeyframe a) (SpeedKeyframe b) ->
  if a.frame < b.frame then LT
  else if a.frame > b.frame then GT
  else EQ
)
