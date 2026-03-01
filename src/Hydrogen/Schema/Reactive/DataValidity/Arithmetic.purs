-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--              // hydrogen // schema // reactive // data-validity // arithmetic
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DataValidity.Arithmetic — Numeric operations for validity calculations.
-- |
-- | ## Purpose
-- |
-- | Provides age arithmetic, confidence math, rate of change calculations,
-- | and helper functions for numeric operations on validity data.

module Hydrogen.Schema.Reactive.DataValidity.Arithmetic
  ( -- * Age Arithmetic
    computeAge
  , updateStaleAge
  , ageExceeds
  , timeUntilInvalid
  
  -- * Confidence Math
  , clampConfidence
  , averageConfidence
  , minimumConfidence
  , confidenceMeetsThreshold
  , degradeConfidence
  
  -- * Rate of Change
  , computeRateOfChange
  , rateWithinLimits
  , computeDisagreement
  
  -- * Helper Functions
  , absNum
  , minNum
  , sumNumbers
  ) where

import Prelude
  ( otherwise
  , (>)
  , (<)
  , (<=)
  , (>=)
  , (==)
  , (-)
  , (+)
  , (/)
  , (*)
  , ($)
  )

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Int (toNumber)

import Hydrogen.Schema.Reactive.DataValidity.Types
  ( DataValidity
      ( Stale
      , CommsLost
      )
  , Timestamp
  , Duration
  , Percent
  )

import Hydrogen.Schema.Reactive.DataValidity.DataAge
  ( DataAgeThresholds
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // age arithmetic
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute age from timestamps
computeAge :: Timestamp -> Timestamp -> Duration
computeAge currentTime lastValidTime = currentTime - lastValidTime

-- | Update stale data with new age
updateStaleAge :: Timestamp -> DataValidity -> DataValidity
updateStaleAge currentTime validity = case validity of
  Stale r -> Stale $ r { age = currentTime - r.lastValid }
  CommsLost r -> CommsLost $ r { since = currentTime - r.lastPacket }
  other -> other

-- | Check if age exceeds threshold
ageExceeds :: Duration -> Duration -> Boolean
ageExceeds age threshold = age > threshold

-- | Compute time until state becomes invalid
timeUntilInvalid :: DataAgeThresholds -> Duration -> Duration
timeUntilInvalid thresholds currentAge = 
  if currentAge >= thresholds.invalidMs 
    then 0.0 
    else thresholds.invalidMs - currentAge

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // confidence math
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp confidence to valid range
clampConfidence :: Percent -> Percent
clampConfidence c
  | c < 0.0 = 0.0
  | c > 100.0 = 100.0
  | otherwise = c

-- | Average confidence of multiple readings
averageConfidence :: Array Percent -> Percent
averageConfidence arr = 
  let len = Array.length arr
  in if len == 0 
       then 0.0 
       else sumNumbers arr / toNumber len

-- | Minimum confidence of multiple readings (pessimistic)
minimumConfidence :: Array Percent -> Percent
minimumConfidence arr = foldl minNum 100.0 arr

-- | Check if confidence meets threshold
confidenceMeetsThreshold :: Percent -> Percent -> Boolean
confidenceMeetsThreshold confidence threshold = confidence >= threshold

-- | Degrade confidence by factor (0.0-1.0)
degradeConfidence :: Number -> Percent -> Percent
degradeConfidence factor confidence = clampConfidence (confidence * factor)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // rate of change
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute rate of change between two values
computeRateOfChange :: Number -> Number -> Duration -> Number
computeRateOfChange current previous deltaMs =
  if deltaMs <= 0.0 
    then 0.0 
    else absNum (current - previous) / (deltaMs / 1000.0)

-- | Check if rate of change is within limits
rateWithinLimits :: Number -> Number -> Boolean
rateWithinLimits rate maxRate = rate <= maxRate

-- | Compute disagreement between two sensor readings
computeDisagreement :: Number -> Number -> Number -> Percent
computeDisagreement value1 value2 referenceRange =
  if referenceRange <= 0.0
    then 100.0
    else clampConfidence (absNum (value1 - value2) / referenceRange * 100.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // helper functions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Absolute value helper
absNum :: Number -> Number
absNum n = if n < 0.0 then 0.0 - n else n

-- | Minimum of two numbers
minNum :: Number -> Number -> Number
minNum a b = if a <= b then a else b

-- | Sum an array of numbers
sumNumbers :: Array Number -> Number
sumNumbers = foldl (+) 0.0
