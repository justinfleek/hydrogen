-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--              // hydrogen // schema // reactive // data-validity // operations
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DataValidity.Operations — Constructors, queries, and combining operations.
-- |
-- | ## Purpose
-- |
-- | Provides constructor functions for creating DataValidity values,
-- | query functions for inspecting validity state, comparison functions
-- | for ranking validity states, and combining operations for working
-- | with multiple validity states.

module Hydrogen.Schema.Reactive.DataValidity.Operations
  ( -- * Constructors
    validData
  , degradedData
  , staleData
  , sensorFailure
  , commsLost
  , crossCheckFailed
  , outOfRange
  , rateExceeded
  , neverReceived
  
  -- * Basic Queries
  , isValid
  , isUsable
  , isFailed
  , requiresWarning
  , shouldDisplay
  , getConfidence
  , getAge
  
  -- * Validity Comparisons
  , validityScore
  , isBetterThan
  , isWorseThan
  , isEquivalentTo
  
  -- * Validity Combining
  , worstValidity
  , bestValidity
  , anyFailed
  , allValid
  , allUsable
  
  -- * Compound Predicates
  , isValidPrimary
  , isUsableDegraded
  , isWarningState
  , requiresImmediateAttention
  , safeForCriticalUse
  , needsFallback
  , validityChanged
  , isOperatingDegraded
  , eitherRequiresAttention
  ) where

import Prelude
  ( not
  , (&&)
  , (||)
  , (<)
  , (<=)
  , (>)
  , (>=)
  , (==)
  , (/=)
  )

-- Note: Array is imported from Prim (built-in)
import Data.Foldable (any, all)
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Reactive.DataValidity.Types
  ( DataValidity
      ( Valid
      , Degraded
      , Stale
      , SensorFailure
      , CommsLost
      , CrossCheckFailed
      , OutOfRange
      , RateOfChangeExceeded
      , NeverReceived
      )
  , FailureMode
  , DegradationReason
  , SensorId
  , Timestamp
  , Duration
  , Percent
  )

import Hydrogen.Schema.Reactive.DataValidity.DataAge
  ( DataAgeThresholds
  )

import Hydrogen.Schema.Reactive.DataValidity.SensorSource
  ( SensorSource
  , isPrimarySensor
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create valid data
validData :: Percent -> SensorId -> Timestamp -> DataValidity
validData confidence source timestamp = Valid { confidence, source, timestamp }

-- | Create degraded data
degradedData :: DegradationReason -> Boolean -> Percent -> SensorId -> Timestamp -> DataValidity
degradedData reason usable confidence source timestamp = 
  Degraded { reason, usable, confidence, source, timestamp }

-- | Create stale data
staleData :: Duration -> Timestamp -> SensorId -> DataValidity
staleData age lastValid source = Stale { age, lastValid, source }

-- | Create sensor failure
sensorFailure :: SensorId -> FailureMode -> Timestamp -> DataValidity
sensorFailure sensor failureMode detectedAt = 
  SensorFailure { sensor, failureMode, detectedAt }

-- | Create communications lost
commsLost :: Duration -> Timestamp -> SensorId -> DataValidity
commsLost since lastPacket source = CommsLost { since, lastPacket, source }

-- | Create cross-check failure
crossCheckFailed :: Array SensorId -> Percent -> Timestamp -> DataValidity
crossCheckFailed sources disagreement detectedAt = 
  CrossCheckFailed { sources, disagreement, detectedAt }

-- | Create out-of-range error
outOfRange :: Number -> Number -> Number -> SensorId -> Timestamp -> DataValidity
outOfRange value minBound maxBound source timestamp = 
  OutOfRange { value, minBound, maxBound, source, timestamp }

-- | Create rate-of-change exceeded
rateExceeded :: Number -> Number -> Number -> SensorId -> Timestamp -> DataValidity
rateExceeded current previous maxRate source timestamp = 
  RateOfChangeExceeded { current, previous, maxRate, source, timestamp }

-- | Create never received
neverReceived :: DataValidity
neverReceived = NeverReceived

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // basic queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is data currently valid (not degraded, stale, or failed)?
isValid :: DataValidity -> Boolean
isValid (Valid _) = true
isValid _ = false

-- | Is data usable (valid or usable-degraded)?
isUsable :: DataValidity -> Boolean
isUsable (Valid _) = true
isUsable (Degraded r) = r.usable
isUsable _ = false

-- | Has data failed completely?
isFailed :: DataValidity -> Boolean
isFailed (SensorFailure _) = true
isFailed (CommsLost _) = true
isFailed NeverReceived = true
isFailed _ = false

-- | Does this state require a warning to be displayed?
requiresWarning :: DataValidity -> Boolean
requiresWarning (Valid _) = false
requiresWarning _ = true

-- | Should this data be displayed at all?
shouldDisplay :: DataValidity -> Boolean
shouldDisplay NeverReceived = false
shouldDisplay (SensorFailure _) = false  -- Show failure flag, not data
shouldDisplay _ = true

-- | Get confidence level (0.0 for failed states)
getConfidence :: DataValidity -> Percent
getConfidence (Valid r) = r.confidence
getConfidence (Degraded r) = r.confidence
getConfidence _ = 0.0

-- | Get age of stale data (Nothing if not stale)
getAge :: DataValidity -> Maybe Duration
getAge (Stale r) = Just r.age
getAge (CommsLost r) = Just r.since
getAge _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // validity comparisons
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compare two validity states (more valid = greater)
-- |
-- | Valid > Degraded > Stale > Failed states
validityScore :: DataValidity -> Int
validityScore (Valid _) = 100
validityScore (Degraded r) = if r.usable then 75 else 50
validityScore (Stale _) = 25
validityScore (OutOfRange _) = 20
validityScore (RateOfChangeExceeded _) = 15
validityScore (CrossCheckFailed _) = 10
validityScore (CommsLost _) = 5
validityScore (SensorFailure _) = 2
validityScore NeverReceived = 0

-- | Is first validity state better than second?
isBetterThan :: DataValidity -> DataValidity -> Boolean
isBetterThan a b = validityScore a > validityScore b

-- | Is first validity state worse than second?
isWorseThan :: DataValidity -> DataValidity -> Boolean
isWorseThan a b = validityScore a < validityScore b

-- | Are two validity states equivalent in severity?
isEquivalentTo :: DataValidity -> DataValidity -> Boolean
isEquivalentTo a b = validityScore a == validityScore b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // validity combining
-- ═════════════════════════════════════════════════════════════════════════════

-- | Combine two validity states (take the worse)
-- |
-- | Useful for derived values that depend on multiple inputs:
-- | if any input is invalid, the derived value is invalid.
worstValidity :: DataValidity -> DataValidity -> DataValidity
worstValidity a b = if validityScore a <= validityScore b then a else b

-- | Combine two validity states (take the better)
-- |
-- | Useful for redundant sensors: take the best available reading.
bestValidity :: DataValidity -> DataValidity -> DataValidity
bestValidity a b = if validityScore a >= validityScore b then a else b

-- | Check if any validity state in array is failed
anyFailed :: Array DataValidity -> Boolean
anyFailed = any isFailed

-- | Check if all validity states in array are valid
allValid :: Array DataValidity -> Boolean
allValid = all isValid

-- | Check if all validity states in array are at least usable
allUsable :: Array DataValidity -> Boolean
allUsable = all isUsable

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // compound predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is data valid AND from primary sensor?
isValidPrimary :: DataValidity -> SensorSource -> Boolean
isValidPrimary validity source = isValid validity && isPrimarySensor source

-- | Is data usable but degraded?
isUsableDegraded :: DataValidity -> Boolean
isUsableDegraded (Degraded r) = r.usable
isUsableDegraded _ = false

-- | Is data in a warning state (not failed, but not fully valid)?
isWarningState :: DataValidity -> Boolean
isWarningState validity = requiresWarning validity && not (isFailed validity)

-- | Does data require immediate attention (failed or very stale)?
requiresImmediateAttention :: DataAgeThresholds -> DataValidity -> Boolean
requiresImmediateAttention thresholds validity = case validity of
  SensorFailure _ -> true
  CommsLost r -> r.since >= thresholds.staleMs
  Stale r -> r.age >= thresholds.staleMs
  CrossCheckFailed _ -> true
  NeverReceived -> true
  _ -> false

-- | Can data be used for safety-critical decisions?
safeForCriticalUse :: Percent -> DataValidity -> Boolean
safeForCriticalUse minConfidence validity = case validity of
  Valid r -> r.confidence >= minConfidence
  Degraded r -> r.usable && r.confidence >= minConfidence
  _ -> false

-- | Is data either failed OR below confidence threshold?
-- |
-- | Useful for triggering fallback to backup sensors.
needsFallback :: Percent -> DataValidity -> Boolean
needsFallback minConfidence validity = 
  isFailed validity || getConfidence validity < minConfidence

-- | Are two validity states different in severity?
-- |
-- | Useful for detecting state transitions that need logging.
validityChanged :: DataValidity -> DataValidity -> Boolean
validityChanged a b = validityScore a /= validityScore b

-- | Is data either stale OR from a non-primary source?
-- |
-- | Triggers "degraded operation" mode in some systems.
isOperatingDegraded :: DataValidity -> SensorSource -> Boolean
isOperatingDegraded validity source = 
  requiresWarning validity || not (isPrimarySensor source)

-- | Does either of two readings require attention?
-- |
-- | For redundant sensor pairs - alert if either has issues.
eitherRequiresAttention :: DataAgeThresholds -> DataValidity -> DataValidity -> Boolean
eitherRequiresAttention thresholds a b =
  requiresImmediateAttention thresholds a || requiresImmediateAttention thresholds b
