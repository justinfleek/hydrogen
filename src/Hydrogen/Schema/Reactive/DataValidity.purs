-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // reactive // data-validity
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DataValidity — Graduated failure modes for safety-critical systems.
-- |
-- | ## Purpose
-- |
-- | In safety-critical domains (avionics DO-178C DAL-A, medical FDA 21 CFR Part 11),
-- | a simple boolean "stale" flag is insufficient. Systems must distinguish between:
-- |
-- | - Data that is current and trustworthy
-- | - Data that is aging but still usable
-- | - Data that is stale and requires visual indication
-- | - Data that has failed and must be removed from display
-- | - Data from redundant sources that disagree
-- |
-- | ## DO-178C Requirements
-- |
-- | Avionics displays must show:
-- | - Fresh data (< 250ms): normal display
-- | - Aging data (250ms - 2s): yellow cross-hatch overlay
-- | - Stale data (2s - 10s): X through display element
-- | - Invalid data (> 10s or sensor failure): remove from display entirely
-- |
-- | ## FDA Requirements
-- |
-- | Medical displays must:
-- | - Track data provenance (which sensor, which timestamp)
-- | - Show signal quality indicators
-- | - Provide audible alarms for data failure
-- | - Never display potentially misleading information without warning
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports all submodules:
-- | - Types: Core types (DataValidity, FailureMode, DegradationReason)
-- | - Display: Display response types and computation
-- | - DataAge: Data age classification per DO-178C
-- | - SignalQuality: Signal quality indicators for medical displays
-- | - SensorSource: Sensor source tracking for redundancy
-- | - Operations: Constructors, queries, comparisons, combining
-- | - Arithmetic: Numeric operations for validity calculations

module Hydrogen.Schema.Reactive.DataValidity
  ( -- * Core Types (from Types)
    module Hydrogen.Schema.Reactive.DataValidity.Types
  
  -- * Display Response (from Display)
  , module Hydrogen.Schema.Reactive.DataValidity.Display
  
  -- * Data Age (from DataAge)
  , module Hydrogen.Schema.Reactive.DataValidity.DataAge
  
  -- * Signal Quality (from SignalQuality)
  , module Hydrogen.Schema.Reactive.DataValidity.SignalQuality
  
  -- * Sensor Source (from SensorSource)
  , module Hydrogen.Schema.Reactive.DataValidity.SensorSource
  
  -- * Operations (from Operations)
  , module Hydrogen.Schema.Reactive.DataValidity.Operations
  
  -- * Arithmetic (from Arithmetic)
  , module Hydrogen.Schema.Reactive.DataValidity.Arithmetic
  ) where

import Hydrogen.Schema.Reactive.DataValidity.Types
  ( SensorId
  , Timestamp
  , Duration
  , Percent
  , DataValidity
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
      ( HardwareFault
      , CalibrationError
      , RangeExceeded
      , SelfTestFailed
      , PowerFailure
      , ConnectionLost
      , UnknownFailure
      )
  , DegradationReason
      ( ReducedAccuracy
      , InterferenceDet
      , EnvironmentalLimit
      , BackupSensor
      , FilteredData
      , Interpolated
      )
  )

import Hydrogen.Schema.Reactive.DataValidity.Display
  ( DisplayResponse
      ( DisplayNormal
      , DisplayWithAge
      , DisplayCrossHatch
      , DisplayXThrough
      , DisplayRemove
      , DisplayWithFlag
      , DisplayFlash
      )
  , FailureFlag
      ( FlagSensorFail
      , FlagCommsLoss
      , FlagXCheck
      , FlagOutOfRange
      , FlagRateExceeded
      , FlagNoData
      , FlagDegraded
      )
  , computeDisplayResponse
  , dataAgeToResponse
  )

import Hydrogen.Schema.Reactive.DataValidity.DataAge
  ( DataAge
      ( Fresh
      , Aging
      , StaleAge
      , Invalid
      )
  , DataAgeThresholds
  , ageThresholds
  , computeDataAge
  )

import Hydrogen.Schema.Reactive.DataValidity.SignalQuality
  ( SignalQuality
      ( QualityGood
      , QualityMarginal
      , QualityPoor
      , QualityInvalid
      , QualityLeadOff
      )
  , signalQualityFromConfidence
  , signalQualityToString
  )

import Hydrogen.Schema.Reactive.DataValidity.SensorSource
  ( SensorSource
      ( Primary
      , Secondary
      , Tertiary
      , Computed
      , Synthesized
      )
  , isPrimarySensor
  , sensorSourcePriority
  , compareSensorSources
  , hasHigherPriority
  )

import Hydrogen.Schema.Reactive.DataValidity.Operations
  ( validData
  , degradedData
  , staleData
  , sensorFailure
  , commsLost
  , crossCheckFailed
  , outOfRange
  , rateExceeded
  , neverReceived
  , isValid
  , isUsable
  , isFailed
  , requiresWarning
  , shouldDisplay
  , getConfidence
  , getAge
  , validityScore
  , isBetterThan
  , isWorseThan
  , isEquivalentTo
  , worstValidity
  , bestValidity
  , anyFailed
  , allValid
  , allUsable
  , isValidPrimary
  , isUsableDegraded
  , isWarningState
  , requiresImmediateAttention
  , safeForCriticalUse
  , needsFallback
  , validityChanged
  , isOperatingDegraded
  , eitherRequiresAttention
  )

import Hydrogen.Schema.Reactive.DataValidity.Arithmetic
  ( computeAge
  , updateStaleAge
  , ageExceeds
  , timeUntilInvalid
  , clampConfidence
  , averageConfidence
  , minimumConfidence
  , confidenceMeetsThreshold
  , degradeConfidence
  , computeRateOfChange
  , rateWithinLimits
  , computeDisagreement
  , absNum
  , minNum
  , sumNumbers
  )
