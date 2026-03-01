-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                   // hydrogen // schema // reactive // data-validity // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DataValidity.Types — Core types for graduated failure modes.
-- |
-- | ## Purpose
-- |
-- | Defines the core types for data validity states in safety-critical systems.
-- | These types capture the full spectrum of data integrity states required by
-- | DO-178C and FDA regulations.

module Hydrogen.Schema.Reactive.DataValidity.Types
  ( -- * Core Aliases
    SensorId
  , Timestamp
  , Duration
  , Percent
  
  -- * Data Validity
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
  
  -- * Failure Modes
  , FailureMode
      ( HardwareFault
      , CalibrationError
      , RangeExceeded
      , SelfTestFailed
      , PowerFailure
      , ConnectionLost
      , UnknownFailure
      )
  
  -- * Degradation Reasons
  , DegradationReason
      ( ReducedAccuracy
      , InterferenceDet
      , EnvironmentalLimit
      , BackupSensor
      , FilteredData
      , Interpolated
      )
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

-- Note: Array is imported from Prim (built-in)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // core aliases
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sensor identifier (opaque string for now, could be UUID5)
type SensorId = String

-- | Unix timestamp in milliseconds
type Timestamp = Number

-- | Duration in milliseconds
type Duration = Number

-- | Percentage (0.0 to 100.0)
type Percent = Number

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // data validity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Graduated data validity states for safety-critical systems.
-- |
-- | Unlike simple boolean staleness, this captures the full spectrum of
-- | data integrity states required by DO-178C and FDA regulations.
data DataValidity
  = Valid 
      { confidence :: Percent    -- 0.0-100.0 confidence level
      , source :: SensorId       -- Which sensor provided this data
      , timestamp :: Timestamp   -- When data was sampled
      }
  | Degraded
      { reason :: DegradationReason
      , usable :: Boolean        -- Can still be used with caution
      , confidence :: Percent    -- Reduced confidence level
      , source :: SensorId
      , timestamp :: Timestamp
      }
  | Stale
      { age :: Duration          -- How long since last valid data
      , lastValid :: Timestamp   -- When data was last valid
      , source :: SensorId
      }
  | SensorFailure
      { sensor :: SensorId
      , failureMode :: FailureMode
      , detectedAt :: Timestamp
      }
  | CommsLost
      { since :: Duration        -- Duration of communication loss
      , lastPacket :: Timestamp  -- When last packet was received
      , source :: SensorId
      }
  | CrossCheckFailed
      { sources :: Array SensorId    -- Disagreeing sensors
      , disagreement :: Percent      -- How much they disagree
      , detectedAt :: Timestamp
      }
  | OutOfRange
      { value :: Number
      , minBound :: Number
      , maxBound :: Number
      , source :: SensorId
      , timestamp :: Timestamp
      }
  | RateOfChangeExceeded
      { current :: Number
      , previous :: Number
      , maxRate :: Number        -- Maximum allowed rate of change per second
      , source :: SensorId
      , timestamp :: Timestamp
      }
  | NeverReceived               -- Source never provided any data

derive instance eqDataValidity :: Eq DataValidity

instance showDataValidity :: Show DataValidity where
  show (Valid r) = "Valid(confidence=" <> show r.confidence <> "%, source=" <> r.source <> ")"
  show (Degraded r) = "Degraded(" <> show r.reason <> ", usable=" <> show r.usable <> ")"
  show (Stale r) = "Stale(age=" <> show r.age <> "ms)"
  show (SensorFailure r) = "SensorFailure(" <> r.sensor <> ", " <> show r.failureMode <> ")"
  show (CommsLost r) = "CommsLost(since=" <> show r.since <> "ms)"
  show (CrossCheckFailed r) = "CrossCheckFailed(disagreement=" <> show r.disagreement <> "%)"
  show (OutOfRange r) = "OutOfRange(value=" <> show r.value <> ")"
  show (RateOfChangeExceeded r) = "RateOfChangeExceeded(current=" <> show r.current <> ")"
  show NeverReceived = "NeverReceived"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // failure modes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Specific failure modes for sensor failures
data FailureMode
  = HardwareFault       -- Physical sensor failure
  | CalibrationError    -- Sensor needs recalibration
  | RangeExceeded       -- Value outside sensor capability
  | SelfTestFailed      -- Built-in test failed
  | PowerFailure        -- Sensor lost power
  | ConnectionLost      -- Physical connection broken
  | UnknownFailure      -- Undiagnosed failure

derive instance eqFailureMode :: Eq FailureMode
derive instance ordFailureMode :: Ord FailureMode

instance showFailureMode :: Show FailureMode where
  show HardwareFault = "HardwareFault"
  show CalibrationError = "CalibrationError"
  show RangeExceeded = "RangeExceeded"
  show SelfTestFailed = "SelfTestFailed"
  show PowerFailure = "PowerFailure"
  show ConnectionLost = "ConnectionLost"
  show UnknownFailure = "UnknownFailure"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // degradation reasons
-- ═════════════════════════════════════════════════════════════════════════════

-- | Reasons for degraded data quality
data DegradationReason
  = ReducedAccuracy     -- Sensor operating in degraded mode
  | InterferenceDet     -- Electromagnetic interference detected
  | EnvironmentalLimit  -- Temperature/pressure outside optimal range
  | BackupSensor        -- Using backup instead of primary
  | FilteredData        -- Data has been filtered/smoothed
  | Interpolated        -- Value interpolated from adjacent samples

derive instance eqDegradationReason :: Eq DegradationReason

instance showDegradationReason :: Show DegradationReason where
  show ReducedAccuracy = "ReducedAccuracy"
  show InterferenceDet = "InterferenceDetected"
  show EnvironmentalLimit = "EnvironmentalLimit"
  show BackupSensor = "BackupSensor"
  show FilteredData = "FilteredData"
  show Interpolated = "Interpolated"
