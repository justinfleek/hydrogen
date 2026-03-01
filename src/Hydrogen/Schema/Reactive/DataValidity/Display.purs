-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                 // hydrogen // schema // reactive // data-validity // display
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DataValidity.Display — Display response types and computation.
-- |
-- | ## Purpose
-- |
-- | Defines how data should be displayed based on validity state.
-- | Implements DO-178C display requirements:
-- | - Fresh data (< 250ms): normal display
-- | - Aging data (250ms - 2s): yellow cross-hatch overlay
-- | - Stale data (2s - 10s): X through display element
-- | - Invalid data (> 10s or sensor failure): remove from display entirely

module Hydrogen.Schema.Reactive.DataValidity.Display
  ( -- * Display Response
    DisplayResponse
      ( DisplayNormal
      , DisplayWithAge
      , DisplayCrossHatch
      , DisplayXThrough
      , DisplayRemove
      , DisplayWithFlag
      , DisplayFlash
      )
  
  -- * Failure Flags
  , FailureFlag
      ( FlagSensorFail
      , FlagCommsLoss
      , FlagXCheck
      , FlagOutOfRange
      , FlagRateExceeded
      , FlagNoData
      , FlagDegraded
      )
  
  -- * Display Response Computation
  , computeDisplayResponse
  , dataAgeToResponse
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , otherwise
  , (<)
  , (<>)
  )

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
  , Duration
  )

import Hydrogen.Schema.Reactive.DataValidity.DataAge
  ( DataAgeThresholds
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // display response
-- ═════════════════════════════════════════════════════════════════════════════

-- | How to display data based on validity state
data DisplayResponse
  = DisplayNormal                            -- Show normally
  | DisplayWithAge { age :: Duration }       -- Show with age indicator
  | DisplayCrossHatch                        -- Yellow cross-hatch overlay
  | DisplayXThrough                          -- X through the display element
  | DisplayRemove                            -- Remove from display entirely
  | DisplayWithFlag { flag :: FailureFlag }  -- Show with specific failure flag
  | DisplayFlash { message :: String, rateHz :: Number }  -- Flashing warning

derive instance eqDisplayResponse :: Eq DisplayResponse

instance showDisplayResponse :: Show DisplayResponse where
  show DisplayNormal = "DisplayNormal"
  show (DisplayWithAge r) = "DisplayWithAge(" <> show r.age <> "ms)"
  show DisplayCrossHatch = "DisplayCrossHatch"
  show DisplayXThrough = "DisplayXThrough"
  show DisplayRemove = "DisplayRemove"
  show (DisplayWithFlag r) = "DisplayWithFlag(" <> show r.flag <> ")"
  show (DisplayFlash r) = "DisplayFlash(" <> r.message <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // failure flags
-- ═════════════════════════════════════════════════════════════════════════════

-- | Specific failure flags for safety-critical displays
data FailureFlag
  = FlagSensorFail      -- SENS FAIL
  | FlagCommsLoss       -- COMMS
  | FlagXCheck          -- X-CHECK
  | FlagOutOfRange      -- OOR
  | FlagRateExceeded    -- RATE
  | FlagNoData          -- NO DATA
  | FlagDegraded        -- DEGD

derive instance eqFailureFlag :: Eq FailureFlag

instance showFailureFlag :: Show FailureFlag where
  show FlagSensorFail = "SENS FAIL"
  show FlagCommsLoss = "COMMS"
  show FlagXCheck = "X-CHECK"
  show FlagOutOfRange = "OOR"
  show FlagRateExceeded = "RATE"
  show FlagNoData = "NO DATA"
  show FlagDegraded = "DEGD"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // display response logic
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute display response from data validity
computeDisplayResponse :: DataAgeThresholds -> DataValidity -> DisplayResponse
computeDisplayResponse thresholds validity = case validity of
  Valid _ -> 
    DisplayNormal
  
  Degraded r -> 
    if r.usable 
      then DisplayWithFlag { flag: FlagDegraded }
      else DisplayXThrough
  
  Stale r -> 
    dataAgeToResponse thresholds r.age
  
  SensorFailure _ -> 
    DisplayWithFlag { flag: FlagSensorFail }
  
  CommsLost r -> 
    if r.since < thresholds.invalidMs
      then DisplayWithFlag { flag: FlagCommsLoss }
      else DisplayRemove
  
  CrossCheckFailed _ -> 
    DisplayWithFlag { flag: FlagXCheck }
  
  OutOfRange _ -> 
    DisplayWithFlag { flag: FlagOutOfRange }
  
  RateOfChangeExceeded _ -> 
    DisplayWithFlag { flag: FlagRateExceeded }
  
  NeverReceived -> 
    DisplayRemove

-- | Convert data age to display response
dataAgeToResponse :: DataAgeThresholds -> Duration -> DisplayResponse
dataAgeToResponse thresholds ageMs
  | ageMs < thresholds.freshMs = DisplayNormal
  | ageMs < thresholds.staleMs = DisplayWithAge { age: ageMs }
  | ageMs < thresholds.invalidMs = DisplayXThrough
  | otherwise = DisplayRemove
