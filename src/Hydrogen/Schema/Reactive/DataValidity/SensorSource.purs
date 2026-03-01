-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--           // hydrogen // schema // reactive // data-validity // sensor-source
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DataValidity.SensorSource — Sensor source tracking for redundancy.
-- |
-- | ## Purpose
-- |
-- | Tracks which sensor provided data for redundancy management.
-- | Safety-critical systems require tracking of sensor source to:
-- | - Identify when backup sensors are in use
-- | - Compare readings from multiple sources
-- | - Prioritize primary sensors over computed values

module Hydrogen.Schema.Reactive.DataValidity.SensorSource
  ( -- * Sensor Source Type
    SensorSource
      ( Primary
      , Secondary
      , Tertiary
      , Computed
      , Synthesized
      )
  
  -- * Query Functions
  , isPrimarySensor
  , sensorSourcePriority
  
  -- * Comparison Functions
  , compareSensorSources
  , hasHigherPriority
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , Ordering
  , compare
  , (<)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // sensor source
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sensor source for redundancy tracking
data SensorSource
  = Primary         -- Primary sensor
  | Secondary       -- Backup sensor
  | Tertiary        -- Third-level redundancy
  | Computed        -- Computed/derived value
  | Synthesized     -- Synthesized from multiple sources

derive instance eqSensorSource :: Eq SensorSource
derive instance ordSensorSource :: Ord SensorSource

instance showSensorSource :: Show SensorSource where
  show Primary = "Primary"
  show Secondary = "Secondary"
  show Tertiary = "Tertiary"
  show Computed = "Computed"
  show Synthesized = "Synthesized"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // query functions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if this is a primary sensor
isPrimarySensor :: SensorSource -> Boolean
isPrimarySensor Primary = true
isPrimarySensor _ = false

-- | Get priority order (lower = higher priority)
sensorSourcePriority :: SensorSource -> Int
sensorSourcePriority Primary = 0
sensorSourcePriority Secondary = 1
sensorSourcePriority Tertiary = 2
sensorSourcePriority Computed = 3
sensorSourcePriority Synthesized = 4

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // comparison functions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compare sensor sources by priority
compareSensorSources :: SensorSource -> SensorSource -> Ordering
compareSensorSources a b = compare (sensorSourcePriority a) (sensorSourcePriority b)

-- | Check if first sensor has higher priority than second
hasHigherPriority :: SensorSource -> SensorSource -> Boolean
hasHigherPriority a b = sensorSourcePriority a < sensorSourcePriority b
