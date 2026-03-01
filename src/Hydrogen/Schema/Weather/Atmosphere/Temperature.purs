-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                // hydrogen // schema // weather // atmosphere // temperature
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Temperature primitives for atmospheric measurement.
-- |
-- | ## Physical Bounds
-- |
-- | Temperature (Earth surface):
-- | - Record low: -89.2°C (Antarctica, Vostok Station)
-- | - Record high: +56.7°C (Death Valley)
-- | - Practical range: -100°C to +100°C (includes margin)
-- |
-- | Celsius is canonical; conversions to Fahrenheit and Kelvin available.

module Hydrogen.Schema.Weather.Atmosphere.Temperature
  ( -- * Temperature Type
    Temperature
  , temperature
  , temperatureUnsafe
  , unwrapTemperature
  , temperatureBounds
  
  -- * Unit Conversions
  , celsius
  , fahrenheit
  , kelvin
  
  -- * Constants
  , tempAbsoluteZero
  , tempFreezingPoint
  , tempRoomTemp
  , tempBodyTemp
  , tempBoilingPoint
  , tempRecordLow
  , tempRecordHigh
  
  -- * Operations
  , lerp
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , negate
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // temperature
-- ═════════════════════════════════════════════════════════════════════════════

-- | Temperature in Celsius [-100, 100].
-- |
-- | ## Bounds Rationale
-- |
-- | - Minimum -100°C: Below coldest recorded (-89.2°C)
-- | - Maximum +100°C: Above boiling, covers extreme scenarios
-- |
-- | Celsius is canonical; conversions available.
newtype Temperature = Temperature Number

derive instance eqTemperature :: Eq Temperature
derive instance ordTemperature :: Ord Temperature

instance showTemperature :: Show Temperature where
  show (Temperature n) = "Temperature " <> show n <> "°C"

-- | Safe constructor with clamping.
temperature :: Number -> Temperature
temperature n = Temperature (Bounded.clampNumber (-100.0) 100.0 n)

-- | Unsafe constructor for known-valid values.
temperatureUnsafe :: Number -> Temperature
temperatureUnsafe = Temperature

-- | Extract raw value.
unwrapTemperature :: Temperature -> Number
unwrapTemperature (Temperature n) = n

-- | Valid bounds documentation.
temperatureBounds :: Bounded.NumberBounds
temperatureBounds = Bounded.numberBounds (-100.0) 100.0 Bounded.Clamps "temperature" "Temperature in Celsius"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // unit // conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get temperature in Celsius (identity).
celsius :: Temperature -> Number
celsius = unwrapTemperature

-- | Convert to Fahrenheit.
fahrenheit :: Temperature -> Number
fahrenheit (Temperature c) = c * 9.0 / 5.0 + 32.0

-- | Convert to Kelvin.
kelvin :: Temperature -> Number
kelvin (Temperature c) = c + 273.15

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Absolute zero (-273.15°C, clamped to -100°C).
tempAbsoluteZero :: Temperature
tempAbsoluteZero = Temperature (-100.0)  -- Clamped from true -273.15

-- | Water freezing point (0°C).
tempFreezingPoint :: Temperature
tempFreezingPoint = Temperature 0.0

-- | Room temperature (20°C).
tempRoomTemp :: Temperature
tempRoomTemp = Temperature 20.0

-- | Human body temperature (37°C).
tempBodyTemp :: Temperature
tempBodyTemp = Temperature 37.0

-- | Water boiling point at sea level (100°C).
tempBoilingPoint :: Temperature
tempBoilingPoint = Temperature 100.0

-- | Record low Earth surface (-89.2°C).
tempRecordLow :: Temperature
tempRecordLow = Temperature (-89.2)

-- | Record high Earth surface (+56.7°C).
tempRecordHigh :: Temperature
tempRecordHigh = Temperature 56.7

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Linear interpolation between two temperatures.
lerp :: Number -> Temperature -> Temperature -> Temperature
lerp t (Temperature a) (Temperature b) =
  temperature (a + t * (b - a))
