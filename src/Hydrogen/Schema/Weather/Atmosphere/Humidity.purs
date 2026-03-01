-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                  // hydrogen // schema // weather // atmosphere // humidity
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Humidity and dew point primitives for atmospheric measurement.
-- |
-- | ## Relative Humidity
-- |
-- | Ratio of actual water vapor to saturation vapor pressure.
-- | - Range: 0-100% (can exceed 100% in supersaturated conditions)
-- |
-- | ## Dew Point
-- |
-- | Temperature at which condensation occurs.
-- | - Range: -80°C (Antarctica interior) to +40°C (Persian Gulf extremes)
-- |
-- | Dew point indicates moisture content independent of temperature.

module Hydrogen.Schema.Weather.Atmosphere.Humidity
  ( -- * Relative Humidity
    RelativeHumidity
  , relativeHumidity
  , relativeHumidityUnsafe
  , unwrapRelativeHumidity
  , humidityBounds
  , humidityPercent
  
  -- * Humidity Constants
  , humidityDesert
  , humidityComfortable
  , humidityHumid
  , humiditySaturated
  
  -- * Dew Point
  , DewPoint
  , dewPoint
  , dewPointUnsafe
  , unwrapDewPoint
  , dewPointBounds
  , dewPointCelsius
  
  -- * Dew Point Constants
  , dewPointDry
  , dewPointComfortable
  , dewPointHumid
  , dewPointOppressive
  
  -- * Operations
  , calculateDewPoint
  , calculateHumidity
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

import Data.Number (log, exp) as Number
import Hydrogen.Schema.Bounded as Bounded
import Hydrogen.Schema.Weather.Atmosphere.Temperature (Temperature, unwrapTemperature, temperature)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // relative // humidity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Relative humidity in percent [0, 100].
-- |
-- | Ratio of actual water vapor to saturation vapor pressure.
-- | Can exceed 100% in supersaturated conditions (fog, clouds).
newtype RelativeHumidity = RelativeHumidity Number

derive instance eqRelativeHumidity :: Eq RelativeHumidity
derive instance ordRelativeHumidity :: Ord RelativeHumidity

instance showRelativeHumidity :: Show RelativeHumidity where
  show (RelativeHumidity n) = "RelativeHumidity " <> show n <> "%"

-- | Safe constructor with clamping.
relativeHumidity :: Number -> RelativeHumidity
relativeHumidity n = RelativeHumidity (Bounded.clampNumber 0.0 100.0 n)

-- | Unsafe constructor for known-valid values.
relativeHumidityUnsafe :: Number -> RelativeHumidity
relativeHumidityUnsafe = RelativeHumidity

-- | Extract raw value.
unwrapRelativeHumidity :: RelativeHumidity -> Number
unwrapRelativeHumidity (RelativeHumidity n) = n

-- | Valid bounds documentation.
humidityBounds :: Bounded.NumberBounds
humidityBounds = Bounded.numberBounds 0.0 100.0 Bounded.Clamps "relativeHumidity" "Relative humidity in percent"

-- | Get humidity as percent (identity).
humidityPercent :: RelativeHumidity -> Number
humidityPercent = unwrapRelativeHumidity

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // humidity // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Desert humidity (~15%).
humidityDesert :: RelativeHumidity
humidityDesert = RelativeHumidity 15.0

-- | Comfortable humidity (~45%).
humidityComfortable :: RelativeHumidity
humidityComfortable = RelativeHumidity 45.0

-- | Humid conditions (~75%).
humidityHumid :: RelativeHumidity
humidityHumid = RelativeHumidity 75.0

-- | Saturated air (100%).
humiditySaturated :: RelativeHumidity
humiditySaturated = RelativeHumidity 100.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // dew // point
-- ═════════════════════════════════════════════════════════════════════════════

-- | Dew point temperature in Celsius [-80, 40].
-- |
-- | ## Bounds Rationale
-- |
-- | - Minimum -80°C: Extremely dry air (Antarctica interior)
-- | - Maximum +40°C: Extremely humid (Persian Gulf extreme events)
-- |
-- | Dew point indicates moisture content independent of temperature.
newtype DewPoint = DewPoint Number

derive instance eqDewPoint :: Eq DewPoint
derive instance ordDewPoint :: Ord DewPoint

instance showDewPoint :: Show DewPoint where
  show (DewPoint n) = "DewPoint " <> show n <> "°C"

-- | Safe constructor with clamping.
dewPoint :: Number -> DewPoint
dewPoint n = DewPoint (Bounded.clampNumber (-80.0) 40.0 n)

-- | Unsafe constructor for known-valid values.
dewPointUnsafe :: Number -> DewPoint
dewPointUnsafe = DewPoint

-- | Extract raw value.
unwrapDewPoint :: DewPoint -> Number
unwrapDewPoint (DewPoint n) = n

-- | Valid bounds documentation.
dewPointBounds :: Bounded.NumberBounds
dewPointBounds = Bounded.numberBounds (-80.0) 40.0 Bounded.Clamps "dewPoint" "Dew point in Celsius"

-- | Get dew point in Celsius (identity).
dewPointCelsius :: DewPoint -> Number
dewPointCelsius = unwrapDewPoint

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // dew point // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Very dry air (-10°C dew point).
dewPointDry :: DewPoint
dewPointDry = DewPoint (-10.0)

-- | Comfortable (10°C dew point).
dewPointComfortable :: DewPoint
dewPointComfortable = DewPoint 10.0

-- | Humid (18°C dew point).
dewPointHumid :: DewPoint
dewPointHumid = DewPoint 18.0

-- | Oppressive (24°C+ dew point).
dewPointOppressive :: DewPoint
dewPointOppressive = DewPoint 24.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate dew point from temperature and relative humidity.
-- |
-- | Uses Magnus-Tetens approximation:
-- | Td = b × α / (a - α)
-- | where α = a × T / (b + T) + ln(RH/100)
-- | a = 17.27, b = 237.7°C
calculateDewPoint :: Temperature -> RelativeHumidity -> DewPoint
calculateDewPoint temp (RelativeHumidity rh) =
  let t = unwrapTemperature temp
      a = 17.27
      b = 237.7
      alpha = a * t / (b + t) + Number.log (rh / 100.0)
      td = b * alpha / (a - alpha)
  in dewPoint td

-- | Calculate relative humidity from temperature and dew point.
-- |
-- | RH = 100 × exp(a × Td / (b + Td)) / exp(a × T / (b + T))
calculateHumidity :: Temperature -> DewPoint -> RelativeHumidity
calculateHumidity temp (DewPoint td) =
  let t = unwrapTemperature temp
      a = 17.27
      b = 237.7
      rh = 100.0 * Number.exp (a * td / (b + td)) / Number.exp (a * t / (b + t))
  in relativeHumidity rh
