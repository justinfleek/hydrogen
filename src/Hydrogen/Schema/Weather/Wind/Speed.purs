-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // weather // wind // speed
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Wind speed primitives.
-- |
-- | ## Physical Bounds
-- |
-- | - Minimum 0: Calm conditions
-- | - Maximum 150: Above highest recorded gusts (~113 m/s)
-- |
-- | SI unit (m/s) is canonical; conversions available.

module Hydrogen.Schema.Weather.Wind.Speed
  ( -- * Wind Speed
    WindSpeed
  , windSpeed
  , windSpeedUnsafe
  , unwrapSpeed
  , speedBounds
  
  -- * Unit Conversions
  , metersPerSecond
  , kilometersPerHour
  , knots
  , milesPerHour
  
  -- * Constants
  , speedCalm
  , speedLightAir
  , speedLightBreeze
  , speedGentleBreeze
  , speedModerateBreeze
  , speedFreshBreeze
  , speedStrongBreeze
  , speedNearGale
  , speedGale
  , speedStrongGale
  , speedStorm
  , speedViolentStorm
  , speedHurricane
  
  -- * Operations
  , lerp
  , pressureFromSpeed
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (+)
  , (-)
  , (*)
  , (<>)
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // wind // speed
-- ═════════════════════════════════════════════════════════════════════════════

-- | Wind speed in m/s [0, 150].
newtype WindSpeed = WindSpeed Number

derive instance eqWindSpeed :: Eq WindSpeed
derive instance ordWindSpeed :: Ord WindSpeed

instance showWindSpeed :: Show WindSpeed where
  show (WindSpeed n) = "WindSpeed " <> show n <> " m/s"

-- | Safe constructor with clamping.
windSpeed :: Number -> WindSpeed
windSpeed n = WindSpeed (Bounded.clampNumber 0.0 150.0 n)

-- | Unsafe constructor for known-valid values.
windSpeedUnsafe :: Number -> WindSpeed
windSpeedUnsafe = WindSpeed

-- | Extract raw value.
unwrapSpeed :: WindSpeed -> Number
unwrapSpeed (WindSpeed n) = n

-- | Valid bounds documentation.
speedBounds :: Bounded.NumberBounds
speedBounds = Bounded.numberBounds 0.0 150.0 Bounded.Clamps "windSpeed" "Wind speed in m/s"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // unit // conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get speed in m/s (identity, canonical unit).
metersPerSecond :: WindSpeed -> Number
metersPerSecond = unwrapSpeed

-- | Convert to km/h (× 3.6).
kilometersPerHour :: WindSpeed -> Number
kilometersPerHour (WindSpeed n) = n * 3.6

-- | Convert to knots (× 1.944).
knots :: WindSpeed -> Number
knots (WindSpeed n) = n * 1.94384

-- | Convert to mph (× 2.237).
milesPerHour :: WindSpeed -> Number
milesPerHour (WindSpeed n) = n * 2.23694

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calm (< 0.5 m/s, Beaufort 0).
speedCalm :: WindSpeed
speedCalm = WindSpeed 0.3

-- | Light air (0.5-1.5 m/s, Beaufort 1).
speedLightAir :: WindSpeed
speedLightAir = WindSpeed 1.0

-- | Light breeze (1.6-3.3 m/s, Beaufort 2).
speedLightBreeze :: WindSpeed
speedLightBreeze = WindSpeed 2.5

-- | Gentle breeze (3.4-5.4 m/s, Beaufort 3).
speedGentleBreeze :: WindSpeed
speedGentleBreeze = WindSpeed 4.4

-- | Moderate breeze (5.5-7.9 m/s, Beaufort 4).
speedModerateBreeze :: WindSpeed
speedModerateBreeze = WindSpeed 6.7

-- | Fresh breeze (8.0-10.7 m/s, Beaufort 5).
speedFreshBreeze :: WindSpeed
speedFreshBreeze = WindSpeed 9.4

-- | Strong breeze (10.8-13.8 m/s, Beaufort 6).
speedStrongBreeze :: WindSpeed
speedStrongBreeze = WindSpeed 12.3

-- | Near gale (13.9-17.1 m/s, Beaufort 7).
speedNearGale :: WindSpeed
speedNearGale = WindSpeed 15.5

-- | Gale (17.2-20.7 m/s, Beaufort 8).
speedGale :: WindSpeed
speedGale = WindSpeed 19.0

-- | Strong gale (20.8-24.4 m/s, Beaufort 9).
speedStrongGale :: WindSpeed
speedStrongGale = WindSpeed 22.6

-- | Storm (24.5-28.4 m/s, Beaufort 10).
speedStorm :: WindSpeed
speedStorm = WindSpeed 26.5

-- | Violent storm (28.5-32.6 m/s, Beaufort 11).
speedViolentStorm :: WindSpeed
speedViolentStorm = WindSpeed 30.5

-- | Hurricane (> 32.7 m/s, Beaufort 12).
speedHurricane :: WindSpeed
speedHurricane = WindSpeed 40.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Linear interpolation between two wind speeds.
lerp :: Number -> WindSpeed -> WindSpeed -> WindSpeed
lerp t (WindSpeed a) (WindSpeed b) =
  windSpeed (a + t * (b - a))

-- | Calculate dynamic pressure from wind speed (Pa).
-- |
-- | P = 0.5 × ρ × v²
-- | where ρ ≈ 1.225 kg/m³ (air at sea level, 15°C)
pressureFromSpeed :: WindSpeed -> Number
pressureFromSpeed (WindSpeed v) = 0.5 * 1.225 * v * v
