-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // weather // wind
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Wind primitives — velocity, direction, gusts, and classification.
-- |
-- | ## What is Wind?
-- |
-- | Wind is air movement caused by pressure differentials. Key parameters:
-- |
-- | - **Speed**: Velocity in m/s, km/h, knots, or mph
-- | - **Direction**: Compass bearing wind is coming FROM
-- | - **Gusts**: Brief speed increases above sustained wind
-- | - **Turbulence**: Variability in speed and direction
-- |
-- | ## Module Structure
-- |
-- | This is a leader module re-exporting from submodules:
-- | - `Wind.Speed` — Wind speed and unit conversions
-- | - `Wind.Direction` — Direction and cardinal compass points
-- | - `Wind.Beaufort` — Beaufort scale classification
-- | - `Wind.Gust` — Gust factor and turbulence intensity

module Hydrogen.Schema.Weather.Wind
  ( -- * Re-exports from Speed
    module Hydrogen.Schema.Weather.Wind.Speed
  
  -- * Re-exports from Direction
  , module Hydrogen.Schema.Weather.Wind.Direction
  
  -- * Re-exports from Beaufort
  , module Hydrogen.Schema.Weather.Wind.Beaufort
  
  -- * Re-exports from Gust
  , module Hydrogen.Schema.Weather.Wind.Gust
  
  -- * Wind Vector
  , WindVector(..)
  , windVector
  , windVectorFromComponents
  , speedFromVector
  , directionFromVector
  , uComponent
  , vComponent
  
  -- * Wind Event
  , WindEvent(..)
  , steadyWind
  , gustyWind
  , calmConditions
  
  -- * Operations
  , windChill
  , apparentTemperature
  , isGusty
  , isCalm
  , isHazardous
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (>=)
  , (||)
  , (<>)
  )

import Data.Number (sqrt, sin, cos, atan2, pow) as Number

-- Re-export all submodules
import Hydrogen.Schema.Weather.Wind.Speed
  ( WindSpeed
  , windSpeed
  , windSpeedUnsafe
  , unwrapSpeed
  , speedBounds
  , metersPerSecond
  , kilometersPerHour
  , knots
  , milesPerHour
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
  , lerp
  , pressureFromSpeed
  )

import Hydrogen.Schema.Weather.Wind.Direction
  ( WindDirection
  , windDirection
  , windDirectionUnsafe
  , unwrapDirection
  , directionBounds
  , degrees
  , radians
  , directionNorth
  , directionNorthEast
  , directionEast
  , directionSouthEast
  , directionSouth
  , directionSouthWest
  , directionWest
  , directionNorthWest
  , Cardinal(..)
  , allCardinals
  , cardinalToDegrees
  , degreesToCardinal
  , cardinalAbbreviation
  )

import Hydrogen.Schema.Weather.Wind.Beaufort
  ( BeaufortNumber
  , beaufortNumber
  , beaufortNumberUnsafe
  , unwrapBeaufort
  , beaufortBounds
  , speedToBeaufort
  , beaufortToMinSpeed
  , beaufortDescription
  , beaufortSeaCondition
  , beaufortLandCondition
  )

import Hydrogen.Schema.Weather.Wind.Gust
  ( GustFactor
  , gustFactor
  , gustFactorUnsafe
  , unwrapGustFactor
  , gustFactorBounds
  , gustNone
  , gustLight
  , gustModerate
  , gustStrong
  , gustSevere
  , TurbulenceIntensity
  , turbulenceIntensity
  , turbulenceIntensityUnsafe
  , unwrapTurbulence
  , turbulenceBounds
  , turbulenceNone
  , turbulenceLight
  , turbulenceModerate
  , turbulenceSevere
  , turbulenceExtreme
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // wind // vector
-- ═════════════════════════════════════════════════════════════════════════════

-- | Wind as a 2D vector with u (east-west) and v (north-south) components.
-- |
-- | ## Convention
-- |
-- | - u > 0: Wind blowing eastward (from west)
-- | - v > 0: Wind blowing northward (from south)
data WindVector = WindVector
  { u :: Number  -- East-west component (m/s)
  , v :: Number  -- North-south component (m/s)
  }

derive instance eqWindVector :: Eq WindVector

instance showWindVector :: Show WindVector where
  show (WindVector { u, v }) = "WindVector { u: " <> show u <> ", v: " <> show v <> " }"

-- | Create wind vector from speed and direction.
windVector :: WindSpeed -> WindDirection -> WindVector
windVector spd dir =
  let s = unwrapSpeed spd
      d = unwrapDirection dir
      rad = (d + 180.0) * 3.14159265358979323846 / 180.0  -- +180 for "from" to "to"
      u = s * Number.sin rad
      v = s * Number.cos rad
  in WindVector { u, v }

-- | Create wind vector from u, v components directly.
windVectorFromComponents :: Number -> Number -> WindVector
windVectorFromComponents u v = WindVector { u, v }

-- | Extract speed from vector.
speedFromVector :: WindVector -> WindSpeed
speedFromVector (WindVector { u, v }) =
  windSpeed (Number.sqrt (u * u + v * v))

-- | Extract direction from vector.
directionFromVector :: WindVector -> WindDirection
directionFromVector (WindVector { u, v }) =
  let rad = Number.atan2 u v
      deg = rad * 180.0 / 3.14159265358979323846
      fromDir = deg + 180.0  -- Convert "to" to "from"
  in windDirection fromDir

-- | Get u (east-west) component.
uComponent :: WindVector -> Number
uComponent (WindVector { u }) = u

-- | Get v (north-south) component.
vComponent :: WindVector -> Number
vComponent (WindVector { v }) = v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // wind // event
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete wind event with all parameters.
data WindEvent
  = SteadyWind
      { speed :: WindSpeed
      , direction :: WindDirection
      }
  | GustyWind
      { sustained :: WindSpeed
      , direction :: WindDirection
      , gustFactor_ :: GustFactor
      , turbulence :: TurbulenceIntensity
      }
  | CalmConditions

derive instance eqWindEvent :: Eq WindEvent

instance showWindEvent :: Show WindEvent where
  show (SteadyWind r) = "SteadyWind { speed: " <> show r.speed <> ", dir: " <> show r.direction <> " }"
  show (GustyWind r) = "GustyWind { sustained: " <> show r.sustained <> ", gusts: " <> show r.gustFactor_ <> " }"
  show CalmConditions = "CalmConditions"

-- | Create steady wind event.
steadyWind :: WindSpeed -> WindDirection -> WindEvent
steadyWind speed direction = SteadyWind { speed, direction }

-- | Create gusty wind event.
gustyWind :: WindSpeed -> WindDirection -> GustFactor -> TurbulenceIntensity -> WindEvent
gustyWind sustained direction gustFactor_ turbulence = 
  GustyWind { sustained, direction, gustFactor_, turbulence }

-- | Create calm conditions.
calmConditions :: WindEvent
calmConditions = CalmConditions

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate wind chill temperature (Celsius).
-- |
-- | Uses NWS/Environment Canada formula:
-- | T_wc = 13.12 + 0.6215×T - 11.37×v^0.16 + 0.3965×T×v^0.16
-- |
-- | Valid for T ≤ 10°C and v ≥ 4.8 km/h.
windChill :: Number -> WindSpeed -> Number
windChill tempC spd =
  let v = unwrapSpeed spd
      vKmh = v * 3.6
      vPow = Number.pow vKmh 0.16
  in if tempC > 10.0 || vKmh < 4.8
     then tempC  -- Formula not applicable
     else 13.12 + 0.6215 * tempC - 11.37 * vPow + 0.3965 * tempC * vPow

-- | Calculate apparent temperature (simplified heat index + wind chill).
apparentTemperature :: Number -> Number -> WindSpeed -> Number
apparentTemperature tempC humidity wind =
  if tempC < 10.0
  then windChill tempC wind
  else tempC + 0.348 * humidity - 0.7

-- | Is wind gusty (gust factor > 1.3)?
isGusty :: WindEvent -> Boolean
isGusty (GustyWind r) = unwrapGustFactor r.gustFactor_ > 1.3
isGusty _ = false

-- | Is wind calm (Beaufort 0)?
isCalm :: WindEvent -> Boolean
isCalm CalmConditions = true
isCalm (SteadyWind r) = unwrapSpeed r.speed < 0.5
isCalm (GustyWind r) = unwrapSpeed r.sustained < 0.5

-- | Is wind hazardous (Beaufort 8+)?
isHazardous :: WindEvent -> Boolean
isHazardous CalmConditions = false
isHazardous (SteadyWind r) = unwrapSpeed r.speed >= 17.2
isHazardous (GustyWind r) = 
  let gustSpeed = unwrapSpeed r.sustained * unwrapGustFactor r.gustFactor_
  in gustSpeed >= 17.2
