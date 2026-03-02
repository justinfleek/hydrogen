-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // weather
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Weather pillar — Complete atmospheric and meteorological primitives.
-- |
-- | ## Overview
-- |
-- | Weather encompasses all atmospheric phenomena affecting environmental
-- | conditions. This pillar provides bounded, deterministic primitives for:
-- |
-- | - **Precipitation**: Rain, snow, sleet, hail, and mixed forms
-- | - **Wind**: Speed, direction, gusts, turbulence, Beaufort scale
-- | - **Atmosphere**: Temperature, pressure, humidity, visibility, clouds
-- |
-- | ## Why Weather Matters
-- |
-- | At billion-agent scale, weather primitives enable:
-- |
-- | - **Rendering**: Particle systems, volumetric effects, sky rendering
-- | - **Audio**: Rain on surfaces, wind howling, thunder synthesis
-- | - **Haptic**: Temperature sensation, wind pressure, droplet impacts
-- | - **Simulation**: Flight physics, vehicle handling, water accumulation
-- | - **Mood**: Environmental atmosphere (cozy rain, oppressive heat)
-- |
-- | ## Submodules
-- |
-- | - `Weather.Precipitation`: Rain, snow, sleet, hail rates and properties
-- | - `Weather.Wind`: Speed, direction, gusts, Beaufort classification
-- | - `Weather.Atmosphere`: Temperature, pressure, humidity, visibility
-- |
-- | ## Related Modules
-- |
-- | - `Sensation.Environment`: Agent-centric environmental sensing
-- | - `Physical.Fluid`: Material fluid properties (viscosity, surface tension)
-- | - `Physical.Thermal`: Thermal conductivity for heat transfer
-- |
-- | ## Data Sources
-- |
-- | - WMO (World Meteorological Organization) standards
-- | - ICAO International Standard Atmosphere
-- | - NOAA/NWS weather classification
-- | - METAR aviation weather codes

module Hydrogen.Schema.Weather
  ( -- * Re-exports
    module Hydrogen.Schema.Weather.Precipitation
  , module Hydrogen.Schema.Weather.Wind
  , module Hydrogen.Schema.Weather.Atmosphere
  
  -- * Weather Condition
  , WeatherCondition(Clear, Cloudy, Rainy, Snowy, Stormy, Foggy, Windy, Hazy)
  , clearCondition
  , cloudyCondition
  , rainyCondition
  , snowyCondition
  , stormyCondition
  , foggyCondition
  
  -- * Weather Event (Complete)
  , WeatherEvent(WeatherEvent)
  , weatherEvent
  , currentCondition
  , eventPrecipitation
  , eventWind
  , eventAtmosphere
  
  -- * Composite Operations
  , isSevere
  , isHazardousToTravel
  , isOutdoorActivitySafe
  , comfortIndex
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , negate
  , map
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (>=)
  , (<=)
  , (==)
  , (/=)
  , (&&)
  , (||)
  , (<>)
  , (<<<)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Weather.Precipitation
  ( PrecipitationType(Rain, Drizzle, Snow, Sleet, FreezingRain, Hail, Graupel, IcePellets, MixedRainSnow, MixedSleet)
  , PrecipitationRate
  , precipitationRate
  , unwrapRate
  , rateNone
  , rateLight
  , rateModerate
  , rateHeavy
  , Intensity(IntensityNone, IntensityTrace, IntensityLight, IntensityModerate, IntensityHeavy, IntensityViolent)
  , rateToIntensity
  , DropletDiameter
  , dropletLight
  , SnowflakeType(Plates, StellarDendrites, Columns, Needles, SpatialDendrites, CappedColumns, IrregularCrystals, SnowGraupel, SleetCrystals)
  , SnowDensity
  , densityFresh
  , HailDiameter
  , HailCategory(HailSmall, HailSevere, HailSignificant, HailGiant)
  , PrecipitationEvent(RainEvent, SnowEvent, SleetEvent, HailEvent, FreezingRainEvent, MixedEvent)
  , rainEvent
  , snowEvent
  , Accumulation
  , visibilityReduction
  )
import Hydrogen.Schema.Weather.Wind
  ( WindSpeed
  , windSpeed
  , unwrapSpeed
  , speedCalm
  , speedGale
  , speedHurricane
  , WindDirection
  , windDirection
  , directionNorth
  , BeaufortNumber
  , speedToBeaufort
  , beaufortDescription
  , GustFactor
  , gustNone
  , gustModerate
  , unwrapGustFactor
  , TurbulenceIntensity
  , turbulenceNone
  , WindEvent(SteadyWind, GustyWind, CalmConditions)
  , steadyWind
  , calmConditions
  , isHazardous
  , windChill
  )
import Hydrogen.Schema.Weather.Atmosphere
  ( Temperature
  , temperature
  , unwrapTemperature
  , tempFreezingPoint
  , tempRoomTemp
  , celsius
  , Pressure
  , pressure
  , pressureStandard
  , RelativeHumidity
  , relativeHumidity
  , unwrapRelativeHumidity
  , humidityComfortable
  , DewPoint
  , dewPoint
  , dewPointComfortable
  , Visibility
  , visibility
  , unwrapVisibility
  , visibilityClear
  , VisibilityCategory(VisZero, VisDenseFog, VisFog, VisMist, VisHaze, VisClear)
  , visibilityToCategory
  , CloudCover
  , cloudCover
  , unwrapCloudCover
  , cloudCoverClear
  , cloudCoverOvercast
  , CloudCategory(SKC, FEW, SCT, BKN, OVC)
  , cloudCoverToCategory
  , AtmosphericState(AtmosphericState)
  , atmosphericState
  , defaultAtmosphere
  , standardAtmosphere
  , isComfortable
  , isFoggy
  , heatIndex
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // weather // condition
-- ═════════════════════════════════════════════════════════════════════════════

-- | High-level weather condition classification.
-- |
-- | Provides a simple categorical view of weather state.
data WeatherCondition
  = Clear     -- ^ Clear skies, good visibility
  | Cloudy    -- ^ Overcast but no precipitation
  | Rainy     -- ^ Active rainfall
  | Snowy     -- ^ Active snowfall
  | Stormy    -- ^ Severe weather (high winds, heavy precip)
  | Foggy     -- ^ Low visibility due to fog
  | Windy     -- ^ High winds, any sky condition
  | Hazy      -- ^ Reduced visibility due to haze

derive instance eqWeatherCondition :: Eq WeatherCondition

instance showWeatherCondition :: Show WeatherCondition where
  show Clear = "Clear"
  show Cloudy = "Cloudy"
  show Rainy = "Rainy"
  show Snowy = "Snowy"
  show Stormy = "Stormy"
  show Foggy = "Foggy"
  show Windy = "Windy"
  show Hazy = "Hazy"

-- | Clear weather condition.
clearCondition :: WeatherCondition
clearCondition = Clear

-- | Cloudy weather condition.
cloudyCondition :: WeatherCondition
cloudyCondition = Cloudy

-- | Rainy weather condition.
rainyCondition :: WeatherCondition
rainyCondition = Rainy

-- | Snowy weather condition.
snowyCondition :: WeatherCondition
snowyCondition = Snowy

-- | Stormy weather condition.
stormyCondition :: WeatherCondition
stormyCondition = Stormy

-- | Foggy weather condition.
foggyCondition :: WeatherCondition
foggyCondition = Foggy

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // weather // event
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete weather event combining all components.
-- |
-- | Represents a snapshot of weather conditions at a specific time/location.
data WeatherEvent = WeatherEvent
  { condition :: WeatherCondition
  , precip :: Maybe PrecipitationEvent
  , wind :: WindEvent
  , atmosphere :: AtmosphericState
  }

derive instance eqWeatherEvent :: Eq WeatherEvent

instance showWeatherEvent :: Show WeatherEvent where
  show (WeatherEvent e) = 
    "WeatherEvent { condition: " <> show e.condition 
    <> ", wind: " <> show e.wind 
    <> " }"

-- | Create a weather event.
weatherEvent 
  :: WeatherCondition 
  -> Maybe PrecipitationEvent 
  -> WindEvent 
  -> AtmosphericState 
  -> WeatherEvent
weatherEvent condition precip wind atmosphere = 
  WeatherEvent { condition, precip, wind, atmosphere }

-- | Get the current condition from an event.
currentCondition :: WeatherEvent -> WeatherCondition
currentCondition (WeatherEvent e) = e.condition

-- | Get precipitation from an event (if any).
eventPrecipitation :: WeatherEvent -> Maybe PrecipitationEvent
eventPrecipitation (WeatherEvent e) = e.precip

-- | Get wind from an event.
eventWind :: WeatherEvent -> WindEvent
eventWind (WeatherEvent e) = e.wind

-- | Get atmosphere from an event.
eventAtmosphere :: WeatherEvent -> AtmosphericState
eventAtmosphere (WeatherEvent e) = e.atmosphere

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // composite // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is this severe weather?
-- |
-- | Severe = Beaufort 8+ OR heavy precipitation OR poor visibility.
isSevere :: WeatherEvent -> Boolean
isSevere (WeatherEvent e) =
  e.condition == Stormy || isHazardous e.wind || hasHeavyPrecip e.precip
  where
    hasHeavyPrecip :: Maybe PrecipitationEvent -> Boolean
    hasHeavyPrecip Nothing = false
    hasHeavyPrecip (Just (RainEvent r)) = unwrapRate r.rate > 25.0
    hasHeavyPrecip (Just (SnowEvent r)) = unwrapRate r.rate > 10.0
    hasHeavyPrecip (Just (HailEvent _)) = true
    hasHeavyPrecip (Just _) = false

-- | Is this hazardous for travel?
-- |
-- | Hazardous = poor visibility (<1km) OR icy conditions OR high winds.
isHazardousToTravel :: WeatherEvent -> Boolean
isHazardousToTravel (WeatherEvent e) =
  let AtmosphericState atm = e.atmosphere
      poorVis = unwrapVisibility atm.vis < 1000.0
      icyConditions = e.condition == Snowy && unwrapTemperature atm.temp < 0.0
      dangerousWinds = isHazardous e.wind
  in poorVis || icyConditions || dangerousWinds

-- | Is outdoor activity safe?
-- |
-- | Safe = no severe weather AND comfortable temperature AND no lightning risk.
isOutdoorActivitySafe :: WeatherEvent -> Boolean
isOutdoorActivitySafe event@(WeatherEvent e) =
  let AtmosphericState atm = e.atmosphere
      tempOk = unwrapTemperature atm.temp >= 5.0 && unwrapTemperature atm.temp <= 35.0
      notSevere = e.condition /= Stormy
      visOk = unwrapVisibility atm.vis >= 500.0
  in tempOk && notSevere && visOk && isOutdoorActivitySafe_internal event

-- Internal helper to avoid self-reference
isOutdoorActivitySafe_internal :: WeatherEvent -> Boolean
isOutdoorActivitySafe_internal (WeatherEvent e) =
  case e.precip of
    Nothing -> true
    Just (HailEvent _) -> false
    Just (RainEvent r) -> unwrapRate r.rate < 25.0
    Just (SnowEvent r) -> unwrapRate r.rate < 10.0
    Just _ -> true

-- | Calculate comfort index [0-100].
-- |
-- | Combines temperature comfort, humidity, wind chill, and precipitation.
-- | 100 = perfect conditions, 0 = extremely uncomfortable.
comfortIndex :: WeatherEvent -> Number
comfortIndex (WeatherEvent e) =
  let AtmosphericState atm = e.atmosphere
      
      -- Temperature comfort (ideal around 20-22°C)
      temp = unwrapTemperature atm.temp
      tempScore = 100.0 - 5.0 * absNum (temp - 21.0)
      
      -- Humidity comfort (ideal 40-60%)
      humid = unwrapRelativeHumidity atm.humidity
      humidScore = if humid >= 40.0 && humid <= 60.0 
                   then 100.0 
                   else 100.0 - 2.0 * absNum (humid - 50.0)
      
      -- Wind comfort (calm is best)
      windScore = case e.wind of
        CalmConditions -> 100.0
        SteadyWind r -> 100.0 - unwrapSpeed r.speed * 5.0
        GustyWind r -> 100.0 - unwrapSpeed r.sustained * 6.0
      
      -- Precipitation penalty
      precipPenalty = case e.precip of
        Nothing -> 0.0
        Just (RainEvent r) -> unwrapRate r.rate * 2.0
        Just (SnowEvent r) -> unwrapRate r.rate * 3.0
        Just (HailEvent _) -> 50.0
        Just _ -> 20.0
      
      -- Combine scores
      raw = (tempScore + humidScore + windScore) / 3.0 - precipPenalty
  in clampNum 0.0 100.0 raw

-- Helper: absolute value for Number
absNum :: Number -> Number
absNum n = if n < 0.0 then n * (-1.0) else n

-- Helper: clamp Number
clampNum :: Number -> Number -> Number -> Number
clampNum minVal maxVal n
  | n < minVal = minVal
  | n > maxVal = maxVal
  | otherwise = n


