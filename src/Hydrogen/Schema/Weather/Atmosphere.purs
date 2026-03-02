-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // weather // atmosphere
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Atmospheric primitives — pressure, humidity, temperature, visibility.
-- |
-- | ## What is Atmosphere?
-- |
-- | Atmospheric state encompasses:
-- |
-- | - **Temperature**: Air temperature at measurement height
-- | - **Pressure**: Barometric pressure (absolute and sea-level adjusted)
-- | - **Humidity**: Water vapor content (relative and absolute)
-- | - **Dew Point**: Temperature at which condensation occurs
-- | - **Visibility**: Distance at which objects can be discerned
-- | - **Cloud Cover**: Sky obscuration percentage
-- |
-- | ## Why This Matters
-- |
-- | At billion-agent scale, atmospheric state determines:
-- | - Rendering (fog, haze, sky color, cloud rendering)
-- | - Audio (sound propagation, muffling)
-- | - Haptic (humidity feel, temperature sensation)
-- | - Simulation (flight physics, thermal updrafts)
-- | - Mood (oppressive humidity, crisp cold, hazy warmth)
-- |
-- | ## Module Structure
-- |
-- | This is a leader module re-exporting from submodules:
-- | - `Atmosphere.Temperature` — Temperature type and conversions
-- | - `Atmosphere.Pressure` — Barometric pressure
-- | - `Atmosphere.Humidity` — Relative humidity and dew point
-- | - `Atmosphere.Visibility` — Visibility distance and categories
-- | - `Atmosphere.CloudCover` — Cloud cover and METAR categories
-- | - `Atmosphere.Layer` — Atmospheric layer classification

module Hydrogen.Schema.Weather.Atmosphere
  ( -- * Re-exports from Temperature
    module Hydrogen.Schema.Weather.Atmosphere.Temperature
    
  -- * Re-exports from Pressure
  , module Hydrogen.Schema.Weather.Atmosphere.Pressure
  
  -- * Re-exports from Humidity
  , module Hydrogen.Schema.Weather.Atmosphere.Humidity
  
  -- * Re-exports from Visibility
  , module Hydrogen.Schema.Weather.Atmosphere.Visibility
  
  -- * Re-exports from CloudCover
  , module Hydrogen.Schema.Weather.Atmosphere.CloudCover
  
  -- * Re-exports from Layer
  , module Hydrogen.Schema.Weather.Atmosphere.Layer
  
  -- * Atmospheric State
  , AtmosphericState(AtmosphericState)
  , atmosphericState
  , defaultAtmosphere
  , standardAtmosphere
  
  -- * Composite Operations
  , densityAltitude
  , soundSpeed
  , airDensity
  , heatIndex
  , humidex
  , isComfortable
  , isFoggy
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , negate
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (<=)
  , (>=)
  , (&&)
  , (<>)
  )

import Data.Number (sqrt, exp) as Number

-- Re-export all submodules
import Hydrogen.Schema.Weather.Atmosphere.Temperature 
  ( Temperature
  , temperature
  , temperatureUnsafe
  , unwrapTemperature
  , temperatureBounds
  , celsius
  , fahrenheit
  , kelvin
  , tempAbsoluteZero
  , tempFreezingPoint
  , tempRoomTemp
  , tempBodyTemp
  , tempBoilingPoint
  , tempRecordLow
  , tempRecordHigh
  , lerp
  )

import Hydrogen.Schema.Weather.Atmosphere.Pressure
  ( Pressure
  , pressure
  , pressureUnsafe
  , unwrapPressure
  , pressureBounds
  , hectopascals
  , millibars
  , atmospheres
  , inchesOfMercury
  , mmOfMercury
  , pressureStandard
  , pressureRecordLow
  , pressureRecordHigh
  , pressureEverest
  , pressureDeadSea
  , pressureAltitude
  )

import Hydrogen.Schema.Weather.Atmosphere.Humidity
  ( RelativeHumidity
  , relativeHumidity
  , relativeHumidityUnsafe
  , unwrapRelativeHumidity
  , humidityBounds
  , humidityPercent
  , humidityDesert
  , humidityComfortable
  , humidityHumid
  , humiditySaturated
  , DewPoint
  , dewPoint
  , dewPointUnsafe
  , unwrapDewPoint
  , dewPointBounds
  , dewPointCelsius
  , dewPointDry
  , dewPointComfortable
  , dewPointHumid
  , dewPointOppressive
  , calculateDewPoint
  , calculateHumidity
  )

import Hydrogen.Schema.Weather.Atmosphere.Visibility
  ( Visibility
  , visibility
  , visibilityUnsafe
  , unwrapVisibility
  , visibilityBounds
  , visibilityMeters
  , visibilityKilometers
  , visibilityMiles
  , visibilityZero
  , visibilityDenseFog
  , visibilityFog
  , visibilityMist
  , visibilityHaze
  , visibilityClear
  , visibilityUnlimited
  , VisibilityCategory(VisZero, VisDenseFog, VisFog, VisMist, VisHaze, VisClear)
  , allVisibilityCategories
  , visibilityToCategory
  , categoryToMinVisibility
  )

import Hydrogen.Schema.Weather.Atmosphere.CloudCover
  ( CloudCover
  , cloudCover
  , cloudCoverUnsafe
  , unwrapCloudCover
  , cloudCoverBounds
  , cloudCoverPercent
  , cloudCoverOktas
  , cloudCoverClear
  , cloudCoverFewClouds
  , cloudCoverScattered
  , cloudCoverBroken
  , cloudCoverOvercast
  , CloudCategory(SKC, FEW, SCT, BKN, OVC)
  , allCloudCategories
  , cloudCoverToCategory
  , categoryDescription
  )

import Hydrogen.Schema.Weather.Atmosphere.Layer
  ( AtmosphericLayer(Troposphere, Stratosphere, Mesosphere, Thermosphere, Exosphere)
  , allAtmosphericLayers
  , layerAltitudeRange
  , layerDescription
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // atmospheric // state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete atmospheric state.
data AtmosphericState = AtmosphericState
  { temp :: Temperature
  , press :: Pressure
  , humidity :: RelativeHumidity
  , dewPt :: DewPoint
  , vis :: Visibility
  , clouds :: CloudCover
  }

derive instance eqAtmosphericState :: Eq AtmosphericState

instance showAtmosphericState :: Show AtmosphericState where
  show (AtmosphericState s) = 
    "AtmosphericState { temp: " <> show s.temp 
    <> ", pressure: " <> show s.press 
    <> ", humidity: " <> show s.humidity 
    <> " }"

-- | Create atmospheric state.
atmosphericState 
  :: Temperature 
  -> Pressure 
  -> RelativeHumidity 
  -> DewPoint 
  -> Visibility 
  -> CloudCover 
  -> AtmosphericState
atmosphericState temp press hum dewPt vis clouds = 
  AtmosphericState { temp, press, humidity: hum, dewPt, vis, clouds }

-- | Default comfortable atmosphere.
defaultAtmosphere :: AtmosphericState
defaultAtmosphere = AtmosphericState
  { temp: tempRoomTemp
  , press: pressureStandard
  , humidity: humidityComfortable
  , dewPt: dewPointComfortable
  , vis: visibilityClear
  , clouds: cloudCoverFewClouds
  }

-- | ICAO International Standard Atmosphere (ISA) at sea level.
standardAtmosphere :: AtmosphericState
standardAtmosphere = AtmosphericState
  { temp: temperature 15.0  -- 15°C
  , press: pressureStandard  -- 1013.25 hPa
  , humidity: relativeHumidity 0.0  -- ISA assumes dry air
  , dewPt: dewPoint (-40.0)  -- Very low for dry air
  , vis: visibilityUnlimited
  , clouds: cloudCoverClear
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // composite // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate density altitude in meters.
-- |
-- | Density altitude = pressure altitude + 120 × (ISA_temp - actual_temp)
-- | where ISA_temp = 15 - 0.00198 × pressure_altitude
densityAltitude :: Pressure -> Temperature -> Number
densityAltitude press temp =
  let pa = pressureAltitude press
      isaTemp = 15.0 - 0.00198 * pa
      actualTemp = unwrapTemperature temp
  in pa + 120.0 * (actualTemp - isaTemp)

-- | Calculate speed of sound in m/s.
-- |
-- | c = 331.3 × √(1 + T/273.15)
soundSpeed :: Temperature -> Number
soundSpeed temp =
  let t = unwrapTemperature temp
  in 331.3 * Number.sqrt (1.0 + t / 273.15)

-- | Calculate air density in kg/m³.
-- |
-- | ρ = P / (R × T) where R = 287.05 J/(kg·K)
airDensity :: Pressure -> Temperature -> Number
airDensity press temp =
  let p = unwrapPressure press
      t = unwrapTemperature temp
  in (p * 100.0) / (287.05 * (t + 273.15))

-- | Calculate heat index (feels-like temperature) in Celsius.
-- |
-- | Uses Rothfusz regression equation.
-- | Valid for T > 27°C and RH > 40%.
heatIndex :: Temperature -> RelativeHumidity -> Temperature
heatIndex temp rh =
  let t = unwrapTemperature temp
      h = unwrapRelativeHumidity rh
  in if t < 27.0
     then temp  -- Formula not applicable
     else
       -- Simplified heat index (Steadman approximation)
       let hi = t + 0.5 * (h - 40.0) / 60.0 * (t - 27.0)
       in temperature hi

-- | Calculate humidex (Canadian "feels like" temperature).
-- |
-- | Humidex = T + 5/9 × (e - 10)
-- | where e = 6.11 × exp(5417.7530 × (1/273.16 - 1/Td))
humidex :: Temperature -> DewPoint -> Temperature
humidex temp dp =
  let t = unwrapTemperature temp
      td = unwrapDewPoint dp
      tdK = td + 273.15
      e = 6.11 * Number.exp (5417.7530 * (1.0 / 273.16 - 1.0 / tdK))
      h = t + 5.0 / 9.0 * (e - 10.0)
  in temperature h

-- | Is the atmospheric state comfortable?
-- |
-- | Comfortable: 18-26°C, 30-60% humidity, good visibility.
isComfortable :: AtmosphericState -> Boolean
isComfortable (AtmosphericState s) =
  let t = unwrapTemperature s.temp
      h = unwrapRelativeHumidity s.humidity
      v = unwrapVisibility s.vis
  in t >= 18.0 && t <= 26.0 && h >= 30.0 && h <= 60.0 && v >= 5000.0

-- | Is there fog (visibility < 1000m)?
isFoggy :: AtmosphericState -> Boolean
isFoggy (AtmosphericState s) = unwrapVisibility s.vis < 1000.0
