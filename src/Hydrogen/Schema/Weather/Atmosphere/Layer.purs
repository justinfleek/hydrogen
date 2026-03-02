-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                    // hydrogen // schema // weather // atmosphere // layer
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Atmospheric layer classification.
-- |
-- | The atmosphere is divided into layers by temperature profile:
-- |
-- | - **Troposphere** (0-12km): Where weather occurs
-- | - **Stratosphere** (12-50km): Contains ozone layer
-- | - **Mesosphere** (50-80km): Where meteors burn up
-- | - **Thermosphere** (80-700km): Aurora, ISS orbit
-- | - **Exosphere** (700-10000km): Transition to space

module Hydrogen.Schema.Weather.Atmosphere.Layer
  ( -- * Atmospheric Layer
    AtmosphericLayer(Troposphere, Stratosphere, Mesosphere, Thermosphere, Exosphere)
  , allAtmosphericLayers
  , layerAltitudeRange
  , layerDescription
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // atmospheric // layer
-- ═════════════════════════════════════════════════════════════════════════════

-- | Atmospheric layers by altitude.
data AtmosphericLayer
  = Troposphere    -- ^ 0-12km, weather occurs here
  | Stratosphere   -- ^ 12-50km, ozone layer
  | Mesosphere     -- ^ 50-80km, meteors burn
  | Thermosphere   -- ^ 80-700km, aurora, ISS
  | Exosphere      -- ^ 700-10000km, transition to space

derive instance eqAtmosphericLayer :: Eq AtmosphericLayer
derive instance ordAtmosphericLayer :: Ord AtmosphericLayer

instance showAtmosphericLayer :: Show AtmosphericLayer where
  show Troposphere = "Troposphere"
  show Stratosphere = "Stratosphere"
  show Mesosphere = "Mesosphere"
  show Thermosphere = "Thermosphere"
  show Exosphere = "Exosphere"

-- | All atmospheric layers for enumeration.
allAtmosphericLayers :: Array AtmosphericLayer
allAtmosphericLayers = [Troposphere, Stratosphere, Mesosphere, Thermosphere, Exosphere]

-- | Altitude range in meters (min, max).
layerAltitudeRange :: AtmosphericLayer -> { min :: Number, max :: Number }
layerAltitudeRange Troposphere = { min: 0.0, max: 12000.0 }
layerAltitudeRange Stratosphere = { min: 12000.0, max: 50000.0 }
layerAltitudeRange Mesosphere = { min: 50000.0, max: 80000.0 }
layerAltitudeRange Thermosphere = { min: 80000.0, max: 700000.0 }
layerAltitudeRange Exosphere = { min: 700000.0, max: 10000000.0 }

-- | Layer description.
layerDescription :: AtmosphericLayer -> String
layerDescription Troposphere = "Weather layer, temperature decreases with altitude"
layerDescription Stratosphere = "Ozone layer, temperature increases with altitude"
layerDescription Mesosphere = "Coldest layer, meteors burn up here"
layerDescription Thermosphere = "Hot but thin, aurora and ISS orbit here"
layerDescription Exosphere = "Transition to space, particles escape"
