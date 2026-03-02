-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                 // hydrogen // schema // weather // precipitation // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Precipitation type classification.
-- |
-- | Each type has distinct:
-- | - Formation mechanism
-- | - Visual appearance
-- | - Terminal velocity
-- | - Accumulation behavior
-- | - Sound profile on impact

module Hydrogen.Schema.Weather.Precipitation.Types
  ( -- * Precipitation Type
    PrecipitationType(Rain, Drizzle, Snow, Sleet, FreezingRain, Hail, Graupel, IcePellets, MixedRainSnow, MixedSleet)
  , allPrecipitationTypes
  , isLiquid
  , isFrozen
  , isMixed
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // precipitation // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Classification of precipitation by physical form.
data PrecipitationType
  = Rain          -- ^ Liquid drops (diameter 0.5-5mm)
  | Drizzle       -- ^ Fine liquid drops (< 0.5mm)
  | Snow          -- ^ Ice crystals (various forms)
  | Sleet         -- ^ Ice pellets (frozen rain)
  | FreezingRain  -- ^ Supercooled liquid
  | Hail          -- ^ Layered ice spheres
  | Graupel       -- ^ Soft rime pellets
  | IcePellets    -- ^ Small clear ice
  | MixedRainSnow -- ^ Rain/snow mix
  | MixedSleet    -- ^ Sleet/freezing rain mix

derive instance eqPrecipitationType :: Eq PrecipitationType
derive instance ordPrecipitationType :: Ord PrecipitationType

instance showPrecipitationType :: Show PrecipitationType where
  show Rain = "Rain"
  show Drizzle = "Drizzle"
  show Snow = "Snow"
  show Sleet = "Sleet"
  show FreezingRain = "FreezingRain"
  show Hail = "Hail"
  show Graupel = "Graupel"
  show IcePellets = "IcePellets"
  show MixedRainSnow = "MixedRainSnow"
  show MixedSleet = "MixedSleet"

-- | All precipitation types for enumeration.
allPrecipitationTypes :: Array PrecipitationType
allPrecipitationTypes =
  [ Rain
  , Drizzle
  , Snow
  , Sleet
  , FreezingRain
  , Hail
  , Graupel
  , IcePellets
  , MixedRainSnow
  , MixedSleet
  ]

-- | Is this liquid precipitation?
isLiquid :: PrecipitationType -> Boolean
isLiquid Rain = true
isLiquid Drizzle = true
isLiquid FreezingRain = true  -- Liquid until contact
isLiquid _ = false

-- | Is this frozen precipitation?
isFrozen :: PrecipitationType -> Boolean
isFrozen Snow = true
isFrozen Sleet = true
isFrozen Hail = true
isFrozen Graupel = true
isFrozen IcePellets = true
isFrozen _ = false

-- | Is this mixed precipitation?
isMixed :: PrecipitationType -> Boolean
isMixed MixedRainSnow = true
isMixed MixedSleet = true
isMixed _ = false
