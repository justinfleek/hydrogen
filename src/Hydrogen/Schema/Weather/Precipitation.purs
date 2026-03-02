-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // schema // weather // precipitation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Precipitation primitives — rain, snow, sleet, hail, and mixed forms.
-- |
-- | ## What is Precipitation?
-- |
-- | Precipitation is water falling from the atmosphere. Its form depends on
-- | temperature profile through the atmospheric column:
-- |
-- | - **Rain**: Liquid drops (T > 0C at surface)
-- | - **Snow**: Ice crystals (T < 0C entire column)
-- | - **Sleet**: Ice pellets (freezes falling through cold layer)
-- | - **Freezing rain**: Supercooled liquid (freezes on contact)
-- | - **Hail**: Layered ice balls (convective updrafts)
-- | - **Graupel**: Soft ice pellets (rime accretion)
-- |
-- | ## Module Structure
-- |
-- | This is a leader module re-exporting from submodules:
-- | - `Precipitation.Types` — Precipitation type classification
-- | - `Precipitation.Rate` — Precipitation rate and intensity
-- | - `Precipitation.Rain` — Raindrop diameter
-- | - `Precipitation.Snow` — Snowflake types and density
-- | - `Precipitation.Hail` — Hail size and classification

module Hydrogen.Schema.Weather.Precipitation
  ( -- * Re-exports from Types
    module Hydrogen.Schema.Weather.Precipitation.Types
  
  -- * Re-exports from Rate
  , module Hydrogen.Schema.Weather.Precipitation.Rate
  
  -- * Re-exports from Rain
  , module Hydrogen.Schema.Weather.Precipitation.Rain
  
  -- * Re-exports from Snow
  , module Hydrogen.Schema.Weather.Precipitation.Snow
  
  -- * Re-exports from Hail
  , module Hydrogen.Schema.Weather.Precipitation.Hail
  
  -- * Precipitation Event
  , PrecipitationEvent(RainEvent, SnowEvent, SleetEvent, HailEvent, FreezingRainEvent, MixedEvent)
  , rainEvent
  , snowEvent
  , sleetEvent
  , hailEvent
  , freezingRainEvent
  , mixedEvent
  
  -- * Accumulation
  , Accumulation
  , accumulation
  , accumulationUnsafe
  , unwrapAccumulation
  , accumulationBounds
  , accumulationMm
  
  -- * Operations
  , waterEquivalent
  , visibilityReduction
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  )

import Hydrogen.Schema.Bounded as Bounded

-- Re-export all submodules
import Hydrogen.Schema.Weather.Precipitation.Types
  ( PrecipitationType(Rain, Drizzle, Snow, Sleet, FreezingRain, Hail, Graupel, IcePellets, MixedRainSnow, MixedSleet)
  , allPrecipitationTypes
  , isLiquid
  , isFrozen
  , isMixed
  )

import Hydrogen.Schema.Weather.Precipitation.Rate
  ( PrecipitationRate
  , precipitationRate
  , precipitationRateUnsafe
  , unwrapRate
  , rateBounds
  , mmPerHour
  , inchesPerHour
  , rateNone
  , rateTrace
  , rateLight
  , rateModerate
  , rateHeavy
  , rateViolent
  , rateTorrential
  , Intensity(IntensityNone, IntensityTrace, IntensityLight, IntensityModerate, IntensityHeavy, IntensityViolent)
  , allIntensities
  , rateToIntensity
  , intensityToMinRate
  , lerp
  )

import Hydrogen.Schema.Weather.Precipitation.Rain
  ( DropletDiameter
  , dropletDiameter
  , dropletDiameterUnsafe
  , unwrapDroplet
  , dropletBounds
  , millimeters
  , dropletMist
  , dropletDrizzle
  , dropletLight
  , dropletModerate
  , dropletHeavy
  , terminalVelocity
  , impactEnergy
  )

import Hydrogen.Schema.Weather.Precipitation.Snow
  ( SnowflakeType(Plates, StellarDendrites, Columns, Needles, SpatialDendrites, CappedColumns, IrregularCrystals, SnowGraupel, SleetCrystals)
  , allSnowflakeTypes
  , snowflakeDescription
  , SnowDensity
  , snowDensity
  , snowDensityUnsafe
  , unwrapSnowDensity
  , snowDensityBounds
  , kgPerCubicMeter
  , densityPowder
  , densityFresh
  , densitySettled
  , densityWet
  , densityCompacted
  , densityIce
  )

import Hydrogen.Schema.Weather.Precipitation.Hail
  ( HailDiameter
  , hailDiameter
  , hailDiameterUnsafe
  , unwrapHail
  , hailBounds
  , hailMillimeters
  , hailPea
  , hailMarble
  , hailGolfBall
  , hailTennisBall
  , hailSoftball
  , HailCategory(HailSmall, HailSevere, HailSignificant, HailGiant)
  , allHailCategories
  , hailToCategory
  , categoryToMinDiameter
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // precipitation // event
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete precipitation event with type-specific parameters.
data PrecipitationEvent
  = RainEvent
      { rate :: PrecipitationRate
      , dropletSize :: DropletDiameter
      }
  | SnowEvent
      { rate :: PrecipitationRate  -- Water equivalent
      , snowflake :: SnowflakeType
      , density :: SnowDensity
      }
  | SleetEvent
      { rate :: PrecipitationRate
      }
  | HailEvent
      { rate :: PrecipitationRate
      , size :: HailDiameter
      }
  | FreezingRainEvent
      { rate :: PrecipitationRate
      , dropletSize :: DropletDiameter
      }
  | MixedEvent
      { rainRate :: PrecipitationRate
      , snowRate :: PrecipitationRate
      }

derive instance eqPrecipitationEvent :: Eq PrecipitationEvent

instance showPrecipitationEvent :: Show PrecipitationEvent where
  show (RainEvent r) = "RainEvent { rate: " <> show r.rate <> ", droplet: " <> show r.dropletSize <> " }"
  show (SnowEvent r) = "SnowEvent { rate: " <> show r.rate <> ", type: " <> show r.snowflake <> " }"
  show (SleetEvent r) = "SleetEvent { rate: " <> show r.rate <> " }"
  show (HailEvent r) = "HailEvent { rate: " <> show r.rate <> ", size: " <> show r.size <> " }"
  show (FreezingRainEvent r) = "FreezingRainEvent { rate: " <> show r.rate <> " }"
  show (MixedEvent r) = "MixedEvent { rain: " <> show r.rainRate <> ", snow: " <> show r.snowRate <> " }"

-- | Create a rain event.
rainEvent :: PrecipitationRate -> DropletDiameter -> PrecipitationEvent
rainEvent rate dropletSize = RainEvent { rate, dropletSize }

-- | Create a snow event.
snowEvent :: PrecipitationRate -> SnowflakeType -> SnowDensity -> PrecipitationEvent
snowEvent rate snowflake density = SnowEvent { rate, snowflake, density }

-- | Create a sleet event.
sleetEvent :: PrecipitationRate -> PrecipitationEvent
sleetEvent rate = SleetEvent { rate }

-- | Create a hail event.
hailEvent :: PrecipitationRate -> HailDiameter -> PrecipitationEvent
hailEvent rate size = HailEvent { rate, size }

-- | Create a freezing rain event.
freezingRainEvent :: PrecipitationRate -> DropletDiameter -> PrecipitationEvent
freezingRainEvent rate dropletSize = FreezingRainEvent { rate, dropletSize }

-- | Create a mixed precipitation event.
mixedEvent :: PrecipitationRate -> PrecipitationRate -> PrecipitationEvent
mixedEvent rainRate snowRate = MixedEvent { rainRate, snowRate }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // accumulation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Precipitation accumulation in mm [0, 5000].
-- |
-- | ## Bounds Rationale
-- |
-- | - Minimum 0: No accumulation
-- | - Maximum 5000: 5 meters of snow or 200 inches (extreme seasonal)
newtype Accumulation = Accumulation Number

derive instance eqAccumulation :: Eq Accumulation

instance showAccumulation :: Show Accumulation where
  show (Accumulation n) = "Accumulation " <> show n <> " mm"

-- | Safe constructor with clamping.
accumulation :: Number -> Accumulation
accumulation n = Accumulation (Bounded.clampNumber 0.0 5000.0 n)

-- | Unsafe constructor for known-valid values.
accumulationUnsafe :: Number -> Accumulation
accumulationUnsafe = Accumulation

-- | Extract raw value.
unwrapAccumulation :: Accumulation -> Number
unwrapAccumulation (Accumulation n) = n

-- | Valid bounds documentation.
accumulationBounds :: Bounded.NumberBounds
accumulationBounds = Bounded.numberBounds 0.0 5000.0 Bounded.Clamps "accumulation" "Precipitation accumulation in mm"

-- | Get accumulation in mm (identity).
accumulationMm :: Accumulation -> Number
accumulationMm = unwrapAccumulation

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert snow accumulation to water equivalent.
-- |
-- | Uses density to calculate: water_mm = snow_mm × (density / 1000)
waterEquivalent :: Accumulation -> SnowDensity -> Accumulation
waterEquivalent (Accumulation snowMm) dens =
  accumulation (snowMm * unwrapSnowDensity dens / 1000.0)

-- | Estimate visibility reduction factor [0, 1].
-- |
-- | 1.0 = no reduction (clear)
-- | 0.0 = zero visibility
visibilityReduction :: PrecipitationEvent -> Number
visibilityReduction event =
  case event of
    RainEvent r ->
      let rate = unwrapRate r.rate
      in Bounded.clampNumber 0.0 1.0 (1.0 - rate / 100.0)
    SnowEvent r ->
      let rate = unwrapRate r.rate
      in Bounded.clampNumber 0.0 1.0 (1.0 - rate / 30.0)  -- Snow reduces visibility faster
    SleetEvent r ->
      let rate = unwrapRate r.rate
      in Bounded.clampNumber 0.0 1.0 (1.0 - rate / 50.0)
    HailEvent r ->
      let rate = unwrapRate r.rate
      in Bounded.clampNumber 0.0 1.0 (1.0 - rate / 75.0)
    FreezingRainEvent r ->
      let rate = unwrapRate r.rate
      in Bounded.clampNumber 0.0 1.0 (1.0 - rate / 80.0)
    MixedEvent r ->
      let totalRate = unwrapRate r.rainRate + unwrapRate r.snowRate
      in Bounded.clampNumber 0.0 1.0 (1.0 - totalRate / 60.0)
