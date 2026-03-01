-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                  // hydrogen // schema // weather // precipitation // rate
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Precipitation rate primitives.
-- |
-- | ## Physical Bounds
-- |
-- | Precipitation rate measured in mm/hour:
-- | - **Light rain**: < 2.5 mm/hr
-- | - **Moderate rain**: 2.5 - 7.6 mm/hr
-- | - **Heavy rain**: 7.6 - 50 mm/hr
-- | - **Violent rain**: > 50 mm/hr (tropical storms)
-- | - **Record**: ~300 mm/hr (brief bursts)

module Hydrogen.Schema.Weather.Precipitation.Rate
  ( -- * Precipitation Rate
    PrecipitationRate
  , precipitationRate
  , precipitationRateUnsafe
  , unwrapRate
  , rateBounds
  , mmPerHour
  , inchesPerHour
  
  -- * Constants
  , rateNone
  , rateTrace
  , rateLight
  , rateModerate
  , rateHeavy
  , rateViolent
  , rateTorrential
  
  -- * Intensity Classification
  , Intensity(..)
  , allIntensities
  , rateToIntensity
  , intensityToMinRate
  
  -- * Operations
  , lerp
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (<=)
  , (<>)
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // precipitation // rate
-- ═════════════════════════════════════════════════════════════════════════════

-- | Precipitation rate in mm/hour [0, 500].
-- |
-- | ## Bounds Rationale
-- |
-- | - Minimum 0: No precipitation
-- | - Maximum 500: Exceeds any recorded sustained rate (~300 mm/hr max bursts)
newtype PrecipitationRate = PrecipitationRate Number

derive instance eqPrecipitationRate :: Eq PrecipitationRate
derive instance ordPrecipitationRate :: Ord PrecipitationRate

instance showPrecipitationRate :: Show PrecipitationRate where
  show (PrecipitationRate n) = "PrecipitationRate " <> show n <> " mm/hr"

-- | Safe constructor with clamping.
precipitationRate :: Number -> PrecipitationRate
precipitationRate n = PrecipitationRate (Bounded.clampNumber 0.0 500.0 n)

-- | Unsafe constructor for known-valid values.
precipitationRateUnsafe :: Number -> PrecipitationRate
precipitationRateUnsafe = PrecipitationRate

-- | Extract raw value.
unwrapRate :: PrecipitationRate -> Number
unwrapRate (PrecipitationRate n) = n

-- | Valid bounds documentation.
rateBounds :: Bounded.NumberBounds
rateBounds = Bounded.numberBounds 0.0 500.0 Bounded.Clamps "precipitationRate" "Precipitation rate in mm/hr"

-- | Convert to mm/hour (identity, canonical unit).
mmPerHour :: PrecipitationRate -> Number
mmPerHour = unwrapRate

-- | Convert to inches/hour (1 inch = 25.4 mm).
inchesPerHour :: PrecipitationRate -> Number
inchesPerHour (PrecipitationRate n) = n / 25.4

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | No precipitation (0 mm/hr).
rateNone :: PrecipitationRate
rateNone = PrecipitationRate 0.0

-- | Trace precipitation (0.1 mm/hr).
rateTrace :: PrecipitationRate
rateTrace = PrecipitationRate 0.1

-- | Light precipitation (1.5 mm/hr).
rateLight :: PrecipitationRate
rateLight = PrecipitationRate 1.5

-- | Moderate precipitation (5.0 mm/hr).
rateModerate :: PrecipitationRate
rateModerate = PrecipitationRate 5.0

-- | Heavy precipitation (25.0 mm/hr).
rateHeavy :: PrecipitationRate
rateHeavy = PrecipitationRate 25.0

-- | Violent precipitation (75.0 mm/hr).
rateViolent :: PrecipitationRate
rateViolent = PrecipitationRate 75.0

-- | Torrential precipitation (150.0 mm/hr).
rateTorrential :: PrecipitationRate
rateTorrential = PrecipitationRate 150.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // intensity // classification
-- ═════════════════════════════════════════════════════════════════════════════

-- | Intensity classification per WMO standards.
data Intensity
  = IntensityNone      -- ^ 0 mm/hr
  | IntensityTrace     -- ^ < 0.5 mm/hr
  | IntensityLight     -- ^ 0.5 - 2.5 mm/hr
  | IntensityModerate  -- ^ 2.5 - 10 mm/hr
  | IntensityHeavy     -- ^ 10 - 50 mm/hr
  | IntensityViolent   -- ^ > 50 mm/hr

derive instance eqIntensity :: Eq Intensity
derive instance ordIntensity :: Ord Intensity

instance showIntensity :: Show Intensity where
  show IntensityNone = "None"
  show IntensityTrace = "Trace"
  show IntensityLight = "Light"
  show IntensityModerate = "Moderate"
  show IntensityHeavy = "Heavy"
  show IntensityViolent = "Violent"

-- | All intensity levels for enumeration.
allIntensities :: Array Intensity
allIntensities =
  [ IntensityNone
  , IntensityTrace
  , IntensityLight
  , IntensityModerate
  , IntensityHeavy
  , IntensityViolent
  ]

-- | Classify rate into intensity category.
rateToIntensity :: PrecipitationRate -> Intensity
rateToIntensity (PrecipitationRate n)
  | n <= 0.0 = IntensityNone
  | n < 0.5 = IntensityTrace
  | n < 2.5 = IntensityLight
  | n < 10.0 = IntensityModerate
  | n < 50.0 = IntensityHeavy
  | otherwise = IntensityViolent

-- | Minimum rate for an intensity category.
intensityToMinRate :: Intensity -> PrecipitationRate
intensityToMinRate IntensityNone = PrecipitationRate 0.0
intensityToMinRate IntensityTrace = PrecipitationRate 0.1
intensityToMinRate IntensityLight = PrecipitationRate 0.5
intensityToMinRate IntensityModerate = PrecipitationRate 2.5
intensityToMinRate IntensityHeavy = PrecipitationRate 10.0
intensityToMinRate IntensityViolent = PrecipitationRate 50.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Linear interpolation between two precipitation rates.
lerp :: Number -> PrecipitationRate -> PrecipitationRate -> PrecipitationRate
lerp t (PrecipitationRate a) (PrecipitationRate b) =
  precipitationRate (a + t * (b - a))
