-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // weather // wind // gust
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Wind gust and turbulence primitives.
-- |
-- | ## Gust Factor
-- |
-- | Ratio of gust speed to sustained wind [1.0, 3.0]:
-- | - 1.1-1.3: Light gustiness
-- | - 1.3-1.5: Moderate gustiness
-- | - 1.5-2.0: Strong gustiness
-- | - > 2.0: Severe/turbulent conditions
-- |
-- | ## Turbulence Intensity
-- |
-- | Dimensionless measure of wind variability [0, 1]:
-- | - 0.0: Perfectly steady wind
-- | - 1.0: Extremely turbulent

module Hydrogen.Schema.Weather.Wind.Gust
  ( -- * Gust Factor
    GustFactor
  , gustFactor
  , gustFactorUnsafe
  , unwrapGustFactor
  , gustFactorBounds
  
  -- * Gust Constants
  , gustNone
  , gustLight
  , gustModerate
  , gustStrong
  , gustSevere
  
  -- * Turbulence Intensity
  , TurbulenceIntensity
  , turbulenceIntensity
  , turbulenceIntensityUnsafe
  , unwrapTurbulence
  , turbulenceBounds
  
  -- * Turbulence Constants
  , turbulenceNone
  , turbulenceLight
  , turbulenceModerate
  , turbulenceSevere
  , turbulenceExtreme
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // gust // factor
-- ═════════════════════════════════════════════════════════════════════════════

-- | Gust factor: ratio of gust speed to sustained wind [1.0, 3.0].
newtype GustFactor = GustFactor Number

derive instance eqGustFactor :: Eq GustFactor
derive instance ordGustFactor :: Ord GustFactor

instance showGustFactor :: Show GustFactor where
  show (GustFactor n) = "GustFactor " <> show n

-- | Safe constructor with clamping.
gustFactor :: Number -> GustFactor
gustFactor n = GustFactor (Bounded.clampNumber 1.0 3.0 n)

-- | Unsafe constructor for known-valid values.
gustFactorUnsafe :: Number -> GustFactor
gustFactorUnsafe = GustFactor

-- | Extract raw value.
unwrapGustFactor :: GustFactor -> Number
unwrapGustFactor (GustFactor n) = n

-- | Valid bounds documentation.
gustFactorBounds :: Bounded.NumberBounds
gustFactorBounds = Bounded.numberBounds 1.0 3.0 Bounded.Clamps "gustFactor" "Ratio of gust to sustained wind"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // gust // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | No gusts (factor 1.0).
gustNone :: GustFactor
gustNone = GustFactor 1.0

-- | Light gusts (factor 1.2).
gustLight :: GustFactor
gustLight = GustFactor 1.2

-- | Moderate gusts (factor 1.4).
gustModerate :: GustFactor
gustModerate = GustFactor 1.4

-- | Strong gusts (factor 1.7).
gustStrong :: GustFactor
gustStrong = GustFactor 1.7

-- | Severe gusts (factor 2.2).
gustSevere :: GustFactor
gustSevere = GustFactor 2.2

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // turbulence // intensity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Turbulence intensity [0, 1].
newtype TurbulenceIntensity = TurbulenceIntensity Number

derive instance eqTurbulenceIntensity :: Eq TurbulenceIntensity
derive instance ordTurbulenceIntensity :: Ord TurbulenceIntensity

instance showTurbulenceIntensity :: Show TurbulenceIntensity where
  show (TurbulenceIntensity n) = "Turbulence " <> show n

-- | Safe constructor with clamping.
turbulenceIntensity :: Number -> TurbulenceIntensity
turbulenceIntensity n = TurbulenceIntensity (Bounded.clampNumber 0.0 1.0 n)

-- | Unsafe constructor for known-valid values.
turbulenceIntensityUnsafe :: Number -> TurbulenceIntensity
turbulenceIntensityUnsafe = TurbulenceIntensity

-- | Extract raw value.
unwrapTurbulence :: TurbulenceIntensity -> Number
unwrapTurbulence (TurbulenceIntensity n) = n

-- | Valid bounds documentation.
turbulenceBounds :: Bounded.NumberBounds
turbulenceBounds = Bounded.numberBounds 0.0 1.0 Bounded.Clamps "turbulence" "Turbulence intensity"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // turbulence // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | No turbulence (0.0).
turbulenceNone :: TurbulenceIntensity
turbulenceNone = TurbulenceIntensity 0.0

-- | Light turbulence (0.1).
turbulenceLight :: TurbulenceIntensity
turbulenceLight = TurbulenceIntensity 0.1

-- | Moderate turbulence (0.3).
turbulenceModerate :: TurbulenceIntensity
turbulenceModerate = TurbulenceIntensity 0.3

-- | Severe turbulence (0.5).
turbulenceSevere :: TurbulenceIntensity
turbulenceSevere = TurbulenceIntensity 0.5

-- | Extreme turbulence (0.8).
turbulenceExtreme :: TurbulenceIntensity
turbulenceExtreme = TurbulenceIntensity 0.8
