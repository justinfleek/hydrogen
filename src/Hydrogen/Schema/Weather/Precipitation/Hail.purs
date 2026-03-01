-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                  // hydrogen // schema // weather // precipitation // hail
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Hail primitives — size and classification.
-- |
-- | ## Physical Bounds
-- |
-- | Hail diameter in mm [5, 150]:
-- | - Minimum 5: Below this is graupel/ice pellets
-- | - Maximum 150: ~6 inches, near record sizes (softball+)
-- |
-- | Hail grows by accretion in convective updrafts.

module Hydrogen.Schema.Weather.Precipitation.Hail
  ( -- * Hail Diameter
    HailDiameter
  , hailDiameter
  , hailDiameterUnsafe
  , unwrapHail
  , hailBounds
  , hailMillimeters
  
  -- * Size Constants
  , hailPea
  , hailMarble
  , hailGolfBall
  , hailTennisBall
  , hailSoftball
  
  -- * Classification
  , HailCategory(..)
  , allHailCategories
  , hailToCategory
  , categoryToMinDiameter
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (<)
  , (<>)
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // hail // diameter
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hail diameter in mm [5, 150].
newtype HailDiameter = HailDiameter Number

derive instance eqHailDiameter :: Eq HailDiameter
derive instance ordHailDiameter :: Ord HailDiameter

instance showHailDiameter :: Show HailDiameter where
  show (HailDiameter n) = "HailDiameter " <> show n <> " mm"

-- | Safe constructor with clamping.
hailDiameter :: Number -> HailDiameter
hailDiameter n = HailDiameter (Bounded.clampNumber 5.0 150.0 n)

-- | Unsafe constructor for known-valid values.
hailDiameterUnsafe :: Number -> HailDiameter
hailDiameterUnsafe = HailDiameter

-- | Extract raw value.
unwrapHail :: HailDiameter -> Number
unwrapHail (HailDiameter n) = n

-- | Valid bounds documentation.
hailBounds :: Bounded.NumberBounds
hailBounds = Bounded.numberBounds 5.0 150.0 Bounded.Clamps "hailDiameter" "Hail diameter in mm"

-- | Get diameter in millimeters (identity).
hailMillimeters :: HailDiameter -> Number
hailMillimeters = unwrapHail

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // size // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pea-sized hail (~6 mm).
hailPea :: HailDiameter
hailPea = HailDiameter 6.0

-- | Marble-sized hail (~15 mm).
hailMarble :: HailDiameter
hailMarble = HailDiameter 15.0

-- | Golf ball hail (~44 mm / 1.75 inches).
hailGolfBall :: HailDiameter
hailGolfBall = HailDiameter 44.0

-- | Tennis ball hail (~64 mm / 2.5 inches).
hailTennisBall :: HailDiameter
hailTennisBall = HailDiameter 64.0

-- | Softball hail (~100 mm / 4 inches).
hailSoftball :: HailDiameter
hailSoftball = HailDiameter 100.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // classification
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hail size categories (NOAA/NWS classification).
data HailCategory
  = HailSmall       -- ^ < 25mm (quarter)
  | HailSevere      -- ^ 25-50mm (quarter to golf ball)
  | HailSignificant -- ^ 50-75mm (golf ball to tennis ball)
  | HailGiant       -- ^ > 75mm (larger than tennis ball)

derive instance eqHailCategory :: Eq HailCategory
derive instance ordHailCategory :: Ord HailCategory

instance showHailCategory :: Show HailCategory where
  show HailSmall = "Small"
  show HailSevere = "Severe"
  show HailSignificant = "Significant"
  show HailGiant = "Giant"

-- | All hail categories for enumeration.
allHailCategories :: Array HailCategory
allHailCategories =
  [ HailSmall
  , HailSevere
  , HailSignificant
  , HailGiant
  ]

-- | Classify hail by diameter.
hailToCategory :: HailDiameter -> HailCategory
hailToCategory (HailDiameter d)
  | d < 25.0 = HailSmall
  | d < 50.0 = HailSevere
  | d < 75.0 = HailSignificant
  | otherwise = HailGiant

-- | Minimum diameter for a category.
categoryToMinDiameter :: HailCategory -> HailDiameter
categoryToMinDiameter HailSmall = HailDiameter 5.0
categoryToMinDiameter HailSevere = HailDiameter 25.0
categoryToMinDiameter HailSignificant = HailDiameter 50.0
categoryToMinDiameter HailGiant = HailDiameter 75.0
