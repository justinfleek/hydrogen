-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                // hydrogen // schema // weather // atmosphere // cloud cover
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Cloud cover primitives for atmospheric measurement.
-- |
-- | ## Physical Bounds
-- |
-- | - Range: 0-100% sky obscuration
-- | - Also expressible in oktas (eighths of sky, 0-8)
-- |
-- | METAR categories: SKC, FEW, SCT, BKN, OVC.

module Hydrogen.Schema.Weather.Atmosphere.CloudCover
  ( -- * Cloud Cover Type
    CloudCover
  , cloudCover
  , cloudCoverUnsafe
  , unwrapCloudCover
  , cloudCoverBounds
  , cloudCoverPercent
  , cloudCoverOktas
  
  -- * Constants
  , cloudCoverClear
  , cloudCoverFewClouds
  , cloudCoverScattered
  , cloudCoverBroken
  , cloudCoverOvercast
  
  -- * Categories
  , CloudCategory(SKC, FEW, SCT, BKN, OVC)
  , allCloudCategories
  , cloudCoverToCategory
  , categoryDescription
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (<=)
  , (<>)
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // cloud // cover
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cloud cover in percent [0, 100].
-- |
-- | Percentage of sky obscured by clouds.
newtype CloudCover = CloudCover Number

derive instance eqCloudCover :: Eq CloudCover
derive instance ordCloudCover :: Ord CloudCover

instance showCloudCover :: Show CloudCover where
  show (CloudCover n) = "CloudCover " <> show n <> "%"

-- | Safe constructor with clamping.
cloudCover :: Number -> CloudCover
cloudCover n = CloudCover (Bounded.clampNumber 0.0 100.0 n)

-- | Unsafe constructor for known-valid values.
cloudCoverUnsafe :: Number -> CloudCover
cloudCoverUnsafe = CloudCover

-- | Extract raw value.
unwrapCloudCover :: CloudCover -> Number
unwrapCloudCover (CloudCover n) = n

-- | Valid bounds documentation.
cloudCoverBounds :: Bounded.NumberBounds
cloudCoverBounds = Bounded.numberBounds 0.0 100.0 Bounded.Clamps "cloudCover" "Cloud cover in percent"

-- | Get cloud cover as percent (identity).
cloudCoverPercent :: CloudCover -> Number
cloudCoverPercent = unwrapCloudCover

-- | Convert to oktas (eighths of sky, 0-8).
cloudCoverOktas :: CloudCover -> Int
cloudCoverOktas (CloudCover p)
  | p <= 0.0 = 0
  | p <= 12.5 = 1
  | p <= 25.0 = 2
  | p <= 37.5 = 3
  | p <= 50.0 = 4
  | p <= 62.5 = 5
  | p <= 75.0 = 6
  | p <= 87.5 = 7
  | otherwise = 8

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clear sky (0%, 0 oktas).
cloudCoverClear :: CloudCover
cloudCoverClear = CloudCover 0.0

-- | Few clouds (12.5%, 1 okta).
cloudCoverFewClouds :: CloudCover
cloudCoverFewClouds = CloudCover 12.5

-- | Scattered clouds (37.5%, 3 oktas).
cloudCoverScattered :: CloudCover
cloudCoverScattered = CloudCover 37.5

-- | Broken clouds (62.5%, 5 oktas).
cloudCoverBroken :: CloudCover
cloudCoverBroken = CloudCover 62.5

-- | Overcast (100%, 8 oktas).
cloudCoverOvercast :: CloudCover
cloudCoverOvercast = CloudCover 100.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // categories
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cloud cover categories (METAR standard).
data CloudCategory
  = SKC  -- ^ Sky clear (0 oktas)
  | FEW  -- ^ Few clouds (1-2 oktas)
  | SCT  -- ^ Scattered (3-4 oktas)
  | BKN  -- ^ Broken (5-7 oktas)
  | OVC  -- ^ Overcast (8 oktas)

derive instance eqCloudCategory :: Eq CloudCategory
derive instance ordCloudCategory :: Ord CloudCategory

instance showCloudCategory :: Show CloudCategory where
  show SKC = "SKC"
  show FEW = "FEW"
  show SCT = "SCT"
  show BKN = "BKN"
  show OVC = "OVC"

-- | All cloud categories for enumeration.
allCloudCategories :: Array CloudCategory
allCloudCategories = [SKC, FEW, SCT, BKN, OVC]

-- | Classify cloud cover.
cloudCoverToCategory :: CloudCover -> CloudCategory
cloudCoverToCategory c =
  let oktas = cloudCoverOktas c
  in if oktas <= 0 then SKC
     else if oktas <= 2 then FEW
     else if oktas <= 4 then SCT
     else if oktas <= 7 then BKN
     else OVC

-- | Human-readable category description.
categoryDescription :: CloudCategory -> String
categoryDescription SKC = "Sky clear"
categoryDescription FEW = "Few clouds"
categoryDescription SCT = "Scattered clouds"
categoryDescription BKN = "Broken clouds"
categoryDescription OVC = "Overcast"
