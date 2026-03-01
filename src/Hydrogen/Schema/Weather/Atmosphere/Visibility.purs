-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                // hydrogen // schema // weather // atmosphere // visibility
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Visibility primitives for atmospheric measurement.
-- |
-- | ## Physical Bounds
-- |
-- | - Minimum 0: Zero visibility (dense fog, whiteout)
-- | - Maximum 100000: 100km, "unlimited" visibility in very clear air
-- |
-- | Aviation uses statute miles; we use meters as SI canonical.

module Hydrogen.Schema.Weather.Atmosphere.Visibility
  ( -- * Visibility Type
    Visibility
  , visibility
  , visibilityUnsafe
  , unwrapVisibility
  , visibilityBounds
  
  -- * Unit Conversions
  , visibilityMeters
  , visibilityKilometers
  , visibilityMiles
  
  -- * Constants
  , visibilityZero
  , visibilityDenseFog
  , visibilityFog
  , visibilityMist
  , visibilityHaze
  , visibilityClear
  , visibilityUnlimited
  
  -- * Classification
  , VisibilityCategory(..)
  , allVisibilityCategories
  , visibilityToCategory
  , categoryToMinVisibility
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (<)
  , (/)
  , (<>)
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // visibility
-- ═════════════════════════════════════════════════════════════════════════════

-- | Visibility distance in meters [0, 100000].
-- |
-- | ## Bounds Rationale
-- |
-- | - Minimum 0: Zero visibility (dense fog, whiteout)
-- | - Maximum 100000: 100km, "unlimited" visibility in very clear air
-- |
-- | Aviation uses statute miles; we use meters as SI canonical.
newtype Visibility = Visibility Number

derive instance eqVisibility :: Eq Visibility
derive instance ordVisibility :: Ord Visibility

instance showVisibility :: Show Visibility where
  show (Visibility n) = "Visibility " <> show n <> "m"

-- | Safe constructor with clamping.
visibility :: Number -> Visibility
visibility n = Visibility (Bounded.clampNumber 0.0 100000.0 n)

-- | Unsafe constructor for known-valid values.
visibilityUnsafe :: Number -> Visibility
visibilityUnsafe = Visibility

-- | Extract raw value.
unwrapVisibility :: Visibility -> Number
unwrapVisibility (Visibility n) = n

-- | Valid bounds documentation.
visibilityBounds :: Bounded.NumberBounds
visibilityBounds = Bounded.numberBounds 0.0 100000.0 Bounded.Clamps "visibility" "Visibility in meters"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // unit // conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get visibility in meters (identity).
visibilityMeters :: Visibility -> Number
visibilityMeters = unwrapVisibility

-- | Convert to kilometers.
visibilityKilometers :: Visibility -> Number
visibilityKilometers (Visibility m) = m / 1000.0

-- | Convert to statute miles.
visibilityMiles :: Visibility -> Number
visibilityMiles (Visibility m) = m / 1609.34

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Zero visibility (0m).
visibilityZero :: Visibility
visibilityZero = Visibility 0.0

-- | Dense fog (< 50m).
visibilityDenseFog :: Visibility
visibilityDenseFog = Visibility 30.0

-- | Fog (50-200m).
visibilityFog :: Visibility
visibilityFog = Visibility 100.0

-- | Mist (200-1000m).
visibilityMist :: Visibility
visibilityMist = Visibility 500.0

-- | Haze (1-10km).
visibilityHaze :: Visibility
visibilityHaze = Visibility 5000.0

-- | Clear (10-40km).
visibilityClear :: Visibility
visibilityClear = Visibility 20000.0

-- | Unlimited (> 40km).
visibilityUnlimited :: Visibility
visibilityUnlimited = Visibility 80000.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // classification
-- ═════════════════════════════════════════════════════════════════════════════

-- | Visibility categories (aviation standard).
data VisibilityCategory
  = VisZero      -- ^ < 50m (LIFR - Low IFR)
  | VisDenseFog  -- ^ 50-200m
  | VisFog       -- ^ 200-1000m
  | VisMist      -- ^ 1-5km
  | VisHaze      -- ^ 5-10km
  | VisClear     -- ^ > 10km

derive instance eqVisibilityCategory :: Eq VisibilityCategory
derive instance ordVisibilityCategory :: Ord VisibilityCategory

instance showVisibilityCategory :: Show VisibilityCategory where
  show VisZero = "Zero"
  show VisDenseFog = "DenseFog"
  show VisFog = "Fog"
  show VisMist = "Mist"
  show VisHaze = "Haze"
  show VisClear = "Clear"

-- | All visibility categories for enumeration.
allVisibilityCategories :: Array VisibilityCategory
allVisibilityCategories = [VisZero, VisDenseFog, VisFog, VisMist, VisHaze, VisClear]

-- | Classify visibility.
visibilityToCategory :: Visibility -> VisibilityCategory
visibilityToCategory (Visibility m)
  | m < 50.0 = VisZero
  | m < 200.0 = VisDenseFog
  | m < 1000.0 = VisFog
  | m < 5000.0 = VisMist
  | m < 10000.0 = VisHaze
  | otherwise = VisClear

-- | Minimum visibility for a category.
categoryToMinVisibility :: VisibilityCategory -> Visibility
categoryToMinVisibility VisZero = Visibility 0.0
categoryToMinVisibility VisDenseFog = Visibility 50.0
categoryToMinVisibility VisFog = Visibility 200.0
categoryToMinVisibility VisMist = Visibility 1000.0
categoryToMinVisibility VisHaze = Visibility 5000.0
categoryToMinVisibility VisClear = Visibility 10000.0
