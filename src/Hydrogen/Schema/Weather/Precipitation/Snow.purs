-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                  // hydrogen // schema // weather // precipitation // snow
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Snow primitives — snowflake types and snow density.
-- |
-- | ## Snowflake Types
-- |
-- | Crystal form depends on temperature and supersaturation (Nakaya classification).
-- |
-- | ## Snow Density
-- |
-- | Snow:water ratio varies from 50:1 (very dry powder) to 3:1 (wet heavy snow).
-- | - Range: 20-917 kg/m³ (fresh powder to glacial ice)

module Hydrogen.Schema.Weather.Precipitation.Snow
  ( -- * Snowflake Types
    SnowflakeType(..)
  , allSnowflakeTypes
  , snowflakeDescription
  
  -- * Snow Density
  , SnowDensity
  , snowDensity
  , snowDensityUnsafe
  , unwrapSnowDensity
  , snowDensityBounds
  , kgPerCubicMeter
  
  -- * Density Constants
  , densityPowder
  , densityFresh
  , densitySettled
  , densityWet
  , densityCompacted
  , densityIce
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
--                                                       // snowflake // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Snowflake crystal types (Nakaya classification).
data SnowflakeType
  = Plates           -- ^ Flat hexagonal (-0 to -4C)
  | StellarDendrites -- ^ Classic 6-branched (-12 to -16C)
  | Columns          -- ^ Hexagonal columns (-5 to -8C)
  | Needles          -- ^ Long thin crystals (-5 to -8C)
  | SpatialDendrites -- ^ 3D branched (-12 to -16C)
  | CappedColumns    -- ^ Columns with plate ends
  | IrregularCrystals -- ^ Mixed/deformed forms
  | SnowGraupel      -- ^ Rime-covered crystals
  | SleetCrystals    -- ^ Refrozen drops

derive instance eqSnowflakeType :: Eq SnowflakeType
derive instance ordSnowflakeType :: Ord SnowflakeType

instance showSnowflakeType :: Show SnowflakeType where
  show Plates = "Plates"
  show StellarDendrites = "StellarDendrites"
  show Columns = "Columns"
  show Needles = "Needles"
  show SpatialDendrites = "SpatialDendrites"
  show CappedColumns = "CappedColumns"
  show IrregularCrystals = "IrregularCrystals"
  show SnowGraupel = "Graupel"
  show SleetCrystals = "SleetCrystals"

-- | All snowflake types for enumeration.
allSnowflakeTypes :: Array SnowflakeType
allSnowflakeTypes =
  [ Plates
  , StellarDendrites
  , Columns
  , Needles
  , SpatialDendrites
  , CappedColumns
  , IrregularCrystals
  , SnowGraupel
  , SleetCrystals
  ]

-- | Human-readable description.
snowflakeDescription :: SnowflakeType -> String
snowflakeDescription Plates = "Flat hexagonal plates, forms near 0C"
snowflakeDescription StellarDendrites = "Classic six-branched stars, forms -12 to -16C"
snowflakeDescription Columns = "Hexagonal columns, forms -5 to -8C"
snowflakeDescription Needles = "Long thin needles, forms -5 to -8C"
snowflakeDescription SpatialDendrites = "Three-dimensional branching, forms -12 to -16C"
snowflakeDescription CappedColumns = "Columns with plate caps at ends"
snowflakeDescription IrregularCrystals = "Mixed or deformed crystal forms"
snowflakeDescription SnowGraupel = "Rime-coated crystals (soft hail)"
snowflakeDescription SleetCrystals = "Refrozen raindrops"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // snow // density
-- ═════════════════════════════════════════════════════════════════════════════

-- | Snow density in kg/m³ [20, 917].
-- |
-- | ## Bounds Rationale
-- |
-- | - Minimum 20: Fresh powder snow (10:1+ ratio)
-- | - Maximum 917: Pure ice density
newtype SnowDensity = SnowDensity Number

derive instance eqSnowDensity :: Eq SnowDensity
derive instance ordSnowDensity :: Ord SnowDensity

instance showSnowDensity :: Show SnowDensity where
  show (SnowDensity n) = "SnowDensity " <> show n <> " kg/m³"

-- | Safe constructor with clamping.
snowDensity :: Number -> SnowDensity
snowDensity n = SnowDensity (Bounded.clampNumber 20.0 917.0 n)

-- | Unsafe constructor for known-valid values.
snowDensityUnsafe :: Number -> SnowDensity
snowDensityUnsafe = SnowDensity

-- | Extract raw value.
unwrapSnowDensity :: SnowDensity -> Number
unwrapSnowDensity (SnowDensity n) = n

-- | Valid bounds documentation.
snowDensityBounds :: Bounded.NumberBounds
snowDensityBounds = Bounded.numberBounds 20.0 917.0 Bounded.Clamps "snowDensity" "Snow density in kg/m³"

-- | Get density in kg/m³ (identity).
kgPerCubicMeter :: SnowDensity -> Number
kgPerCubicMeter = unwrapSnowDensity

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // density // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fresh powder (50 kg/m³, ~20:1 ratio).
densityPowder :: SnowDensity
densityPowder = SnowDensity 50.0

-- | Fresh snow (100 kg/m³, ~10:1 ratio).
densityFresh :: SnowDensity
densityFresh = SnowDensity 100.0

-- | Settled snow (200 kg/m³, ~5:1 ratio).
densitySettled :: SnowDensity
densitySettled = SnowDensity 200.0

-- | Wet snow (400 kg/m³, ~2.5:1 ratio).
densityWet :: SnowDensity
densityWet = SnowDensity 400.0

-- | Compacted snow (550 kg/m³, near firn).
densityCompacted :: SnowDensity
densityCompacted = SnowDensity 550.0

-- | Glacial ice (917 kg/m³).
densityIce :: SnowDensity
densityIce = SnowDensity 917.0
