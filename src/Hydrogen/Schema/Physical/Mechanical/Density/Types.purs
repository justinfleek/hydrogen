-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                // hydrogen // schema // physical // mechanical // density // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core Density type and constructors.
-- |
-- | ## What is Density?
-- |
-- | Density (ρ) is mass per unit volume: ρ = m/V
-- | SI unit: kg/m³ (kilograms per cubic meter)
-- |
-- | ## Physical Bounds
-- |
-- | - **Minimum**: ~0.00008 kg/m³ (interstellar medium)
-- | - **Maximum**: ~22,590 kg/m³ (osmium, densest stable element)
-- | - **Exotic**: Neutron star matter ~10^17 kg/m³ (not rendered)
-- |
-- | For practical materials we bound [0.001, 50000.0] kg/m³.
-- |
-- | ## Why This Matters
-- |
-- | At billion-agent scale, density determines:
-- | - Haptic feedback weight perception
-- | - Physics simulation (gravity, buoyancy, inertia)
-- | - Audio properties (denser materials ring longer)
-- | - Manufacturing simulation (material costs, structural loads)

module Hydrogen.Schema.Physical.Mechanical.Density.Types
  ( Density
  , density
  , densityUnsafe
  , unwrap
  , bounds
  , kgPerM3
  , gPerCm3
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (*)
  , (>=)
  , (<=)
  , (&&)
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // core // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Density in kg/m³ [0.001, 50000.0].
-- |
-- | ## Bounds Rationale
-- |
-- | - Lower bound 0.001: Below interstellar medium density (~0.00008)
-- | - Upper bound 50000: Above osmium (22590), allows for exotic alloys
-- |
-- | ## Invariant
-- |
-- | Value is ALWAYS in [0.001, 50000.0]. Clamped at construction.
newtype Density = Density Number

derive instance eqDensity :: Eq Density
derive instance ordDensity :: Ord Density

instance showDensity :: Show Density where
  show (Density n) = "Density(" <> show n <> " kg/m³)"

-- | Create Density with validation.
density :: Number -> Maybe Density
density n
  | n >= 0.001 && n <= 50000.0 = Just (Density n)
  | otherwise = Nothing

-- | Create Density with clamping.
densityUnsafe :: Number -> Density
densityUnsafe n = Density (Bounded.clampNumber 0.001 50000.0 n)

-- | Extract the underlying Number (kg/m³).
unwrap :: Density -> Number
unwrap (Density n) = n

-- | Bounds documentation for density.
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 0.001 50000.0 Bounded.Clamps
  "density"
  "Material density in kg/m³ (water=1000, osmium=22590)"

-- | Create density from kg/m³ value.
kgPerM3 :: Number -> Density
kgPerM3 = densityUnsafe

-- | Create density from g/cm³ value (common in chemistry).
-- | 1 g/cm³ = 1000 kg/m³
gPerCm3 :: Number -> Density
gPerCm3 n = densityUnsafe (n * 1000.0)
