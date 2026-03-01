-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--    // hydrogen // schema // physical // mechanical // density // materials // gases
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Gas density values at Standard Temperature and Pressure (STP).
-- |
-- | STP conditions: 20°C (293.15 K), 101.325 kPa (1 atm)
-- |
-- | All values in kg/m³.

module Hydrogen.Schema.Physical.Mechanical.Density.Materials.Gases
  ( hydrogen
  , helium
  , air
  , nitrogen
  , oxygen
  , carbonDioxide
  , argon
  , methane
  , propane
  , butane
  ) where

import Hydrogen.Schema.Physical.Mechanical.Density.Types (Density, densityUnsafe)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // gases at STP
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hydrogen gas (H₂) — lightest gas
hydrogen :: Density
hydrogen = densityUnsafe 0.0899

-- | Helium (He) — second lightest
helium :: Density
helium = densityUnsafe 0.1785

-- | Air — standard atmosphere mix
air :: Density
air = densityUnsafe 1.225

-- | Nitrogen (N₂) — 78% of air
nitrogen :: Density
nitrogen = densityUnsafe 1.251

-- | Oxygen (O₂) — 21% of air
oxygen :: Density
oxygen = densityUnsafe 1.429

-- | Carbon dioxide (CO₂)
carbonDioxide :: Density
carbonDioxide = densityUnsafe 1.977

-- | Argon (Ar) — noble gas
argon :: Density
argon = densityUnsafe 1.784

-- | Methane (CH₄) — natural gas
methane :: Density
methane = densityUnsafe 0.717

-- | Propane (C₃H₈) — LPG component
propane :: Density
propane = densityUnsafe 2.01

-- | Butane (C₄H₁₀) — lighter fluid
butane :: Density
butane = densityUnsafe 2.48
