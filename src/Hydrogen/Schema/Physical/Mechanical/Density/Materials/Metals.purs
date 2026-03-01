-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--  // hydrogen // schema // physical // mechanical // density // materials // metals
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Metal density values at 20°C.
-- |
-- | Organized by category: light, common, precious, and heavy metals.
-- |
-- | All values in kg/m³.

module Hydrogen.Schema.Physical.Mechanical.Density.Materials.Metals
  ( -- * Light Metals
    lithium
  , magnesium
  , aluminum
  , titanium
  
  -- * Common Metals
  , iron
  , steel
  , stainlessSteel
  , copper
  , brass
  , bronze
  , zinc
  , tin
  , nickel
  , chromium
  
  -- * Precious Metals
  , silver
  , gold
  , platinum
  , palladium
  , rhodium
  
  -- * Heavy Metals
  , lead
  , tungsten
  , uranium
  , osmium
  , iridium
  ) where

import Hydrogen.Schema.Physical.Mechanical.Density.Types (Density, densityUnsafe)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // metals — light
-- ═════════════════════════════════════════════════════════════════════════════

-- | Lithium (Li) — lightest metal
lithium :: Density
lithium = densityUnsafe 534.0

-- | Magnesium (Mg) — structural light metal
magnesium :: Density
magnesium = densityUnsafe 1738.0

-- | Aluminum (Al) — common light metal
aluminum :: Density
aluminum = densityUnsafe 2700.0

-- | Titanium (Ti) — aerospace metal
titanium :: Density
titanium = densityUnsafe 4507.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // metals — common
-- ═════════════════════════════════════════════════════════════════════════════

-- | Iron (Fe) — pure
iron :: Density
iron = densityUnsafe 7874.0

-- | Steel — carbon steel average
steel :: Density
steel = densityUnsafe 7850.0

-- | Stainless steel — 304 grade
stainlessSteel :: Density
stainlessSteel = densityUnsafe 8000.0

-- | Copper (Cu)
copper :: Density
copper = densityUnsafe 8960.0

-- | Brass — Cu-Zn alloy
brass :: Density
brass = densityUnsafe 8500.0

-- | Bronze — Cu-Sn alloy
bronze :: Density
bronze = densityUnsafe 8900.0

-- | Zinc (Zn)
zinc :: Density
zinc = densityUnsafe 7140.0

-- | Tin (Sn)
tin :: Density
tin = densityUnsafe 7310.0

-- | Nickel (Ni)
nickel :: Density
nickel = densityUnsafe 8908.0

-- | Chromium (Cr)
chromium :: Density
chromium = densityUnsafe 7190.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // metals — precious
-- ═════════════════════════════════════════════════════════════════════════════

-- | Silver (Ag)
silver :: Density
silver = densityUnsafe 10490.0

-- | Gold (Au)
gold :: Density
gold = densityUnsafe 19320.0

-- | Platinum (Pt)
platinum :: Density
platinum = densityUnsafe 21450.0

-- | Palladium (Pd)
palladium :: Density
palladium = densityUnsafe 12023.0

-- | Rhodium (Rh)
rhodium :: Density
rhodium = densityUnsafe 12410.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // metals — heavy
-- ═════════════════════════════════════════════════════════════════════════════

-- | Lead (Pb)
lead :: Density
lead = densityUnsafe 11340.0

-- | Tungsten (W) — very dense refractory
tungsten :: Density
tungsten = densityUnsafe 19250.0

-- | Uranium (U) — depleted
uranium :: Density
uranium = densityUnsafe 19100.0

-- | Osmium (Os) — densest stable element
osmium :: Density
osmium = densityUnsafe 22590.0

-- | Iridium (Ir) — second densest
iridium :: Density
iridium = densityUnsafe 22560.0
