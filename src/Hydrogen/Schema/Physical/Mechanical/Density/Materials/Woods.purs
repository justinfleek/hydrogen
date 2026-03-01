-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--   // hydrogen // schema // physical // mechanical // density // materials // woods
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Wood density values at ~12% moisture content.
-- |
-- | All values in kg/m³.

module Hydrogen.Schema.Physical.Mechanical.Density.Materials.Woods
  ( balsa
  , pine
  , oak
  , maple
  , walnut
  , mahogany
  , teak
  , ebony
  , bamboo
  , cork
  ) where

import Hydrogen.Schema.Physical.Mechanical.Density.Types (Density, densityUnsafe)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // woods
-- ═════════════════════════════════════════════════════════════════════════════

-- | Balsa — lightest commercial wood
balsa :: Density
balsa = densityUnsafe 160.0

-- | Pine — common softwood
pine :: Density
pine = densityUnsafe 510.0

-- | Oak — common hardwood
oak :: Density
oak = densityUnsafe 750.0

-- | Maple — hard, dense hardwood
maple :: Density
maple = densityUnsafe 700.0

-- | Walnut — furniture wood
walnut :: Density
walnut = densityUnsafe 650.0

-- | Mahogany — tropical hardwood
mahogany :: Density
mahogany = densityUnsafe 530.0

-- | Teak — water-resistant hardwood
teak :: Density
teak = densityUnsafe 630.0

-- | Ebony — very dense, nearly sinks
ebony :: Density
ebony = densityUnsafe 1120.0

-- | Bamboo — grass, varies by species
bamboo :: Density
bamboo = densityUnsafe 350.0

-- | Cork — bark, very light
cork :: Density
cork = densityUnsafe 120.0
