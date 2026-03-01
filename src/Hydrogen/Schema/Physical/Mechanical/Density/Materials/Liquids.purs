-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--  // hydrogen // schema // physical // mechanical // density // materials // liquids
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Liquid density values at 20°C unless otherwise noted.
-- |
-- | All values in kg/m³.

module Hydrogen.Schema.Physical.Mechanical.Density.Materials.Liquids
  ( water
  , seawater
  , ethanol
  , methanol
  , acetone
  , gasoline
  , diesel
  , kerosene
  , mercury
  , glycerol
  , oliveoil
  , honey
  , milk
  , blood
  ) where

import Hydrogen.Schema.Physical.Mechanical.Density.Types (Density, densityUnsafe)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // liquids
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pure water at 20°C — reference standard
water :: Density
water = densityUnsafe 1000.0

-- | Seawater — ~3.5% salinity
seawater :: Density
seawater = densityUnsafe 1025.0

-- | Ethanol (ethyl alcohol)
ethanol :: Density
ethanol = densityUnsafe 789.0

-- | Methanol (methyl alcohol)
methanol :: Density
methanol = densityUnsafe 792.0

-- | Acetone — common solvent
acetone :: Density
acetone = densityUnsafe 784.0

-- | Gasoline — automotive fuel
gasoline :: Density
gasoline = densityUnsafe 720.0

-- | Diesel fuel
diesel :: Density
diesel = densityUnsafe 850.0

-- | Kerosene — jet fuel base
kerosene :: Density
kerosene = densityUnsafe 810.0

-- | Mercury (Hg) — liquid metal at room temp
mercury :: Density
mercury = densityUnsafe 13546.0

-- | Glycerol (glycerine)
glycerol :: Density
glycerol = densityUnsafe 1261.0

-- | Olive oil
oliveoil :: Density
oliveoil = densityUnsafe 920.0

-- | Honey — varies by type
honey :: Density
honey = densityUnsafe 1420.0

-- | Milk — whole
milk :: Density
milk = densityUnsafe 1030.0

-- | Human blood
blood :: Density
blood = densityUnsafe 1060.0
