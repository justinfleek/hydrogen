-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // physical // ior // liquids
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Index of Refraction values for liquids.
-- |
-- | Liquids typically have IOR values in the range 1.3-1.65.
-- | Water at 1.333 is the most common reference point.

module Hydrogen.Schema.Physical.Optical.IOR.Liquids
  ( -- * Liquids (n ~ 1.3-1.65)
    water
  , waterIce
  , seawater
  , ethanol
  , methanol
  , acetone
  , glycerol
  , benzene
  , toluene
  , carbonDisulfide
  , oliveoil
  , turpentine
  , honey
  ) where

import Hydrogen.Schema.Physical.Optical.IOR.Core (IOR, iorUnsafe)

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                   // liquids
-- ═══════════════════════════════════════════════════════════════════════════

-- | Pure water at 20°C (n = 1.333)
water :: IOR
water = iorUnsafe 1.333

-- | Water ice (n = 1.31)
waterIce :: IOR
waterIce = iorUnsafe 1.31

-- | Seawater, 3.5% salinity (n = 1.339)
seawater :: IOR
seawater = iorUnsafe 1.339

-- | Ethanol / ethyl alcohol (n = 1.361)
ethanol :: IOR
ethanol = iorUnsafe 1.361

-- | Methanol / methyl alcohol (n = 1.329)
methanol :: IOR
methanol = iorUnsafe 1.329

-- | Acetone (n = 1.359)
acetone :: IOR
acetone = iorUnsafe 1.359

-- | Glycerol / glycerin (n = 1.473)
glycerol :: IOR
glycerol = iorUnsafe 1.473

-- | Benzene (n = 1.501)
benzene :: IOR
benzene = iorUnsafe 1.501

-- | Toluene (n = 1.497)
toluene :: IOR
toluene = iorUnsafe 1.497

-- | Carbon disulfide - very high for liquid (n = 1.628)
carbonDisulfide :: IOR
carbonDisulfide = iorUnsafe 1.628

-- | Olive oil (n = 1.47)
oliveoil :: IOR
oliveoil = iorUnsafe 1.47

-- | Turpentine (n = 1.472)
turpentine :: IOR
turpentine = iorUnsafe 1.472

-- | Honey (n = 1.504)
honey :: IOR
honey = iorUnsafe 1.504
