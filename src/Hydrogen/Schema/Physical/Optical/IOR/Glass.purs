-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // physical // ior // glass
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Index of Refraction values for glass materials.
-- |
-- | Includes both common glass types (window glass, lab glass) and
-- | specialized optical glass used in lenses and instruments.

module Hydrogen.Schema.Physical.Optical.IOR.Glass
  ( -- * Common Glass (n ~ 1.5-1.9)
    sodaLimeGlass
  , borosilicateGlass
  , crownGlass
  , flintGlass
  , denseFlintGlass
  , leadGlass
  , fusedSilica
  , pyrex
  
  -- * Optical Glass (n ~ 1.4-2.0)
  , bk7
  , sf11
  , laf2
  , lasf9
  , nbk7
  , nsk2
  ) where

import Hydrogen.Schema.Physical.Optical.IOR.Core (IOR, iorUnsafe)

-- ═══════════════════════════════════════════════════════════════════════════
--                                                              // common glass
-- ═══════════════════════════════════════════════════════════════════════════

-- | Soda-lime glass (window glass) (n = 1.52)
sodaLimeGlass :: IOR
sodaLimeGlass = iorUnsafe 1.52

-- | Borosilicate glass (lab glass) (n = 1.474)
borosilicateGlass :: IOR
borosilicateGlass = iorUnsafe 1.474

-- | Crown glass (low dispersion optical) (n = 1.52)
crownGlass :: IOR
crownGlass = iorUnsafe 1.52

-- | Flint glass (high dispersion optical) (n = 1.62)
flintGlass :: IOR
flintGlass = iorUnsafe 1.62

-- | Dense flint glass (n = 1.75)
denseFlintGlass :: IOR
denseFlintGlass = iorUnsafe 1.75

-- | Lead glass / crystal (n = 1.65)
leadGlass :: IOR
leadGlass = iorUnsafe 1.65

-- | Fused silica / fused quartz (n = 1.458)
fusedSilica :: IOR
fusedSilica = iorUnsafe 1.458

-- | Pyrex (borosilicate trade name) (n = 1.474)
pyrex :: IOR
pyrex = iorUnsafe 1.474

-- ═══════════════════════════════════════════════════════════════════════════
--                                                             // optical glass
-- ═══════════════════════════════════════════════════════════════════════════

-- | BK7 - most common optical glass (n = 1.5168)
bk7 :: IOR
bk7 = iorUnsafe 1.5168

-- | SF11 - dense flint for dispersion (n = 1.7847)
sf11 :: IOR
sf11 = iorUnsafe 1.7847

-- | LAF2 - lanthanum flint (n = 1.744)
laf2 :: IOR
laf2 = iorUnsafe 1.744

-- | LASF9 - lanthanum dense flint (n = 1.850)
lasf9 :: IOR
lasf9 = iorUnsafe 1.850

-- | N-BK7 - newer BK7 formulation (n = 1.5168)
nbk7 :: IOR
nbk7 = iorUnsafe 1.5168

-- | N-SK2 - dense crown (n = 1.6074)
nsk2 :: IOR
nsk2 = iorUnsafe 1.6074
