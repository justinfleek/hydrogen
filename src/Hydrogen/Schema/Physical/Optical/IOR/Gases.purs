-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // physical // ior // gases
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Index of Refraction values for gases.
-- |
-- | Gases have IOR values extremely close to 1.0 (vacuum). The difference
-- | from unity is typically in the 4th-6th decimal place.

module Hydrogen.Schema.Physical.Optical.IOR.Gases
  ( -- * Gases (n ~ 1.0)
    vacuum
  , air
  , helium
  , hydrogen
  , oxygen
  , nitrogen
  , carbonDioxide
  , methane
  , argon
  , neon
  ) where

import Hydrogen.Schema.Physical.Optical.IOR.Core (IOR, iorUnsafe)

-- ═══════════════════════════════════════════════════════════════════════════
--                                                                     // gases
-- ═══════════════════════════════════════════════════════════════════════════

-- | Vacuum - reference point (n = 1.0 exactly)
vacuum :: IOR
vacuum = iorUnsafe 1.0

-- | Air at STP (n = 1.000293)
air :: IOR
air = iorUnsafe 1.000293

-- | Helium (n = 1.000036)
helium :: IOR
helium = iorUnsafe 1.000036

-- | Hydrogen (n = 1.000132)
hydrogen :: IOR
hydrogen = iorUnsafe 1.000132

-- | Oxygen (n = 1.000271)
oxygen :: IOR
oxygen = iorUnsafe 1.000271

-- | Nitrogen (n = 1.000298)
nitrogen :: IOR
nitrogen = iorUnsafe 1.000298

-- | Carbon dioxide (n = 1.00045)
carbonDioxide :: IOR
carbonDioxide = iorUnsafe 1.00045

-- | Methane (n = 1.000444)
methane :: IOR
methane = iorUnsafe 1.000444

-- | Argon (n = 1.000281)
argon :: IOR
argon = iorUnsafe 1.000281

-- | Neon (n = 1.000067)
neon :: IOR
neon = iorUnsafe 1.000067
