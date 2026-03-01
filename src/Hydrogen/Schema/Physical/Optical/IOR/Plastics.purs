-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // physical // ior // plastics
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Index of Refraction values for plastics and polymers.
-- |
-- | Plastics typically have IOR values in the range 1.35-1.6.
-- | PMMA/acrylic at 1.49 is the most common optical plastic.

module Hydrogen.Schema.Physical.Optical.IOR.Plastics
  ( -- * Plastics & Polymers (n ~ 1.4-1.6)
    acrylic
  , pmma
  , polycarbonate
  , polystyrene
  , polyethylene
  , pvc
  , nylon
  , teflon
  , epoxy
  , silicone
  ) where

import Hydrogen.Schema.Physical.Optical.IOR.Core (IOR, iorUnsafe)

-- ═══════════════════════════════════════════════════════════════════════════
--                                                     // plastics and polymers
-- ═══════════════════════════════════════════════════════════════════════════

-- | Acrylic / Plexiglass (n = 1.49)
acrylic :: IOR
acrylic = iorUnsafe 1.49

-- | PMMA (polymethyl methacrylate) - same as acrylic (n = 1.49)
pmma :: IOR
pmma = iorUnsafe 1.49

-- | Polycarbonate (Lexan) (n = 1.586)
polycarbonate :: IOR
polycarbonate = iorUnsafe 1.586

-- | Polystyrene (n = 1.59)
polystyrene :: IOR
polystyrene = iorUnsafe 1.59

-- | Polyethylene (n = 1.51)
polyethylene :: IOR
polyethylene = iorUnsafe 1.51

-- | PVC (polyvinyl chloride) (n = 1.54)
pvc :: IOR
pvc = iorUnsafe 1.54

-- | Nylon (n = 1.53)
nylon :: IOR
nylon = iorUnsafe 1.53

-- | Teflon / PTFE (n = 1.35)
teflon :: IOR
teflon = iorUnsafe 1.35

-- | Epoxy resin (n = 1.55)
epoxy :: IOR
epoxy = iorUnsafe 1.55

-- | Silicone rubber (n = 1.43)
silicone :: IOR
silicone = iorUnsafe 1.43
