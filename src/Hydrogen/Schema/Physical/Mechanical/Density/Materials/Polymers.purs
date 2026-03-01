-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- // hydrogen // schema // physical // mechanical // density // materials // polymers
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Plastic and polymer density values.
-- |
-- | All values in kg/m³.

module Hydrogen.Schema.Physical.Mechanical.Density.Materials.Polymers
  ( styrofoam
  , polyethylene
  , polypropylene
  , pvc
  , acrylic
  , polycarbonate
  , nylon
  , teflon
  , epoxy
  , rubber
  , silicone
  ) where

import Hydrogen.Schema.Physical.Mechanical.Density.Types (Density, densityUnsafe)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // plastics & polymers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Expanded polystyrene (Styrofoam)
styrofoam :: Density
styrofoam = densityUnsafe 50.0

-- | Polyethylene (PE) — HDPE/LDPE average
polyethylene :: Density
polyethylene = densityUnsafe 950.0

-- | Polypropylene (PP)
polypropylene :: Density
polypropylene = densityUnsafe 905.0

-- | Polyvinyl chloride (PVC)
pvc :: Density
pvc = densityUnsafe 1400.0

-- | Acrylic (PMMA) — Plexiglass
acrylic :: Density
acrylic = densityUnsafe 1180.0

-- | Polycarbonate — Lexan
polycarbonate :: Density
polycarbonate = densityUnsafe 1200.0

-- | Nylon (PA) — polyamide
nylon :: Density
nylon = densityUnsafe 1150.0

-- | PTFE (Teflon)
teflon :: Density
teflon = densityUnsafe 2200.0

-- | Epoxy resin — cured
epoxy :: Density
epoxy = densityUnsafe 1200.0

-- | Natural rubber
rubber :: Density
rubber = densityUnsafe 1100.0

-- | Silicone rubber
silicone :: Density
silicone = densityUnsafe 1100.0
