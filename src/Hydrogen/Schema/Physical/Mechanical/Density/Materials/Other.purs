-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--   // hydrogen // schema // physical // mechanical // density // materials // other
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Miscellaneous material density values.
-- |
-- | Includes natural materials, biological tissues, and other substances.
-- |
-- | All values in kg/m³.

module Hydrogen.Schema.Physical.Mechanical.Density.Materials.Other
  ( ice
  , snow
  , sand
  , soil
  , clay
  , charcoal
  , graphite
  , silicon
  , bone
  , muscle
  , fat
  ) where

import Hydrogen.Schema.Physical.Mechanical.Density.Types (Density, densityUnsafe)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // other materials
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ice (water ice at 0°C)
ice :: Density
ice = densityUnsafe 917.0

-- | Snow — freshly fallen, loose
snow :: Density
snow = densityUnsafe 100.0

-- | Sand — dry, loose
sand :: Density
sand = densityUnsafe 1600.0

-- | Soil — average garden
soil :: Density
soil = densityUnsafe 1500.0

-- | Clay — wet
clay :: Density
clay = densityUnsafe 1800.0

-- | Charcoal — wood
charcoal :: Density
charcoal = densityUnsafe 400.0

-- | Graphite — carbon allotrope
graphite :: Density
graphite = densityUnsafe 2250.0

-- | Silicon — semiconductor grade
silicon :: Density
silicon = densityUnsafe 2330.0

-- | Bone — cortical (compact)
bone :: Density
bone = densityUnsafe 1900.0

-- | Muscle — human
muscle :: Density
muscle = densityUnsafe 1060.0

-- | Fat — adipose tissue
fat :: Density
fat = densityUnsafe 920.0
