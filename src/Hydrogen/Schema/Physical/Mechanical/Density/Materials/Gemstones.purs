-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- // hydrogen // schema // physical // mechanical // density // materials // gemstones
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Gemstone density values.
-- |
-- | All values in kg/m³.

module Hydrogen.Schema.Physical.Mechanical.Density.Materials.Gemstones
  ( diamond
  , ruby
  , sapphire
  , emerald
  , topaz
  , amethyst
  , opal
  , turquoise
  ) where

import Hydrogen.Schema.Physical.Mechanical.Density.Types (Density, densityUnsafe)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // gemstones
-- ═════════════════════════════════════════════════════════════════════════════

-- | Diamond — carbon crystal
diamond :: Density
diamond = densityUnsafe 3520.0

-- | Ruby — corundum (red)
ruby :: Density
ruby = densityUnsafe 4000.0

-- | Sapphire — corundum (non-red)
sapphire :: Density
sapphire = densityUnsafe 4000.0

-- | Emerald — beryl variety
emerald :: Density
emerald = densityUnsafe 2760.0

-- | Topaz — aluminum silicate
topaz :: Density
topaz = densityUnsafe 3550.0

-- | Amethyst — quartz variety
amethyst :: Density
amethyst = densityUnsafe 2650.0

-- | Opal — hydrated silica
opal :: Density
opal = densityUnsafe 2100.0

-- | Turquoise — copper phosphate
turquoise :: Density
turquoise = densityUnsafe 2750.0
