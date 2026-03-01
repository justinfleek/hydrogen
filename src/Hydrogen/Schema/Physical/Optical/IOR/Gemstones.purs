-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // schema // physical // ior // gemstones
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Index of Refraction values for gemstones.
-- |
-- | Gemstones span a wide IOR range from 1.4 to 2.5. Diamond at 2.417 has
-- | the highest natural IOR, responsible for its famous "fire" and brilliance.
-- |
-- | ## Categories
-- | - Precious: Diamond, Ruby, Sapphire, Emerald, Alexandrite
-- | - Semi-Precious: Topaz, Tourmaline, Garnet, etc.
-- | - Quartz Family: Amethyst, Citrine, Rose Quartz, etc.
-- | - Beryl Family: Emerald, Aquamarine, Morganite, etc.
-- | - Rare/Collector: Benitoite, Painite, Taaffeite, etc.

module Hydrogen.Schema.Physical.Optical.IOR.Gemstones
  ( -- * Precious (n ~ 1.5-2.5)
    diamond
  , ruby
  , sapphire
  , emerald
  , aquamarine
  , alexandrite
  
  -- * Semi-Precious (n ~ 1.4-1.8)
  , amethyst
  , citrine
  , topaz
  , tourmaline
  , garnet
  , peridot
  , tanzanite
  , opal
  , turquoise
  , jade
  , lapis
  , malachite
  , obsidian
  , moonstone
  , labradorite
  , amazonite
  
  -- * Quartz Family (n ~ 1.54)
  , quartz
  , roseQuartz
  , smokyQuartz
  , tigerEye
  , agate
  , jasper
  , carnelian
  , onyx
  , chalcedony
  
  -- * Beryl Family (n ~ 1.57-1.60)
  , beryl
  , morganite
  , heliodor
  , goshenite
  
  -- * Rare/Collector (n ~ 1.6-2.4)
  , spinel
  , zircon
  , chrysoberyl
  , sphene
  , demantoid
  , tsavorite
  , rhodolite
  , hessonite
  , spessartine
  , benitoite
  , taaffeite
  , painite
  , musgravite
  ) where

import Hydrogen.Schema.Physical.Optical.IOR.Core (IOR, iorUnsafe)

-- ═══════════════════════════════════════════════════════════════════════════
--                                                   // gemstones - precious
-- ═══════════════════════════════════════════════════════════════════════════

-- | Diamond - highest natural IOR (n = 2.417)
-- | Famous for "fire" (dispersion) and brilliance
diamond :: IOR
diamond = iorUnsafe 2.417

-- | Ruby (corundum + chromium) (n = 1.77)
ruby :: IOR
ruby = iorUnsafe 1.77

-- | Sapphire (corundum) (n = 1.77)
sapphire :: IOR
sapphire = iorUnsafe 1.77

-- | Emerald (beryl + chromium/vanadium) (n = 1.58)
emerald :: IOR
emerald = iorUnsafe 1.58

-- | Aquamarine (beryl) (n = 1.577)
aquamarine :: IOR
aquamarine = iorUnsafe 1.577

-- | Alexandrite (chrysoberyl) - color-change gem (n = 1.746)
alexandrite :: IOR
alexandrite = iorUnsafe 1.746

-- ═══════════════════════════════════════════════════════════════════════════
--                                               // gemstones - semi-precious
-- ═══════════════════════════════════════════════════════════════════════════

-- | Amethyst (purple quartz) (n = 1.544)
amethyst :: IOR
amethyst = iorUnsafe 1.544

-- | Citrine (yellow quartz) (n = 1.544)
citrine :: IOR
citrine = iorUnsafe 1.544

-- | Topaz (n = 1.63)
topaz :: IOR
topaz = iorUnsafe 1.63

-- | Tourmaline (n = 1.64)
tourmaline :: IOR
tourmaline = iorUnsafe 1.64

-- | Garnet (almandine type) (n = 1.79)
garnet :: IOR
garnet = iorUnsafe 1.79

-- | Peridot (olivine) (n = 1.67)
peridot :: IOR
peridot = iorUnsafe 1.67

-- | Tanzanite (zoisite) (n = 1.70)
tanzanite :: IOR
tanzanite = iorUnsafe 1.70

-- | Opal - play of color, approximate (n = 1.45)
opal :: IOR
opal = iorUnsafe 1.45

-- | Turquoise (n = 1.62)
turquoise :: IOR
turquoise = iorUnsafe 1.62

-- | Jade (nephrite) (n = 1.61)
jade :: IOR
jade = iorUnsafe 1.61

-- | Lapis lazuli (n = 1.50)
lapis :: IOR
lapis = iorUnsafe 1.50

-- | Malachite (n = 1.85)
malachite :: IOR
malachite = iorUnsafe 1.85

-- | Obsidian (volcanic glass) (n = 1.50)
obsidian :: IOR
obsidian = iorUnsafe 1.50

-- | Moonstone (feldspar) (n = 1.52)
moonstone :: IOR
moonstone = iorUnsafe 1.52

-- | Labradorite (feldspar) - labradorescence (n = 1.56)
labradorite :: IOR
labradorite = iorUnsafe 1.56

-- | Amazonite (feldspar) (n = 1.53)
amazonite :: IOR
amazonite = iorUnsafe 1.53

-- ═══════════════════════════════════════════════════════════════════════════
--                                               // gemstones - quartz family
-- ═══════════════════════════════════════════════════════════════════════════

-- | Clear quartz / rock crystal (n = 1.544)
quartz :: IOR
quartz = iorUnsafe 1.544

-- | Rose quartz (n = 1.544)
roseQuartz :: IOR
roseQuartz = iorUnsafe 1.544

-- | Smoky quartz (n = 1.544)
smokyQuartz :: IOR
smokyQuartz = iorUnsafe 1.544

-- | Tiger's eye (n = 1.544)
tigerEye :: IOR
tigerEye = iorUnsafe 1.544

-- | Agate (n = 1.544)
agate :: IOR
agate = iorUnsafe 1.544

-- | Jasper (n = 1.54)
jasper :: IOR
jasper = iorUnsafe 1.54

-- | Carnelian (n = 1.544)
carnelian :: IOR
carnelian = iorUnsafe 1.544

-- | Onyx (n = 1.544)
onyx :: IOR
onyx = iorUnsafe 1.544

-- | Chalcedony (n = 1.544)
chalcedony :: IOR
chalcedony = iorUnsafe 1.544

-- ═══════════════════════════════════════════════════════════════════════════
--                                                // gemstones - beryl family
-- ═══════════════════════════════════════════════════════════════════════════

-- | Beryl (colorless) (n = 1.577)
beryl :: IOR
beryl = iorUnsafe 1.577

-- | Morganite (pink beryl) (n = 1.59)
morganite :: IOR
morganite = iorUnsafe 1.59

-- | Heliodor (yellow beryl) (n = 1.577)
heliodor :: IOR
heliodor = iorUnsafe 1.577

-- | Goshenite (colorless beryl) (n = 1.577)
goshenite :: IOR
goshenite = iorUnsafe 1.577

-- ═══════════════════════════════════════════════════════════════════════════
--                                           // gemstones - rare and collector
-- ═══════════════════════════════════════════════════════════════════════════

-- | Spinel (n = 1.72)
spinel :: IOR
spinel = iorUnsafe 1.72

-- | Zircon - high dispersion (n = 1.95)
zircon :: IOR
zircon = iorUnsafe 1.95

-- | Chrysoberyl (cat's eye) (n = 1.746)
chrysoberyl :: IOR
chrysoberyl = iorUnsafe 1.746

-- | Sphene / titanite - extreme dispersion (n = 2.0)
sphene :: IOR
sphene = iorUnsafe 2.0

-- | Demantoid garnet - "diamond-like" fire (n = 1.89)
demantoid :: IOR
demantoid = iorUnsafe 1.89

-- | Tsavorite (green garnet) (n = 1.74)
tsavorite :: IOR
tsavorite = iorUnsafe 1.74

-- | Rhodolite (purple garnet) (n = 1.76)
rhodolite :: IOR
rhodolite = iorUnsafe 1.76

-- | Hessonite (cinnamon garnet) (n = 1.74)
hessonite :: IOR
hessonite = iorUnsafe 1.74

-- | Spessartine (orange garnet) (n = 1.80)
spessartine :: IOR
spessartine = iorUnsafe 1.80

-- | Benitoite - rare California gem (n = 1.80)
benitoite :: IOR
benitoite = iorUnsafe 1.80

-- | Taaffeite - extremely rare (n = 1.72)
taaffeite :: IOR
taaffeite = iorUnsafe 1.72

-- | Painite - was rarest mineral (n = 1.79)
painite :: IOR
painite = iorUnsafe 1.79

-- | Musgravite - rarer than painite (n = 1.72)
musgravite :: IOR
musgravite = iorUnsafe 1.72
