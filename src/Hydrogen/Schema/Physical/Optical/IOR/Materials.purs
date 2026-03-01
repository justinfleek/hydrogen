-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // schema // physical // ior // materials
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Index of Refraction values for crystals, metals, semiconductors, and
-- | biological materials.
-- |
-- | ## Crystals
-- | Common minerals with optical significance.
-- |
-- | ## Metals
-- | Note: Metals have complex IOR (n + ik where k is extinction coefficient).
-- | These values are the real part only, useful for Fresnel calculations.
-- | For accurate metal rendering, use full complex IOR from PBR/Metal module.
-- |
-- | ## Semiconductors
-- | High IOR materials, approaching the physical maximum (~4.0).
-- |
-- | ## Biological
-- | Human tissue IOR values for medical/scientific visualization.

module Hydrogen.Schema.Physical.Optical.IOR.Materials
  ( -- * Crystals - Cubic (n uniform)
    halite
  , fluorite
  , calcite
  , gypsum
  , mica
  
  -- * Metals - Effective IOR (complex)
  , gold
  , silver
  , copper
  , aluminum
  , iron
  , platinum
  , chromium
  , titanium
  
  -- * Semiconductors (high n)
  , silicon
  , germanium
  , galliumArsenide
  
  -- * Biological (n ~ 1.3-1.5)
  , cornea
  , lens
  , vitreous
  , skin
  , blood
  , bone
  ) where

import Hydrogen.Schema.Physical.Optical.IOR.Core (IOR, iorUnsafe)

-- ═══════════════════════════════════════════════════════════════════════════
--                                                     // crystals - minerals
-- ═══════════════════════════════════════════════════════════════════════════

-- | Halite / rock salt (n = 1.544)
halite :: IOR
halite = iorUnsafe 1.544

-- | Fluorite - low dispersion (n = 1.434)
fluorite :: IOR
fluorite = iorUnsafe 1.434

-- | Calcite (birefringent) - ordinary ray (n = 1.658)
calcite :: IOR
calcite = iorUnsafe 1.658

-- | Gypsum (n = 1.52)
gypsum :: IOR
gypsum = iorUnsafe 1.52

-- | Mica (muscovite) (n = 1.58)
mica :: IOR
mica = iorUnsafe 1.58

-- ═══════════════════════════════════════════════════════════════════════════
--                                                  // metals - effective ior
-- ═══════════════════════════════════════════════════════════════════════════

-- Note: Metals have complex IOR (n + ik where k is extinction coefficient).
-- These values are the real part only, useful for Fresnel calculations.
-- For accurate metal rendering, use full complex IOR from PBR/Metal module.

-- | Gold - warm reflection (n = 0.47, but use ~1.0 for simple Fresnel)
gold :: IOR
gold = iorUnsafe 1.0

-- | Silver (n = 0.18)
silver :: IOR
silver = iorUnsafe 1.0

-- | Copper (n = 0.96)
copper :: IOR
copper = iorUnsafe 1.0

-- | Aluminum (n = 1.44)
aluminum :: IOR
aluminum = iorUnsafe 1.44

-- | Iron (n = 2.95)
iron :: IOR
iron = iorUnsafe 2.95

-- | Platinum (n = 2.33)
platinum :: IOR
platinum = iorUnsafe 2.33

-- | Chromium (n = 3.18)
chromium :: IOR
chromium = iorUnsafe 3.18

-- | Titanium (n = 2.16)
titanium :: IOR
titanium = iorUnsafe 2.16

-- ═══════════════════════════════════════════════════════════════════════════
--                                                          // semiconductors
-- ═══════════════════════════════════════════════════════════════════════════

-- | Silicon (n = 3.48 at 589nm, higher at IR)
silicon :: IOR
silicon = iorUnsafe 3.48

-- | Germanium (n = 4.0+ at IR, ~4.0 clamped)
germanium :: IOR
germanium = iorUnsafe 4.0

-- | Gallium arsenide (n = 3.93)
galliumArsenide :: IOR
galliumArsenide = iorUnsafe 3.93

-- ═══════════════════════════════════════════════════════════════════════════
--                                                             // biological
-- ═══════════════════════════════════════════════════════════════════════════

-- | Human cornea (n = 1.376)
cornea :: IOR
cornea = iorUnsafe 1.376

-- | Human lens (n = 1.42)
lens :: IOR
lens = iorUnsafe 1.42

-- | Vitreous humor (eye interior) (n = 1.336)
vitreous :: IOR
vitreous = iorUnsafe 1.336

-- | Human skin (epidermis) (n = 1.44)
skin :: IOR
skin = iorUnsafe 1.44

-- | Blood (n = 1.36)
blood :: IOR
blood = iorUnsafe 1.36

-- | Bone (cortical) (n = 1.55)
bone :: IOR
bone = iorUnsafe 1.55
