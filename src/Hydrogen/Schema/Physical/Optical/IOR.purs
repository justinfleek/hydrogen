-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // physical // optical // ior
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Complete Index of Refraction database for physically accurate rendering.
-- |
-- | ## What is IOR?
-- |
-- | The Index of Refraction (n) describes how much light slows down and bends
-- | when entering a material. It's the ratio of light speed in vacuum to light
-- | speed in the material: n = c / v
-- |
-- | ## Physical Bounds
-- |
-- | - **Minimum**: 1.0 (vacuum, by definition)
-- | - **Maximum**: ~4.0 (germanium at infrared wavelengths)
-- | - **Common range**: 1.0 - 2.5 for visible light applications
-- |
-- | ## Why This Matters
-- |
-- | At billion-agent scale, agents simulating materials need deterministic,
-- | physically accurate values. When an agent creates "diamond glass" or
-- | simulates "underwater viewing", they compose from these verified atoms.
-- |
-- | For haptic/BMI applications, correct IOR affects:
-- | - Visual perception of material density
-- | - Sparkle and fire in gemstones
-- | - Underwater distortion effects
-- | - Lens and optical instrument simulation
-- |
-- | ## Data Sources
-- |
-- | Values from: CRC Handbook of Chemistry and Physics, Gemological Institute
-- | of America (GIA), peer-reviewed optical physics literature. All values
-- | for sodium D-line (589nm) unless otherwise noted.
-- |
-- | ## Module Structure
-- |
-- | This is a leader module re-exporting from:
-- | - `IOR.Core` - Type definition, operations, predicates, categories
-- | - `IOR.Gases` - Vacuum, air, noble gases
-- | - `IOR.Liquids` - Water, alcohols, organic solvents
-- | - `IOR.Glass` - Common and optical glass types
-- | - `IOR.Plastics` - Polymers and synthetic materials
-- | - `IOR.Gemstones` - Precious, semi-precious, quartz, beryl, rare
-- | - `IOR.Materials` - Crystals, metals, semiconductors, biological
-- | - `IOR.Database` - Complete material lookup table

module Hydrogen.Schema.Physical.Optical.IOR
  ( -- * Core Type
    module Core
  
  -- * Gases (n ~ 1.0)
  , module Gases
  
  -- * Liquids (n ~ 1.3-1.5)
  , module Liquids
  
  -- * Glass (n ~ 1.5-1.9)
  , module Glass
  
  -- * Plastics & Polymers (n ~ 1.4-1.6)
  , module Plastics
  
  -- * Gemstones (n ~ 1.4-2.5)
  , module Gemstones
  
  -- * Crystals, Metals, Semiconductors, Biological
  , module Materials
  
  -- * Lookup
  , module Database
  ) where

import Hydrogen.Schema.Physical.Optical.IOR.Core
  ( IOR
  , ior
  , iorUnsafe
  , unwrap
  , bounds
  , fresnel0
  , criticalAngle
  , blend
  , lerp
  , isGas
  , isLiquid
  , isGlass
  , isGemstone
  , isMetal
  , totalInternalReflection
  , MaterialCategory
    ( Gas
    , Liquid
    , Glass
    , Plastic
    , GemPrecious
    , GemSemiPrecious
    , GemQuartz
    , GemBeryl
    , GemRare
    , Crystal
    , Metal
    , Semiconductor
    , Biological
    )
  , category
  ) as Core

import Hydrogen.Schema.Physical.Optical.IOR.Gases
  ( vacuum
  , air
  , helium
  , hydrogen
  , oxygen
  , nitrogen
  , carbonDioxide
  , methane
  , argon
  , neon
  ) as Gases

import Hydrogen.Schema.Physical.Optical.IOR.Liquids
  ( water
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
  ) as Liquids

import Hydrogen.Schema.Physical.Optical.IOR.Glass
  ( sodaLimeGlass
  , borosilicateGlass
  , crownGlass
  , flintGlass
  , denseFlintGlass
  , leadGlass
  , fusedSilica
  , pyrex
  , bk7
  , sf11
  , laf2
  , lasf9
  , nbk7
  , nsk2
  ) as Glass

import Hydrogen.Schema.Physical.Optical.IOR.Plastics
  ( acrylic
  , pmma
  , polycarbonate
  , polystyrene
  , polyethylene
  , pvc
  , nylon
  , teflon
  , epoxy
  , silicone
  ) as Plastics

import Hydrogen.Schema.Physical.Optical.IOR.Gemstones
  ( diamond
  , ruby
  , sapphire
  , emerald
  , aquamarine
  , alexandrite
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
  , quartz
  , roseQuartz
  , smokyQuartz
  , tigerEye
  , agate
  , jasper
  , carnelian
  , onyx
  , chalcedony
  , beryl
  , morganite
  , heliodor
  , goshenite
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
  ) as Gemstones

import Hydrogen.Schema.Physical.Optical.IOR.Materials
  ( halite
  , fluorite
  , calcite
  , gypsum
  , mica
  , gold
  , silver
  , copper
  , aluminum
  , iron
  , platinum
  , chromium
  , titanium
  , silicon
  , germanium
  , galliumArsenide
  , cornea
  , lens
  , vitreous
  , skin
  , blood
  , bone
  ) as Materials

import Hydrogen.Schema.Physical.Optical.IOR.Database
  ( allMaterials
  ) as Database
