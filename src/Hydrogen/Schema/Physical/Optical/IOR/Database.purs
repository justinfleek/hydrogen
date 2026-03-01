-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // physical // ior // database
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Complete IOR material database for lookup operations.
-- |
-- | Provides a unified view of all named materials with their IOR values
-- | and category classifications.

module Hydrogen.Schema.Physical.Optical.IOR.Database
  ( allMaterials
  ) where

import Hydrogen.Schema.Physical.Optical.IOR.Core
  ( IOR
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
  )

import Hydrogen.Schema.Physical.Optical.IOR.Gases as Gases
import Hydrogen.Schema.Physical.Optical.IOR.Liquids as Liquids
import Hydrogen.Schema.Physical.Optical.IOR.Glass as Glass
import Hydrogen.Schema.Physical.Optical.IOR.Plastics as Plastics
import Hydrogen.Schema.Physical.Optical.IOR.Gemstones as Gems
import Hydrogen.Schema.Physical.Optical.IOR.Materials as Mats

-- ═══════════════════════════════════════════════════════════════════════════
--                                                               // database
-- ═══════════════════════════════════════════════════════════════════════════

-- | All named materials with their IOR values
-- | Format: Array { name :: String, ior :: IOR, category :: MaterialCategory }
allMaterials :: Array { name :: String, ior :: IOR, cat :: MaterialCategory }
allMaterials =
  -- Gases
  [ { name: "vacuum", ior: Gases.vacuum, cat: Gas }
  , { name: "air", ior: Gases.air, cat: Gas }
  , { name: "helium", ior: Gases.helium, cat: Gas }
  , { name: "hydrogen", ior: Gases.hydrogen, cat: Gas }
  , { name: "oxygen", ior: Gases.oxygen, cat: Gas }
  , { name: "nitrogen", ior: Gases.nitrogen, cat: Gas }
  , { name: "carbon dioxide", ior: Gases.carbonDioxide, cat: Gas }
  , { name: "methane", ior: Gases.methane, cat: Gas }
  , { name: "argon", ior: Gases.argon, cat: Gas }
  , { name: "neon", ior: Gases.neon, cat: Gas }
  -- Liquids
  , { name: "water", ior: Liquids.water, cat: Liquid }
  , { name: "water ice", ior: Liquids.waterIce, cat: Liquid }
  , { name: "seawater", ior: Liquids.seawater, cat: Liquid }
  , { name: "ethanol", ior: Liquids.ethanol, cat: Liquid }
  , { name: "methanol", ior: Liquids.methanol, cat: Liquid }
  , { name: "acetone", ior: Liquids.acetone, cat: Liquid }
  , { name: "glycerol", ior: Liquids.glycerol, cat: Liquid }
  , { name: "benzene", ior: Liquids.benzene, cat: Liquid }
  , { name: "toluene", ior: Liquids.toluene, cat: Liquid }
  , { name: "carbon disulfide", ior: Liquids.carbonDisulfide, cat: Liquid }
  , { name: "olive oil", ior: Liquids.oliveoil, cat: Liquid }
  , { name: "turpentine", ior: Liquids.turpentine, cat: Liquid }
  , { name: "honey", ior: Liquids.honey, cat: Liquid }
  -- Glass
  , { name: "soda-lime glass", ior: Glass.sodaLimeGlass, cat: Glass }
  , { name: "borosilicate glass", ior: Glass.borosilicateGlass, cat: Glass }
  , { name: "crown glass", ior: Glass.crownGlass, cat: Glass }
  , { name: "flint glass", ior: Glass.flintGlass, cat: Glass }
  , { name: "dense flint glass", ior: Glass.denseFlintGlass, cat: Glass }
  , { name: "lead glass", ior: Glass.leadGlass, cat: Glass }
  , { name: "fused silica", ior: Glass.fusedSilica, cat: Glass }
  , { name: "pyrex", ior: Glass.pyrex, cat: Glass }
  , { name: "BK7", ior: Glass.bk7, cat: Glass }
  , { name: "SF11", ior: Glass.sf11, cat: Glass }
  , { name: "LAF2", ior: Glass.laf2, cat: Glass }
  , { name: "LASF9", ior: Glass.lasf9, cat: Glass }
  , { name: "N-BK7", ior: Glass.nbk7, cat: Glass }
  , { name: "N-SK2", ior: Glass.nsk2, cat: Glass }
  -- Plastics
  , { name: "acrylic", ior: Plastics.acrylic, cat: Plastic }
  , { name: "PMMA", ior: Plastics.pmma, cat: Plastic }
  , { name: "polycarbonate", ior: Plastics.polycarbonate, cat: Plastic }
  , { name: "polystyrene", ior: Plastics.polystyrene, cat: Plastic }
  , { name: "polyethylene", ior: Plastics.polyethylene, cat: Plastic }
  , { name: "PVC", ior: Plastics.pvc, cat: Plastic }
  , { name: "nylon", ior: Plastics.nylon, cat: Plastic }
  , { name: "teflon", ior: Plastics.teflon, cat: Plastic }
  , { name: "epoxy", ior: Plastics.epoxy, cat: Plastic }
  , { name: "silicone", ior: Plastics.silicone, cat: Plastic }
  -- Precious gemstones
  , { name: "diamond", ior: Gems.diamond, cat: GemPrecious }
  , { name: "ruby", ior: Gems.ruby, cat: GemPrecious }
  , { name: "sapphire", ior: Gems.sapphire, cat: GemPrecious }
  , { name: "emerald", ior: Gems.emerald, cat: GemPrecious }
  , { name: "aquamarine", ior: Gems.aquamarine, cat: GemPrecious }
  , { name: "alexandrite", ior: Gems.alexandrite, cat: GemPrecious }
  -- Semi-precious gemstones
  , { name: "amethyst", ior: Gems.amethyst, cat: GemSemiPrecious }
  , { name: "citrine", ior: Gems.citrine, cat: GemSemiPrecious }
  , { name: "topaz", ior: Gems.topaz, cat: GemSemiPrecious }
  , { name: "tourmaline", ior: Gems.tourmaline, cat: GemSemiPrecious }
  , { name: "garnet", ior: Gems.garnet, cat: GemSemiPrecious }
  , { name: "peridot", ior: Gems.peridot, cat: GemSemiPrecious }
  , { name: "tanzanite", ior: Gems.tanzanite, cat: GemSemiPrecious }
  , { name: "opal", ior: Gems.opal, cat: GemSemiPrecious }
  , { name: "turquoise", ior: Gems.turquoise, cat: GemSemiPrecious }
  , { name: "jade", ior: Gems.jade, cat: GemSemiPrecious }
  , { name: "lapis lazuli", ior: Gems.lapis, cat: GemSemiPrecious }
  , { name: "malachite", ior: Gems.malachite, cat: GemSemiPrecious }
  , { name: "obsidian", ior: Gems.obsidian, cat: GemSemiPrecious }
  , { name: "moonstone", ior: Gems.moonstone, cat: GemSemiPrecious }
  , { name: "labradorite", ior: Gems.labradorite, cat: GemSemiPrecious }
  , { name: "amazonite", ior: Gems.amazonite, cat: GemSemiPrecious }
  -- Quartz family
  , { name: "quartz", ior: Gems.quartz, cat: GemQuartz }
  , { name: "rose quartz", ior: Gems.roseQuartz, cat: GemQuartz }
  , { name: "smoky quartz", ior: Gems.smokyQuartz, cat: GemQuartz }
  , { name: "tiger eye", ior: Gems.tigerEye, cat: GemQuartz }
  , { name: "agate", ior: Gems.agate, cat: GemQuartz }
  , { name: "jasper", ior: Gems.jasper, cat: GemQuartz }
  , { name: "carnelian", ior: Gems.carnelian, cat: GemQuartz }
  , { name: "onyx", ior: Gems.onyx, cat: GemQuartz }
  , { name: "chalcedony", ior: Gems.chalcedony, cat: GemQuartz }
  -- Beryl family
  , { name: "beryl", ior: Gems.beryl, cat: GemBeryl }
  , { name: "morganite", ior: Gems.morganite, cat: GemBeryl }
  , { name: "heliodor", ior: Gems.heliodor, cat: GemBeryl }
  , { name: "goshenite", ior: Gems.goshenite, cat: GemBeryl }
  -- Rare gemstones
  , { name: "spinel", ior: Gems.spinel, cat: GemRare }
  , { name: "zircon", ior: Gems.zircon, cat: GemRare }
  , { name: "chrysoberyl", ior: Gems.chrysoberyl, cat: GemRare }
  , { name: "sphene", ior: Gems.sphene, cat: GemRare }
  , { name: "demantoid", ior: Gems.demantoid, cat: GemRare }
  , { name: "tsavorite", ior: Gems.tsavorite, cat: GemRare }
  , { name: "rhodolite", ior: Gems.rhodolite, cat: GemRare }
  , { name: "hessonite", ior: Gems.hessonite, cat: GemRare }
  , { name: "spessartine", ior: Gems.spessartine, cat: GemRare }
  , { name: "benitoite", ior: Gems.benitoite, cat: GemRare }
  , { name: "taaffeite", ior: Gems.taaffeite, cat: GemRare }
  , { name: "painite", ior: Gems.painite, cat: GemRare }
  , { name: "musgravite", ior: Gems.musgravite, cat: GemRare }
  -- Crystals
  , { name: "halite", ior: Mats.halite, cat: Crystal }
  , { name: "fluorite", ior: Mats.fluorite, cat: Crystal }
  , { name: "calcite", ior: Mats.calcite, cat: Crystal }
  , { name: "gypsum", ior: Mats.gypsum, cat: Crystal }
  , { name: "mica", ior: Mats.mica, cat: Crystal }
  -- Metals
  , { name: "gold", ior: Mats.gold, cat: Metal }
  , { name: "silver", ior: Mats.silver, cat: Metal }
  , { name: "copper", ior: Mats.copper, cat: Metal }
  , { name: "aluminum", ior: Mats.aluminum, cat: Metal }
  , { name: "iron", ior: Mats.iron, cat: Metal }
  , { name: "platinum", ior: Mats.platinum, cat: Metal }
  , { name: "chromium", ior: Mats.chromium, cat: Metal }
  , { name: "titanium", ior: Mats.titanium, cat: Metal }
  -- Semiconductors
  , { name: "silicon", ior: Mats.silicon, cat: Semiconductor }
  , { name: "germanium", ior: Mats.germanium, cat: Semiconductor }
  , { name: "gallium arsenide", ior: Mats.galliumArsenide, cat: Semiconductor }
  -- Biological
  , { name: "cornea", ior: Mats.cornea, cat: Biological }
  , { name: "lens", ior: Mats.lens, cat: Biological }
  , { name: "vitreous", ior: Mats.vitreous, cat: Biological }
  , { name: "skin", ior: Mats.skin, cat: Biological }
  , { name: "blood", ior: Mats.blood, cat: Biological }
  , { name: "bone", ior: Mats.bone, cat: Biological }
  ]
