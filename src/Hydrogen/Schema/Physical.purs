-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // schema // physical
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Physical pillar — real-world material properties for accurate simulation.
-- |
-- | ## Overview
-- |
-- | The Physical pillar provides scientifically accurate material properties
-- | for rendering, haptics, physics simulation, and sensor feedback. Every
-- | value is bounded and sourced from peer-reviewed data.
-- |
-- | ## Submodules
-- |
-- | ### Element
-- | Periodic table elements with complete atomic data.
-- |
-- | ### Optical
-- | Light interaction properties:
-- | - IOR: Index of Refraction for ~100 materials
-- | - Dispersion: Abbe number and gemstone "fire"
-- |
-- | ### Mechanical
-- | Physical structure properties:
-- | - Hardness: Mohs scale (1-15, extended for synthetics)
-- | - Density: kg/m³ database (~100 materials)
-- |
-- | ### Thermal
-- | Heat transfer properties:
-- | - Conductivity: W/(m·K) for ~80 materials
-- |
-- | ### Haptic
-- | Touch feedback primitives:
-- | - Force: Newton-based haptic effects
-- | - Vibration, texture, impact, resistance presets
-- |
-- | ### Material
-- | Complete material definitions:
-- | - StandardSurface: MaterialX-compatible PBR shader
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Physical as Physical
-- | import Hydrogen.Schema.Physical.Optical.IOR as IOR
-- | import Hydrogen.Schema.Physical.Mechanical.Density as Density
-- | 
-- | -- Create a gold material description
-- | goldProperties =
-- |   { ior: IOR.gold
-- |   , density: Density.gold
-- |   , hardness: Hardness.gold
-- |   , thermalK: Conductivity.gold
-- |   }
-- | ```
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Agents creating virtual materials compose from these atoms. Same properties
-- | = same physical behavior across all simulations. No ambiguity about what
-- | "gold" means — it's the same density, hardness, and thermal conductivity
-- | everywhere.

module Hydrogen.Schema.Physical
  ( -- * Element Core
    module Element
  
  -- * Element Classification
  , module Block
  , module Period
  , module Group
  , module Category
  , module Symbol
  ) where

import Hydrogen.Schema.Physical.Element
  ( Element(Hydrogen, Helium, Lithium, Beryllium, Boron, Carbon, Nitrogen, Oxygen, Fluorine, Neon, Sodium, Magnesium, Aluminium, Silicon, Phosphorus, Sulfur, Chlorine, Argon, Potassium, Calcium, Scandium, Titanium, Vanadium, Chromium, Manganese, Iron, Cobalt, Nickel, Copper, Zinc, Gallium, Germanium, Arsenic, Selenium, Bromine, Krypton, Rubidium, Strontium, Yttrium, Zirconium, Niobium, Molybdenum, Technetium, Ruthenium, Rhodium, Palladium, Silver, Cadmium, Indium, Tin, Antimony, Tellurium, Iodine, Xenon, Cesium, Barium, Lanthanum, Cerium, Praseodymium, Neodymium, Promethium, Samarium, Europium, Gadolinium, Terbium, Dysprosium, Holmium, Erbium, Thulium, Ytterbium, Lutetium, Hafnium, Tantalum, Tungsten, Rhenium, Osmium, Iridium, Platinum, Gold, Mercury, Thallium, Lead, Bismuth, Polonium, Astatine, Radon, Francium, Radium, Actinium, Thorium, Protactinium, Uranium, Neptunium, Plutonium, Americium, Curium, Berkelium, Californium, Einsteinium, Fermium, Mendelevium, Nobelium, Lawrencium, Rutherfordium, Dubnium, Seaborgium, Bohrium, Hassium, Meitnerium, Darmstadtium, Roentgenium, Copernicium, Nihonium, Flerovium, Moscovium, Livermorium, Tennessine, Oganesson)
  , allElements
  , AtomicNumber
  , atomicNumber
  , mkAtomicNumber
  , unwrapAtomicNumber
  , atomicNumberBounds
  , fromAtomicNumber
  ) as Element

import Hydrogen.Schema.Physical.Element.Block
  ( ElementBlock(SBlock, PBlock, DBlock, FBlock)
  , allElementBlocks
  , block
  ) as Block

import Hydrogen.Schema.Physical.Element.Period
  ( Period
  , mkPeriod
  , unwrapPeriod
  , period
  , periodBounds
  ) as Period

import Hydrogen.Schema.Physical.Element.Group
  ( Group
  , mkGroup
  , unwrapGroup
  , group
  , groupBounds
  ) as Group

import Hydrogen.Schema.Physical.Element.Category
  ( ElementCategory(AlkaliMetal, AlkalineEarthMetal, TransitionMetal, PostTransitionMetal, Metalloid, ReactiveNonmetal, NobleGas, Lanthanide, Actinide, Unknown)
  , allElementCategories
  , category
  ) as Category

import Hydrogen.Schema.Physical.Element.Symbol
  ( symbol
  , name
  , fromSymbol
  ) as Symbol

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // module // index
-- ═════════════════════════════════════════════════════════════════════════════

-- | ## Complete Module List
-- |
-- | ### Core
-- | - Hydrogen.Schema.Physical.Element
-- | - Hydrogen.Schema.Physical.Element.Block
-- | - Hydrogen.Schema.Physical.Element.Period
-- | - Hydrogen.Schema.Physical.Element.Group
-- | - Hydrogen.Schema.Physical.Element.Category
-- | - Hydrogen.Schema.Physical.Element.Symbol
-- |
-- | ### Optical
-- | - Hydrogen.Schema.Physical.Optical.IOR
-- | - Hydrogen.Schema.Physical.Optical.Dispersion
-- |
-- | ### Mechanical
-- | - Hydrogen.Schema.Physical.Mechanical.Hardness
-- | - Hydrogen.Schema.Physical.Mechanical.Density
-- |
-- | ### Thermal
-- | - Hydrogen.Schema.Physical.Thermal.Conductivity
-- |
-- | ### Haptic
-- | - Hydrogen.Schema.Physics.Haptic.Force
-- |
-- | ### Material
-- | - Hydrogen.Schema.Spatial.Material.StandardSurface

-- Note: We don't re-export Optical, Mechanical, Thermal, Haptic, Material
-- to avoid name collisions. Users should import those qualified.
-- The Element types are re-exported as they form the atomic vocabulary.
