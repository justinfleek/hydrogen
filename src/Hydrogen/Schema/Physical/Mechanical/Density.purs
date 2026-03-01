-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                // hydrogen // schema // physical // mechanical // density
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Material density database in kg/m³.
-- |
-- | ## What is Density?
-- |
-- | Density (ρ) is mass per unit volume: ρ = m/V
-- | SI unit: kg/m³ (kilograms per cubic meter)
-- |
-- | ## Physical Bounds
-- |
-- | - **Minimum**: ~0.00008 kg/m³ (interstellar medium)
-- | - **Maximum**: ~22,590 kg/m³ (osmium, densest stable element)
-- | - **Exotic**: Neutron star matter ~10^17 kg/m³ (not rendered)
-- |
-- | For practical materials we bound [0.001, 50000.0] kg/m³.
-- |
-- | ## Why This Matters
-- |
-- | At billion-agent scale, density determines:
-- | - Haptic feedback weight perception
-- | - Physics simulation (gravity, buoyancy, inertia)
-- | - Audio properties (denser materials ring longer)
-- | - Manufacturing simulation (material costs, structural loads)
-- |
-- | ## Data Sources
-- |
-- | CRC Handbook of Chemistry and Physics, MatWeb materials database,
-- | engineering reference tables. All values at 20°C unless noted.
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from:
-- | - `Types`: Core Density type and constructors
-- | - `Materials`: All material density constants
-- | - `Operations`: Functions operating on Density values

module Hydrogen.Schema.Physical.Mechanical.Density
  ( module Types
  , module Materials
  , module Operations
  ) where

import Hydrogen.Schema.Physical.Mechanical.Density.Types
  ( Density
  , bounds
  , density
  , densityUnsafe
  , gPerCm3
  , kgPerM3
  , unwrap
  ) as Types

import Hydrogen.Schema.Physical.Mechanical.Density.Materials
  ( acetone
  , acrylic
  , air
  , aluminum
  , amethyst
  , argon
  , asphalt
  , balsa
  , bamboo
  , blood
  , bone
  , brass
  , brick
  , bronze
  , butane
  , carbonDioxide
  , cement
  , charcoal
  , chromium
  , clay
  , concrete
  , copper
  , cork
  , diamond
  , diesel
  , ebony
  , emerald
  , epoxy
  , ethanol
  , fat
  , gasoline
  , glass
  , glycerol
  , gold
  , granite
  , graphite
  , helium
  , honey
  , hydrogen
  , ice
  , iridium
  , iron
  , kerosene
  , lead
  , limestone
  , lithium
  , magnesium
  , mahogany
  , maple
  , marble
  , mercury
  , methane
  , methanol
  , milk
  , muscle
  , nickel
  , nitrogen
  , nylon
  , oak
  , oliveoil
  , opal
  , osmium
  , oxygen
  , palladium
  , pine
  , plaster
  , platinum
  , polycarbonate
  , polyethylene
  , polypropylene
  , propane
  , pvc
  , rhodium
  , rubber
  , ruby
  , sand
  , sandstone
  , sapphire
  , seawater
  , silicon
  , silicone
  , silver
  , slate
  , snow
  , soil
  , stainlessSteel
  , steel
  , styrofoam
  , teak
  , teflon
  , tin
  , titanium
  , topaz
  , tungsten
  , turquoise
  , uranium
  , walnut
  , water
  , zinc
  ) as Materials

import Hydrogen.Schema.Physical.Mechanical.Density.Operations
  ( floatsIn
  , isLighterThan
  , lerp
  , relativeToWater
  ) as Operations
