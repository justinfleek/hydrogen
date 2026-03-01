-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- // hydrogen // schema // physical // mechanical // density // materials // building
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Building material density values.
-- |
-- | All values in kg/m³.

module Hydrogen.Schema.Physical.Mechanical.Density.Materials.Building
  ( concrete
  , brick
  , glass
  , granite
  , marble
  , limestone
  , sandstone
  , slate
  , plaster
  , cement
  , asphalt
  ) where

import Hydrogen.Schema.Physical.Mechanical.Density.Types (Density, densityUnsafe)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // building materials
-- ═════════════════════════════════════════════════════════════════════════════

-- | Concrete — reinforced average
concrete :: Density
concrete = densityUnsafe 2400.0

-- | Brick — common red
brick :: Density
brick = densityUnsafe 1920.0

-- | Glass — soda-lime
glass :: Density
glass = densityUnsafe 2500.0

-- | Granite — igneous rock
granite :: Density
granite = densityUnsafe 2700.0

-- | Marble — metamorphic rock
marble :: Density
marble = densityUnsafe 2700.0

-- | Limestone — sedimentary
limestone :: Density
limestone = densityUnsafe 2500.0

-- | Sandstone — sedimentary
sandstone :: Density
sandstone = densityUnsafe 2300.0

-- | Slate — metamorphic
slate :: Density
slate = densityUnsafe 2800.0

-- | Plaster — gypsum-based
plaster :: Density
plaster = densityUnsafe 1200.0

-- | Portland cement — powder
cement :: Density
cement = densityUnsafe 1500.0

-- | Asphalt — bitumen mix
asphalt :: Density
asphalt = densityUnsafe 2400.0
