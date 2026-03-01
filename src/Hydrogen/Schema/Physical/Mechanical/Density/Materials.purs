-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--          // hydrogen // schema // physical // mechanical // density // materials
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Material density database in kg/m³.
-- |
-- | ## Data Sources
-- |
-- | CRC Handbook of Chemistry and Physics, MatWeb materials database,
-- | engineering reference tables. All values at 20°C unless noted.
-- |
-- | This module re-exports all material categories for convenience.

module Hydrogen.Schema.Physical.Mechanical.Density.Materials
  ( module Gases
  , module Liquids
  , module Woods
  , module Polymers
  , module Building
  , module Metals
  , module Gemstones
  , module Other
  ) where

import Hydrogen.Schema.Physical.Mechanical.Density.Materials.Gases as Gases
import Hydrogen.Schema.Physical.Mechanical.Density.Materials.Liquids as Liquids
import Hydrogen.Schema.Physical.Mechanical.Density.Materials.Woods as Woods
import Hydrogen.Schema.Physical.Mechanical.Density.Materials.Polymers as Polymers
import Hydrogen.Schema.Physical.Mechanical.Density.Materials.Building as Building
import Hydrogen.Schema.Physical.Mechanical.Density.Materials.Metals as Metals
import Hydrogen.Schema.Physical.Mechanical.Density.Materials.Gemstones as Gemstones
import Hydrogen.Schema.Physical.Mechanical.Density.Materials.Other as Other
