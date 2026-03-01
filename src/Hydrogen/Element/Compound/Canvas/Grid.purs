-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // element // compound // canvas // grid
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas Grid — Bounded visual grids with snap points.
-- |
-- | ## Leader Module
-- |
-- | This module re-exports all grid functionality from submodules:
-- |
-- | - **Grid.Types**: Core types (GridSpacing, Subdivisions, ZoomLevel, etc.)
-- | - **Grid.Snap**: Snap point operations
-- | - **Grid.Style**: Extended grid styles and vanishing points
-- | - **Grid.Generate**: Grid generation functions
-- | - **Grid.Perspective**: Perspective grid types
-- | - **Grid.Composition**: Composition grids (golden ratio, thirds, etc.)
-- | - **Grid.Math**: Trigonometry and geometry helpers
-- |
-- | ## Design Philosophy
-- |
-- | Grids for design canvases must be:
-- |
-- | 1. **Bounded** — Never infinitely small or large
-- | 2. **Snappable** — Every grid point can be a snap target
-- | 3. **Dynamic** — Adapt to zoom level
-- | 4. **Deterministic** — Same inputs = same grid, always
-- |
-- | ## Bounded Parameters
-- |
-- | - **GridSpacing**: 1 to 10000 canvas units
-- | - **Subdivisions**: 1 to 10
-- | - **ZoomLevel**: 0.1 to 10.0 (10% to 1000%)
-- | - **RadialDivisions**: 2 to 360

module Hydrogen.Element.Compound.Canvas.Grid
  ( -- * Re-exports from Types
    module Types
  
  -- * Re-exports from Snap
  , module Snap
  
  -- * Re-exports from Style
  , module Style
  
  -- * Re-exports from Generate
  , module Generate
  
  -- * Re-exports from Perspective
  , module Perspective
  
  -- * Re-exports from Composition
  , module Composition
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Element.Compound.Canvas.Grid.Types
  ( GridSpacing
  , gridSpacing
  , spacingValue
  , minSpacing
  , maxSpacing
  , defaultSpacing
  , doubleSpacing
  , halveSpacing
  , clampSpacing
  , Subdivisions
  , subdivisions
  , subdivisionsValue
  , minSubdivisions
  , maxSubdivisions
  , noSubdivisions
  , decimalSubdivisions
  , ZoomLevel
  , zoomLevel
  , visibleGridLevel
  , effectiveSpacing
  , shouldShowMajorLines
  , shouldShowMinorLines
  , shouldShowDots
  , GridLine
  , gridLine
  , lineStart
  , lineEnd
  , lineIsMajor
  , SnapPointType(..)
  , SnapPoint
  , snapPoint
  , snapPointPosition
  , snapPointType
  , GridGeometry
  , gridGeometry
  , geometryLines
  , geometrySnapPoints
  , geometryMajorLines
  , geometryMinorLines
  ) as Types

import Hydrogen.Element.Compound.Canvas.Grid.Snap
  ( nearestSnapPoint
  , snapPointsInBounds
  , snapToGrid
  ) as Snap

import Hydrogen.Element.Compound.Canvas.Grid.Style
  ( ExtendedGridStyle(..)
  , gridStyleAngle
  , isIsometricFamily
  , isPerspectiveFamily
  , isRadialFamily
  , VanishingPoint
  , vanishingPoint
  , vpPosition
  , vpHorizonY
  ) as Style

import Hydrogen.Element.Compound.Canvas.Grid.Generate
  ( generateSquareGrid
  , generateIsometricGrid
  , generatePolarGrid
  , generateHexGrid
  ) as Generate

import Hydrogen.Element.Compound.Canvas.Grid.Perspective
  ( PerspectiveGrid
  , perspectiveGrid1Point
  , perspectiveGrid2Point
  , perspectiveGrid3Point
  , perspectiveRays
  ) as Perspective

import Hydrogen.Element.Compound.Canvas.Grid.Composition
  ( goldenRatioGrid
  , ruleOfThirdsGrid
  , diagonalGrid
  ) as Composition
