-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--            // hydrogen // element // compound // canvas // grid // composition
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Composition Grids — Classical composition guides.
-- |
-- | ## Grid Types
-- |
-- | - **Golden Ratio**: φ (1.618...) based divisions
-- | - **Rule of Thirds**: 3×3 grid for photography
-- | - **Diagonal**: Diagonal guidelines for dynamic composition
-- |
-- | ## Dependencies
-- |
-- | - Grid.Types (GridLine, GridGeometry, SnapPoint)
-- | - Grid.Math (phi constant)

module Hydrogen.Element.Compound.Canvas.Grid.Composition
  ( -- * Composition Grids
    goldenRatioGrid
  , ruleOfThirdsGrid
  , diagonalGrid
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (-)
  , (*)
  , (/)
  )

import Hydrogen.Element.Compound.Canvas.Grid.Types
  ( GridLine
  , gridLine
  , GridGeometry
  , gridGeometry
  , SnapPoint
  , snapPoint
  , SnapPointType(SnapCompositionPoint)
  )

import Hydrogen.Element.Compound.Canvas.Grid.Math (phi)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // composition grids
-- ═════════════════════════════════════════════════════════════════════════════

-- | Golden ratio (φ = 1.618...) grid.
-- |
-- | Creates vertical and horizontal lines at φ divisions,
-- | with snap points at all four intersections.
goldenRatioGrid :: { width :: Number, height :: Number } -> GridGeometry
goldenRatioGrid size =
  let 
    -- Vertical divisions at 1/φ and (φ-1)/φ
    v1 = size.width / phi
    v2 = size.width - v1
    
    -- Horizontal divisions at 1/φ and (φ-1)/φ
    h1 = size.height / phi
    h2 = size.height - h1
    
    lines :: Array GridLine
    lines = 
      [ gridLine v1 0.0 v1 size.height true
      , gridLine v2 0.0 v2 size.height true
      , gridLine 0.0 h1 size.width h1 true
      , gridLine 0.0 h2 size.width h2 true
      ]
    
    -- Intersection points (power points)
    points :: Array SnapPoint
    points = 
      [ snapPoint v1 h1 SnapCompositionPoint
      , snapPoint v1 h2 SnapCompositionPoint
      , snapPoint v2 h1 SnapCompositionPoint
      , snapPoint v2 h2 SnapCompositionPoint
      ]
    
  in gridGeometry lines points

-- | Rule of thirds grid.
-- |
-- | Creates a 3×3 grid with snap points at the four
-- | "power points" where lines intersect.
ruleOfThirdsGrid :: { width :: Number, height :: Number } -> GridGeometry
ruleOfThirdsGrid size =
  let 
    third = 1.0 / 3.0
    twoThirds = 2.0 / 3.0
    
    v1 = size.width * third
    v2 = size.width * twoThirds
    h1 = size.height * third
    h2 = size.height * twoThirds
    
    lines :: Array GridLine
    lines = 
      [ gridLine v1 0.0 v1 size.height true
      , gridLine v2 0.0 v2 size.height true
      , gridLine 0.0 h1 size.width h1 true
      , gridLine 0.0 h2 size.width h2 true
      ]
    
    -- Power points (intersections)
    points :: Array SnapPoint
    points = 
      [ snapPoint v1 h1 SnapCompositionPoint
      , snapPoint v1 h2 SnapCompositionPoint
      , snapPoint v2 h1 SnapCompositionPoint
      , snapPoint v2 h2 SnapCompositionPoint
      ]
    
  in gridGeometry lines points

-- | Diagonal guidelines.
-- |
-- | Creates diagonal lines from corners with a snap point
-- | at the center where they intersect.
diagonalGrid :: { width :: Number, height :: Number } -> GridGeometry
diagonalGrid size =
  let 
    lines :: Array GridLine
    lines = 
      [ gridLine 0.0 0.0 size.width size.height true          -- Top-left to bottom-right
      , gridLine size.width 0.0 0.0 size.height true          -- Top-right to bottom-left
      ]
    
    -- Center point
    centerX = size.width / 2.0
    centerY = size.height / 2.0
    
    points :: Array SnapPoint
    points = [snapPoint centerX centerY SnapCompositionPoint]
    
  in gridGeometry lines points
