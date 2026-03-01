-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // motion // path-operations
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | PathOperations — Illustrator/C4D-style path manipulation.
-- |
-- | ## Design Philosophy
-- |
-- | Professional motion graphics requires precise control over path shape:
-- |
-- | - **Add points**: Insert control points without changing curve shape
-- | - **Equalize spacing**: Make distance between points uniform
-- | - **Smooth/simplify**: Reduce points while maintaining shape
-- | - **Subdivide**: Add points for finer control
-- | - **Reverse**: Flip path direction
-- | - **Offset**: Create parallel paths
-- |
-- | These operations mirror tools in:
-- | - Adobe Illustrator (Smooth Tool, Simplify, Add Anchor Point)
-- | - Cinema 4D (Spline tools, Resample, Smooth)
-- | - After Effects (Path operations, Zig Zag)
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Motion.PathOperations as PO
-- |
-- | -- Equalize spacing (like C4D's Resample)
-- | uniform = PO.equalizeSpacing 50 path
-- |
-- | -- Smooth with iterations
-- | smoothed = PO.smooth 3 0.5 path
-- |
-- | -- Add point at parameter t
-- | withPoint = PO.insertPoint 0.5 path
-- | ```
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from submodules:
-- |
-- | - **Internal**: Helper functions, constants, geometry utilities
-- | - **Insertion**: Point insertion, subdivision operations
-- | - **Transform**: Spacing, smoothing, direction, offset operations
-- | - **Analysis**: Path analysis, filtering, utilities, display
-- |
-- | ## Dependencies
-- |
-- | - Schema.Geometry.Point (Point2D)
-- | - Schema.Geometry.Vector (Vector2D)

module Hydrogen.Schema.Motion.PathOperations
  ( module Insertion
  , module Transform
  , module Analysis
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Motion.PathOperations.Insertion as Insertion
import Hydrogen.Schema.Motion.PathOperations.Transform as Transform
import Hydrogen.Schema.Motion.PathOperations.Analysis as Analysis
