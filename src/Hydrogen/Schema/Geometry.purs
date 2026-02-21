-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // schema // geometry
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Geometry pillar - shapes, paths, and spatial primitives.
-- |
-- | Covers:
-- | - **Radius**: Border radius and corner definitions
-- | - **Shape**: Primitive shapes (rectangle, circle, polygon)
-- | - **Path**: Bezier paths and curves
-- | - **Transform**: 2D/3D transforms (translate, rotate, scale, skew)
-- |
-- | ## Usage
-- |
-- | Always use qualified imports to avoid naming conflicts:
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Geometry as Geometry
-- |
-- | cardRadius :: Geometry.Corners
-- | cardRadius = Geometry.cornersAll Geometry.md
-- | ```
-- |
-- | Re-exports all Geometry submodules.

module Hydrogen.Schema.Geometry
  ( module Hydrogen.Schema.Geometry.Radius
  ) where

import Hydrogen.Schema.Geometry.Radius
