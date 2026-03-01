-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // geometry // shape
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Shape — Foundational geometric primitives for vector graphics.
-- |
-- | ## Design Philosophy
-- |
-- | Shapes are pure data descriptions of geometry. They compose algebraically
-- | via boolean operations and path combinations. This is the vocabulary for
-- | "Illustrator on steroids" — everything from simple rectangles to complex
-- | compound paths with boolean operations.
-- |
-- | ## Shape Categories
-- |
-- | **Primitives**: Rectangle, Circle, Ellipse, Line, Polygon, Polyline
-- | **Curves**: Bezier (cubic/quadratic), Arc, Spline, NURBS
-- | **Complex**: Star, Ring, Spiral, Arrow, Cross, Heart, Gear
-- | **Paths**: Open paths, Closed paths, Compound paths
-- | **Operations**: Union, Subtract, Intersect, Exclude, Divide
-- | **3D Extrusion**: Extrude, Revolve, Sweep, Loft
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from submodules:
-- | - `Shape.Types` — Core type definitions (PixelPoint, AnchorPoint, PathCommand)
-- | - `Shape.Primitives` — Basic shapes (Rectangle, Ellipse, Polygon, etc.)
-- | - `Shape.Path` — Generic path shapes from commands
-- | - `Shape.Operations` — Boolean and 3D operations
-- | - `Shape.Compound` — Compound shapes and the unified Shape type
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show, Bounded)
-- | - Schema.Dimension.Device (Pixel for measurements)
-- | - Schema.Geometry.Radius (corner treatments)

module Hydrogen.Schema.Geometry.Shape
  ( module Types
  , module Primitives
  , module Path
  , module Operations
  , module Compound
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Geometry.Shape.Types as Types
import Hydrogen.Schema.Geometry.Shape.Primitives as Primitives
import Hydrogen.Schema.Geometry.Shape.Path as Path
import Hydrogen.Schema.Geometry.Shape.Operations as Operations
import Hydrogen.Schema.Geometry.Shape.Compound as Compound
