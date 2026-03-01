-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // geometry // shape // compound
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Compound — Compound shapes from boolean operations and the unified Shape type.
-- |
-- | This module contains:
-- | - CompoundShape for boolean combinations
-- | - The unified Shape wrapper type that holds any shape variant
-- | - Helper functions for creating compound shapes
-- |
-- | ## Note on Mutual Recursion
-- |
-- | Shape and CompoundShape are mutually recursive: CompoundShape contains
-- | an array of Shape, and Shape has a ShapeCompound constructor. This is
-- | intentional and allows for arbitrary nesting of boolean operations.
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Show)
-- | - Shape.Types (core types)
-- | - Shape.Primitives (primitive shape types)
-- | - Shape.Path (PathShape)
-- | - Shape.Operations (BooleanOp)

module Hydrogen.Schema.Geometry.Shape.Compound
  ( -- * Compound Shape
    CompoundShape
  , compoundShape
  , unionShapes
  , subtractShapes
  , intersectShapes
  , excludeShapes
  
  -- * Unified Shape Type
  , Shape(..)
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  )

import Hydrogen.Schema.Geometry.Shape.Operations
  ( BooleanOp
      ( BoolUnion
      , BoolSubtract
      , BoolIntersect
      , BoolExclude
      )
  )
import Hydrogen.Schema.Geometry.Shape.Path (PathShape)
import Hydrogen.Schema.Geometry.Shape.Primitives
  ( RectangleShape
  , EllipseShape
  , LineShape
  , PolygonShape
  , StarShape
  , RingShape
  , SpiralShape
  , ArrowShape
  , CrossShape
  , GearShape
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // shape wrapper
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unified shape type that can hold any shape primitive
data Shape
  = ShapeRectangle RectangleShape
  | ShapeEllipse EllipseShape
  | ShapeLine LineShape
  | ShapePolygon PolygonShape
  | ShapeStar StarShape
  | ShapeRing RingShape
  | ShapeSpiral SpiralShape
  | ShapeArrow ArrowShape
  | ShapeCross CrossShape
  | ShapeGear GearShape
  | ShapePath PathShape
  | ShapeCompound CompoundShape

derive instance eqShape :: Eq Shape

instance showShape :: Show Shape where
  show (ShapeRectangle _) = "(Shape Rectangle)"
  show (ShapeEllipse _) = "(Shape Ellipse)"
  show (ShapeLine _) = "(Shape Line)"
  show (ShapePolygon _) = "(Shape Polygon)"
  show (ShapeStar _) = "(Shape Star)"
  show (ShapeRing _) = "(Shape Ring)"
  show (ShapeSpiral _) = "(Shape Spiral)"
  show (ShapeArrow _) = "(Shape Arrow)"
  show (ShapeCross _) = "(Shape Cross)"
  show (ShapeGear _) = "(Shape Gear)"
  show (ShapePath _) = "(Shape Path)"
  show (ShapeCompound _) = "(Shape Compound)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // compound shape
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compound shape from boolean operations
type CompoundShape =
  { operation :: BooleanOp
  , shapes :: Array Shape
  }

-- | Create a compound shape from boolean operation
compoundShape :: BooleanOp -> Array Shape -> CompoundShape
compoundShape operation shapes = { operation, shapes }

-- | Union multiple shapes
unionShapes :: Array Shape -> CompoundShape
unionShapes = compoundShape BoolUnion

-- | Subtract shapes from first shape
subtractShapes :: Array Shape -> CompoundShape
subtractShapes = compoundShape BoolSubtract

-- | Intersect shapes
intersectShapes :: Array Shape -> CompoundShape
intersectShapes = compoundShape BoolIntersect

-- | Exclude overlapping regions
excludeShapes :: Array Shape -> CompoundShape
excludeShapes = compoundShape BoolExclude
