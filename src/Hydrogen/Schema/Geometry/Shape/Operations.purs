-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // geometry // shape // operations
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Operations — Boolean and 3D shape operations.
-- |
-- | This module contains:
-- | - Boolean operations (Union, Subtract, Intersect, Exclude, Divide)
-- | - 3D extrusion operations (Extrude, Revolve, Sweep)
-- | - Compound shapes from boolean combinations
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)
-- | - Schema.Dimension.Device (Pixel)
-- | - Shape.Path (PathShape for sweep operations)

module Hydrogen.Schema.Geometry.Shape.Operations
  ( -- * Boolean Operations
    BooleanOp(..)
  
  -- * 3D Operations
  , ExtrudeOp
  , extrudeOp
  , RevolveOp
  , revolveOp
  , SweepOp
  , sweepOp
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  )

import Hydrogen.Schema.Dimension.Device (Pixel)
import Hydrogen.Schema.Geometry.Shape.Path (PathShape)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // boolean operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Boolean operations for combining shapes
data BooleanOp
  = BoolUnion           -- ^ Combine shapes (OR)
  | BoolSubtract        -- ^ Remove second from first
  | BoolIntersect       -- ^ Keep only overlap (AND)
  | BoolExclude         -- ^ Keep non-overlapping parts (XOR)
  | BoolDivide          -- ^ Split into separate pieces

derive instance eqBooleanOp :: Eq BooleanOp
derive instance ordBooleanOp :: Ord BooleanOp

instance showBooleanOp :: Show BooleanOp where
  show BoolUnion = "(BooleanOp Union)"
  show BoolSubtract = "(BooleanOp Subtract)"
  show BoolIntersect = "(BooleanOp Intersect)"
  show BoolExclude = "(BooleanOp Exclude)"
  show BoolDivide = "(BooleanOp Divide)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // 3d operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extrude operation - extend 2D shape into 3D along Z axis
type ExtrudeOp =
  { depth :: Pixel          -- ^ Extrusion depth
  , bevel :: Pixel          -- ^ Bevel amount at edges
  , bevelSegments :: Int    -- ^ Smoothness of bevel
  }

-- | Create an extrude operation
extrudeOp :: Pixel -> Pixel -> Int -> ExtrudeOp
extrudeOp depth bevel bevelSegments =
  { depth, bevel, bevelSegments }

-- | Revolve operation - rotate 2D shape around axis to create 3D
type RevolveOp =
  { angle :: Number         -- ^ Rotation angle in degrees (360 = full revolution)
  , segments :: Int         -- ^ Number of segments for smoothness
  , axisOffset :: Pixel     -- ^ Distance of axis from shape
  }

-- | Create a revolve operation
revolveOp :: Number -> Int -> Pixel -> RevolveOp
revolveOp angle segments axisOffset =
  { angle, segments, axisOffset }

-- | Sweep operation - extrude shape along a path
type SweepOp =
  { path :: PathShape       -- ^ Path to sweep along
  , twist :: Number         -- ^ Rotation along path in degrees
  , scale :: Number         -- ^ Scale factor at end (1.0 = no change)
  }

-- | Create a sweep operation
sweepOp :: PathShape -> Number -> Number -> SweepOp
sweepOp path twist scale =
  { path, twist, scale }
