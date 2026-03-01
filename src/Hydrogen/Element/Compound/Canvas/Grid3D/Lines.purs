-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                             // hydrogen // grid3d // lines
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | 3D grid line primitives.
-- |
-- | ## Design
-- |
-- | GridLine3D represents a line segment in 3D space with metadata:
-- | - Start and end points
-- | - Major/minor classification
-- | - Axis alignment (if any)

module Hydrogen.Element.Compound.Canvas.Grid3D.Lines
  ( -- * Line Type
    GridLine3D
  , gridLine3D
  
  -- * Accessors
  , line3DStart
  , line3DEnd
  , line3DIsMajor
  , line3DAxis
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Data.Maybe (Maybe)

import Hydrogen.Element.Compound.Canvas.Grid3D.Types (Axis)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // 3d grid lines
-- ═════════════════════════════════════════════════════════════════════════════

-- | A line in 3D space.
newtype GridLine3D = GridLine3D
  { x1 :: Number, y1 :: Number, z1 :: Number
  , x2 :: Number, y2 :: Number, z2 :: Number
  , isMajor :: Boolean
  , axis :: Maybe Axis  -- Which axis this line is parallel to
  }

derive instance eqGridLine3D :: Eq GridLine3D

instance showGridLine3D :: Show GridLine3D where
  show (GridLine3D l) =
    "Line3D(" <> show l.x1 <> "," <> show l.y1 <> "," <> show l.z1 <> "->" <>
    show l.x2 <> "," <> show l.y2 <> "," <> show l.z2 <> ")"

-- | Create a 3D grid line.
gridLine3D :: Number -> Number -> Number 
           -> Number -> Number -> Number 
           -> Boolean -> Maybe Axis -> GridLine3D
gridLine3D x1 y1 z1 x2 y2 z2 isMajor axis = 
  GridLine3D { x1, y1, z1, x2, y2, z2, isMajor, axis }

-- | Get line start point.
line3DStart :: GridLine3D -> { x :: Number, y :: Number, z :: Number }
line3DStart (GridLine3D l) = { x: l.x1, y: l.y1, z: l.z1 }

-- | Get line end point.
line3DEnd :: GridLine3D -> { x :: Number, y :: Number, z :: Number }
line3DEnd (GridLine3D l) = { x: l.x2, y: l.y2, z: l.z2 }

-- | Check if line is major.
line3DIsMajor :: GridLine3D -> Boolean
line3DIsMajor (GridLine3D l) = l.isMajor

-- | Get axis this line is parallel to.
line3DAxis :: GridLine3D -> Maybe Axis
line3DAxis (GridLine3D l) = l.axis
