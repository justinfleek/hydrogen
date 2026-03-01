-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // physics // collision // point
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Point — 2D point primitives for collision geometry.
-- |
-- | ## Design Philosophy
-- |
-- | Local Point2D definition to avoid circular dependencies with Geometry.Point.
-- | Provides essential point operations needed for collision detection.
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)
-- | - Data.Number (sqrt)
-- |
-- | ## Dependents
-- |
-- | - Collision.Volumes (bounding volume centers)
-- | - Collision.Contact (contact points and normals)
-- | - Collision.Detection (collision algorithms)

module Hydrogen.Schema.Physics.Collision.Point
  ( -- * Point2D Type
    Point2D(..)
  
  -- * Construction
  , point2D
  , origin2D
  
  -- * Operations
  , distance
  , distanceSquared
  , midpoint
  , offsetPoint
  , normalizePoint
  , negatePoint
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , negate
  , (*)
  , (+)
  , (-)
  , (/)
  , (<)
  , (<>)
  )

import Data.Number (sqrt)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // point 2d
-- ═════════════════════════════════════════════════════════════════════════════

-- | 2D point for collision geometry.
-- |
-- | Local definition to avoid circular dependencies with Geometry.Point.
newtype Point2D = Point2D { x :: Number, y :: Number }

derive instance eqPoint2D :: Eq Point2D
derive instance ordPoint2D :: Ord Point2D

instance showPoint2D :: Show Point2D where
  show (Point2D p) = "Point2D(" <> show p.x <> ", " <> show p.y <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a 2D point
point2D :: Number -> Number -> Point2D
point2D x y = Point2D { x, y }

-- | Origin point (0, 0)
origin2D :: Point2D
origin2D = Point2D { x: 0.0, y: 0.0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Distance between two points
distance :: Point2D -> Point2D -> Number
distance (Point2D a) (Point2D b) = 
  let dx = b.x - a.x
      dy = b.y - a.y
  in sqrt (dx * dx + dy * dy)

-- | Squared distance (faster, avoids sqrt)
distanceSquared :: Point2D -> Point2D -> Number
distanceSquared (Point2D a) (Point2D b) = 
  let dx = b.x - a.x
      dy = b.y - a.y
  in dx * dx + dy * dy

-- | Midpoint between two points
midpoint :: Point2D -> Point2D -> Point2D
midpoint (Point2D a) (Point2D b) = Point2D
  { x: (a.x + b.x) / 2.0
  , y: (a.y + b.y) / 2.0
  }

-- | Add a vector (offset) to a point
offsetPoint :: Point2D -> Number -> Number -> Point2D
offsetPoint (Point2D p) dx dy = Point2D { x: p.x + dx, y: p.y + dy }

-- | Normalize a point (make unit length)
normalizePoint :: Point2D -> Point2D
normalizePoint (Point2D p) =
  let len = sqrt (p.x * p.x + p.y * p.y)
  in if len < 0.0001
     then Point2D { x: 1.0, y: 0.0 }  -- Default to right
     else Point2D { x: p.x / len, y: p.y / len }

-- | Negate a point
negatePoint :: Point2D -> Point2D
negatePoint (Point2D p) = Point2D { x: negate p.x, y: negate p.y }
