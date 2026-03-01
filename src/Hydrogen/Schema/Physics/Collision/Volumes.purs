-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                      // hydrogen // schema // physics // collision // volumes
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Volumes — Bounding volume primitives for collision detection.
-- |
-- | ## Design Philosophy
-- |
-- | Bounding volumes are the first line of defense in collision detection.
-- | Broad-phase collision uses simple volume tests to quickly eliminate
-- | pairs that cannot possibly collide.
-- |
-- | ## Volume Types
-- |
-- | - **AABB**: Axis-Aligned Bounding Box — fastest, axis-aligned only
-- | - **BoundingCircle**: Rotationally invariant — good for spinning objects
-- | - **BoundingCapsule**: Stadium shape — good for elongated objects
-- | - **OBB**: Oriented Bounding Box — tighter fit, rotation aware
-- |
-- | ## Dependencies
-- |
-- | - Collision.Point (Point2D)
-- | - Collision.Internal (clampPositive, clampUnit)
-- | - Data.Number (sqrt, cos, sin)

module Hydrogen.Schema.Physics.Collision.Volumes
  ( -- * AABB
    AABB(..)
  , aabb
  , aabbFromPoints
  , aabbCenter
  , aabbSize
  , aabbHalfSize
  , aabbContains
  , aabbExpand
  , aabbMerge
  
  -- * Bounding Circle
  , BoundingCircle(..)
  , boundingCircle
  , circleContains
  , circleExpand
  , circleMerge
  
  -- * Bounding Capsule
  , BoundingCapsule(..)
  , boundingCapsule
  , capsuleContains
  , pointToSegmentDistance
  
  -- * Oriented Bounding Box
  , OBB(..)
  , obb
  , obbCorners
  , obbContains
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
  , (&&)
  , (*)
  , (+)
  , (-)
  , (/)
  , (<)
  , (<=)
  , (<>)
  , (>=)
  )

import Data.Number (sqrt, cos, sin)

import Hydrogen.Schema.Physics.Collision.Point
  ( Point2D(..)
  , point2D
  , distance
  , distanceSquared
  )

import Hydrogen.Schema.Physics.Collision.Internal
  ( minNum
  , maxNum
  , absNum
  , clampPositive
  , clampUnit
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // aabb
-- ═════════════════════════════════════════════════════════════════════════════

-- | Axis-Aligned Bounding Box.
-- |
-- | The simplest and fastest collision primitive. Defined by min/max corners.
-- | "Axis-aligned" means edges are parallel to coordinate axes — no rotation.
newtype AABB = AABB
  { minX :: Number
  , minY :: Number
  , maxX :: Number
  , maxY :: Number
  }

derive instance eqAABB :: Eq AABB
derive instance ordAABB :: Ord AABB

instance showAABB :: Show AABB where
  show (AABB b) = "AABB(" <> show b.minX <> "," <> show b.minY 
               <> " -> " <> show b.maxX <> "," <> show b.maxY <> ")"

-- | Create an AABB from min/max coordinates.
-- | Automatically normalizes so min <= max.
aabb :: Number -> Number -> Number -> Number -> AABB
aabb x1 y1 x2 y2 = AABB
  { minX: minNum x1 x2
  , minY: minNum y1 y2
  , maxX: maxNum x1 x2
  , maxY: maxNum y1 y2
  }

-- | Create AABB from two corner points
aabbFromPoints :: Point2D -> Point2D -> AABB
aabbFromPoints (Point2D a) (Point2D b) = aabb a.x a.y b.x b.y

-- | Get AABB center point
aabbCenter :: AABB -> Point2D
aabbCenter (AABB b) = Point2D
  { x: (b.minX + b.maxX) / 2.0
  , y: (b.minY + b.maxY) / 2.0
  }

-- | Get AABB size (width, height)
aabbSize :: AABB -> { width :: Number, height :: Number }
aabbSize (AABB b) = 
  { width: b.maxX - b.minX
  , height: b.maxY - b.minY
  }

-- | Get AABB half-size (useful for collision math)
aabbHalfSize :: AABB -> { hx :: Number, hy :: Number }
aabbHalfSize (AABB b) =
  { hx: (b.maxX - b.minX) / 2.0
  , hy: (b.maxY - b.minY) / 2.0
  }

-- | Check if point is inside AABB
aabbContains :: AABB -> Point2D -> Boolean
aabbContains (AABB b) (Point2D p) =
  p.x >= b.minX && p.x <= b.maxX &&
  p.y >= b.minY && p.y <= b.maxY

-- | Expand AABB by a margin on all sides
aabbExpand :: Number -> AABB -> AABB
aabbExpand margin (AABB b) = AABB
  { minX: b.minX - margin
  , minY: b.minY - margin
  , maxX: b.maxX + margin
  , maxY: b.maxY + margin
  }

-- | Merge two AABBs into one that contains both
aabbMerge :: AABB -> AABB -> AABB
aabbMerge (AABB a) (AABB b) = AABB
  { minX: minNum a.minX b.minX
  , minY: minNum a.minY b.minY
  , maxX: maxNum a.maxX b.maxX
  , maxY: maxNum a.maxY b.maxY
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // bounding circle
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounding Circle (Bounding Sphere in 2D).
-- |
-- | Rotationally invariant — rotation doesn't change the bounds.
-- | Simpler math than AABB for moving objects.
newtype BoundingCircle = BoundingCircle
  { center :: Point2D
  , radius :: Number    -- ^ Always non-negative (clamped)
  }

derive instance eqBoundingCircle :: Eq BoundingCircle
derive instance ordBoundingCircle :: Ord BoundingCircle

instance showBoundingCircle :: Show BoundingCircle where
  show (BoundingCircle c) = "BoundingCircle(r=" <> show c.radius <> ")"

-- | Create a bounding circle
boundingCircle :: Point2D -> Number -> BoundingCircle
boundingCircle center radius = BoundingCircle
  { center
  , radius: clampPositive 100000.0 radius
  }

-- | Check if point is inside circle
circleContains :: BoundingCircle -> Point2D -> Boolean
circleContains (BoundingCircle c) p =
  distanceSquared c.center p <= c.radius * c.radius

-- | Expand circle radius
circleExpand :: Number -> BoundingCircle -> BoundingCircle
circleExpand delta (BoundingCircle c) = BoundingCircle
  { center: c.center
  , radius: clampPositive 100000.0 (c.radius + delta)
  }

-- | Merge two circles into one containing both
circleMerge :: BoundingCircle -> BoundingCircle -> BoundingCircle
circleMerge (BoundingCircle a) (BoundingCircle b) =
  let 
    d = distance a.center b.center
    -- If one contains the other, return the larger
    newRadius = (d + a.radius + b.radius) / 2.0
    -- Center is on line between centers, weighted by radii
    t = if d < 0.0001 then 0.5 else (newRadius - a.radius) / d
    Point2D ac = a.center
    Point2D bc = b.center
    newCenter = Point2D
      { x: ac.x + t * (bc.x - ac.x)
      , y: ac.y + t * (bc.y - ac.y)
      }
  in BoundingCircle { center: newCenter, radius: clampPositive 100000.0 newRadius }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // bounding capsule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounding Capsule (Stadium shape).
-- |
-- | Two circles connected by a rectangle. Good for elongated moving objects
-- | (characters, bullets, etc.). Also called "swept sphere" or "stadium".
newtype BoundingCapsule = BoundingCapsule
  { pointA :: Point2D   -- ^ First endpoint
  , pointB :: Point2D   -- ^ Second endpoint
  , radius :: Number    -- ^ Capsule radius (thickness)
  }

derive instance eqBoundingCapsule :: Eq BoundingCapsule
derive instance ordBoundingCapsule :: Ord BoundingCapsule

instance showBoundingCapsule :: Show BoundingCapsule where
  show (BoundingCapsule c) = "BoundingCapsule(r=" <> show c.radius <> ")"

-- | Create a bounding capsule
boundingCapsule :: Point2D -> Point2D -> Number -> BoundingCapsule
boundingCapsule pointA pointB radius = BoundingCapsule
  { pointA
  , pointB
  , radius: clampPositive 100000.0 radius
  }

-- | Check if point is inside capsule
capsuleContains :: BoundingCapsule -> Point2D -> Boolean
capsuleContains (BoundingCapsule c) p =
  let dist = pointToSegmentDistance p c.pointA c.pointB
  in dist <= c.radius

-- | Distance from point to line segment.
-- |
-- | Calculates shortest distance from a point to a line segment defined
-- | by two endpoints. Used for capsule collision detection.
pointToSegmentDistance :: Point2D -> Point2D -> Point2D -> Number
pointToSegmentDistance (Point2D p) (Point2D a) (Point2D b) =
  let
    -- Vector from A to B
    abx = b.x - a.x
    aby = b.y - a.y
    -- Vector from A to P
    apx = p.x - a.x
    apy = p.y - a.y
    -- Project P onto line AB, get parameter t
    abSquared = abx * abx + aby * aby
    t = if abSquared < 0.0001 
        then 0.0 
        else clampUnit 1.0 ((apx * abx + apy * aby) / abSquared)
    -- Closest point on segment
    closestX = a.x + t * abx
    closestY = a.y + t * aby
    -- Distance to closest point
    dx = p.x - closestX
    dy = p.y - closestY
  in sqrt (dx * dx + dy * dy)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                        // obb
-- ═════════════════════════════════════════════════════════════════════════════

-- | Oriented Bounding Box.
-- |
-- | Like AABB but can be rotated. More expensive to test but tighter fit
-- | for rotated objects.
newtype OBB = OBB
  { center :: Point2D   -- ^ Center point
  , halfWidth :: Number -- ^ Half-width along local X axis
  , halfHeight :: Number -- ^ Half-height along local Y axis
  , rotation :: Number  -- ^ Rotation angle in radians
  }

derive instance eqOBB :: Eq OBB
derive instance ordOBB :: Ord OBB

instance showOBB :: Show OBB where
  show (OBB o) = "OBB(" <> show o.halfWidth <> "x" <> show o.halfHeight 
             <> " @" <> show o.rotation <> ")"

-- | Create an oriented bounding box
obb :: Point2D -> Number -> Number -> Number -> OBB
obb center halfWidth halfHeight rotation = OBB
  { center
  , halfWidth: clampPositive 100000.0 halfWidth
  , halfHeight: clampPositive 100000.0 halfHeight
  , rotation
  }

-- | Get the four corners of the OBB
obbCorners :: OBB -> { tl :: Point2D, tr :: Point2D, bl :: Point2D, br :: Point2D }
obbCorners (OBB o) =
  let
    Point2D c = o.center
    cosR = cos o.rotation
    sinR = sin o.rotation
    -- Local corners before rotation
    hw = o.halfWidth
    hh = o.halfHeight
    -- Rotate each corner
    rotatePoint lx ly = Point2D
      { x: c.x + lx * cosR - ly * sinR
      , y: c.y + lx * sinR + ly * cosR
      }
  in
    { tl: rotatePoint (negate hw) (negate hh)
    , tr: rotatePoint hw (negate hh)
    , bl: rotatePoint (negate hw) hh
    , br: rotatePoint hw hh
    }

-- | Check if point is inside OBB
obbContains :: OBB -> Point2D -> Boolean
obbContains (OBB o) (Point2D p) =
  let
    Point2D c = o.center
    -- Transform point to OBB local space
    dx = p.x - c.x
    dy = p.y - c.y
    cosR = cos (negate o.rotation)
    sinR = sin (negate o.rotation)
    localX = dx * cosR - dy * sinR
    localY = dx * sinR + dy * cosR
  in absNum localX <= o.halfWidth && absNum localY <= o.halfHeight
