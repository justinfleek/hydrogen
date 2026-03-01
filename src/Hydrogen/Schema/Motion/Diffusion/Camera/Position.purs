-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                // hydrogen // schema // motion // diffusion // camera // position
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | 3D position type and operations for camera positioning.
-- |
-- | This module provides Position3D representing a point in 3D world space,
-- | along with operations for translation, scaling, distance calculation,
-- | interpolation, and bounds checking.

module Hydrogen.Schema.Motion.Diffusion.Camera.Position
  ( -- * Position 3D
    Position3D(Position3D)
  , mkPosition3D
  , originPosition3D
  , translatePosition3D
  , scalePosition3D
  , distanceSquared3D
  , distance3D
  , minPosition3D
  , maxPosition3D
  , lerpPosition3D
  , isInsideBounds3D
  , isOutsideBounds3D
  , arePositionsEqual
  , isCloserThan
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , compare
  , (==)
  , (/=)
  , (<=)
  , (>=)
  , (<)
  , (>)
  , (+)
  , (-)
  , (*)
  , (/)
  , (&&)
  , (||)
  , (<>)
  , otherwise
  , show
  , min
  , max
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // position // 3d
-- ═════════════════════════════════════════════════════════════════════════════

-- | 3D position in world space.
-- |
-- | Coordinates are in world units (typically meters).
newtype Position3D = Position3D
  { x :: Number
  , y :: Number
  , z :: Number
  }

derive instance eqPosition3D :: Eq Position3D

instance ordPosition3D :: Ord Position3D where
  compare (Position3D p1) (Position3D p2) =
    case compare p1.x p2.x of
      c | c /= eq' -> c
      _ -> case compare p1.y p2.y of
        c | c /= eq' -> c
        _ -> compare p1.z p2.z
    where
      eq' = compare 0 0  -- EQ

instance showPosition3D :: Show Position3D where
  show (Position3D p) = 
    "Pos3D(" <> show p.x <> ", " <> show p.y <> ", " <> show p.z <> ")"

-- | Create a 3D position.
mkPosition3D :: Number -> Number -> Number -> Position3D
mkPosition3D x y z = Position3D { x, y, z }

-- | Origin position (0, 0, 0).
originPosition3D :: Position3D
originPosition3D = Position3D { x: 0.0, y: 0.0, z: 0.0 }

-- | Translate a position by an offset.
translatePosition3D :: Number -> Number -> Number -> Position3D -> Position3D
translatePosition3D dx dy dz (Position3D p) =
  Position3D { x: p.x + dx, y: p.y + dy, z: p.z + dz }

-- | Scale a position by a factor.
scalePosition3D :: Number -> Position3D -> Position3D
scalePosition3D s (Position3D p) =
  Position3D { x: p.x * s, y: p.y * s, z: p.z * s }

-- | Calculate squared distance between two positions.
-- |
-- | More efficient than distance when only comparing distances.
distanceSquared3D :: Position3D -> Position3D -> Number
distanceSquared3D (Position3D p1) (Position3D p2) =
  let dx = p1.x - p2.x
      dy = p1.y - p2.y
      dz = p1.z - p2.z
  in dx * dx + dy * dy + dz * dz

-- | Calculate distance between two positions.
-- |
-- | Uses Newton-Raphson square root approximation (3 iterations).
distance3D :: Position3D -> Position3D -> Number
distance3D p1 p2 = sqrtApprox (distanceSquared3D p1 p2)
  where
    sqrtApprox :: Number -> Number
    sqrtApprox n
      | n <= 0.0 = 0.0
      | otherwise =
          let x0 = n / 2.0
              x1 = (x0 + n / x0) / 2.0
              x2 = (x1 + n / x1) / 2.0
              x3 = (x2 + n / x2) / 2.0
          in x3

-- | Component-wise minimum of two positions.
minPosition3D :: Position3D -> Position3D -> Position3D
minPosition3D (Position3D p1) (Position3D p2) =
  Position3D { x: min p1.x p2.x, y: min p1.y p2.y, z: min p1.z p2.z }

-- | Component-wise maximum of two positions.
maxPosition3D :: Position3D -> Position3D -> Position3D
maxPosition3D (Position3D p1) (Position3D p2) =
  Position3D { x: max p1.x p2.x, y: max p1.y p2.y, z: max p1.z p2.z }

-- | Linear interpolation between two positions.
-- |
-- | When t=0, returns p1. When t=1, returns p2.
lerpPosition3D :: Position3D -> Position3D -> Number -> Position3D
lerpPosition3D (Position3D p1) (Position3D p2) t =
  let oneMinusT = 1.0 - t
  in Position3D
    { x: p1.x * oneMinusT + p2.x * t
    , y: p1.y * oneMinusT + p2.y * t
    , z: p1.z * oneMinusT + p2.z * t
    }

-- | Check if a position is inside an axis-aligned bounding box.
-- |
-- | The bounds are specified by min and max corners (inclusive).
isInsideBounds3D :: Position3D -> Position3D -> Position3D -> Boolean
isInsideBounds3D (Position3D minBound) (Position3D maxBound) (Position3D p) =
  p.x >= minBound.x && p.x <= maxBound.x &&
  p.y >= minBound.y && p.y <= maxBound.y &&
  p.z >= minBound.z && p.z <= maxBound.z

-- | Check if a position is outside an axis-aligned bounding box.
-- |
-- | Returns true if any coordinate is outside the bounds.
isOutsideBounds3D :: Position3D -> Position3D -> Position3D -> Boolean
isOutsideBounds3D (Position3D minBound) (Position3D maxBound) (Position3D p) =
  p.x < minBound.x || p.x > maxBound.x ||
  p.y < minBound.y || p.y > maxBound.y ||
  p.z < minBound.z || p.z > maxBound.z

-- | Check if two positions are equal (component-wise).
arePositionsEqual :: Position3D -> Position3D -> Boolean
arePositionsEqual (Position3D p1) (Position3D p2) =
  p1.x == p2.x && p1.y == p2.y && p1.z == p2.z

-- | Check if position p is closer to target than reference position.
-- |
-- | Compares squared distances for efficiency.
isCloserThan :: Position3D -> Position3D -> Position3D -> Boolean
isCloserThan target p reference =
  distanceSquared3D target p < distanceSquared3D target reference
