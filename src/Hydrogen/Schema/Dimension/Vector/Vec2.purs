-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // dimension // vector // 2d
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | 2D vector type parameterized by component type.

module Hydrogen.Schema.Dimension.Vector.Vec2
  ( Vec2(Vec2)
  , vec2
  , vec2Zero
  , vec2One
  , vec2UnitX
  , vec2UnitY
  , addVec2
  , subtractVec2
  , scaleVec2
  , negateVec2
  , dotVec2
  , lengthSquaredVec2
  , lengthVec2
  , normalizeVec2
  , distanceVec2
  , lerpVec2
  , perpendicularVec2
  , angleVec2
  , getX2
  , getY2
  , setX2
  , setY2
  ) where

import Prelude
  ( class Eq
  , class Functor
  , class Ring
  , class Semiring
  , class Show
  , negate
  , one
  , show
  , zero
  , (+)
  , (-)
  , (*)
  , (/)
  , (==)
  , (<>)
  )

import Hydrogen.Math.Core as Math

-- | 2D vector parameterized by component type
data Vec2 a = Vec2 a a

derive instance eqVec2 :: Eq a => Eq (Vec2 a)

instance showVec2 :: Show a => Show (Vec2 a) where
  show (Vec2 x y) = "Vec2(" <> show x <> ", " <> show y <> ")"

instance functorVec2 :: Functor Vec2 where
  map f (Vec2 x y) = Vec2 (f x) (f y)

-- | Create a 2D vector
vec2 :: forall a. a -> a -> Vec2 a
vec2 = Vec2

-- | Zero vector
vec2Zero :: forall a. Semiring a => Vec2 a
vec2Zero = Vec2 zero zero

-- | Unit vector (1,1)
vec2One :: forall a. Semiring a => Vec2 a
vec2One = Vec2 one one

-- | Unit vector along X axis
vec2UnitX :: forall a. Semiring a => Vec2 a
vec2UnitX = Vec2 one zero

-- | Unit vector along Y axis
vec2UnitY :: forall a. Semiring a => Vec2 a
vec2UnitY = Vec2 zero one

-- | Add two 2D vectors
addVec2 :: forall a. Semiring a => Vec2 a -> Vec2 a -> Vec2 a
addVec2 (Vec2 x1 y1) (Vec2 x2 y2) = Vec2 (x1 + x2) (y1 + y2)

-- | Subtract two 2D vectors
subtractVec2 :: forall a. Ring a => Vec2 a -> Vec2 a -> Vec2 a
subtractVec2 (Vec2 x1 y1) (Vec2 x2 y2) = Vec2 (x1 - x2) (y1 - y2)

-- | Scale a 2D vector by a scalar
scaleVec2 :: forall a. Semiring a => a -> Vec2 a -> Vec2 a
scaleVec2 s (Vec2 x y) = Vec2 (s * x) (s * y)

-- | Negate a 2D vector
negateVec2 :: forall a. Ring a => Vec2 a -> Vec2 a
negateVec2 (Vec2 x y) = Vec2 (negate x) (negate y)

-- | Dot product of two 2D vectors
dotVec2 :: forall a. Semiring a => Vec2 a -> Vec2 a -> a
dotVec2 (Vec2 x1 y1) (Vec2 x2 y2) = x1 * x2 + y1 * y2

-- | Squared length of a 2D Number vector
lengthSquaredVec2 :: Vec2 Number -> Number
lengthSquaredVec2 v = dotVec2 v v

-- | Length of a 2D Number vector
lengthVec2 :: Vec2 Number -> Number
lengthVec2 v = Math.sqrt (lengthSquaredVec2 v)

-- | Normalize a 2D Number vector to unit length
normalizeVec2 :: Vec2 Number -> Vec2 Number
normalizeVec2 v =
  let len = lengthVec2 v
  in if len == 0.0 then v else scaleVec2 (1.0 / len) v

-- | Distance between two 2D points
distanceVec2 :: Vec2 Number -> Vec2 Number -> Number
distanceVec2 a b = lengthVec2 (subtractVec2 b a)

-- | Linear interpolation between two 2D vectors
lerpVec2 :: Number -> Vec2 Number -> Vec2 Number -> Vec2 Number
lerpVec2 t (Vec2 x1 y1) (Vec2 x2 y2) = 
  Vec2 (Math.lerp x1 x2 t) (Math.lerp y1 y2 t)

-- | Perpendicular vector (rotated 90 degrees counter-clockwise)
perpendicularVec2 :: forall a. Ring a => Vec2 a -> Vec2 a
perpendicularVec2 (Vec2 x y) = Vec2 (negate y) x

-- | Angle of a 2D vector in radians
angleVec2 :: Vec2 Number -> Number
angleVec2 (Vec2 x y) = Math.atan2 y x

-- | Get X component
getX2 :: forall a. Vec2 a -> a
getX2 (Vec2 x _) = x

-- | Get Y component
getY2 :: forall a. Vec2 a -> a
getY2 (Vec2 _ y) = y

-- | Set X component
setX2 :: forall a. a -> Vec2 a -> Vec2 a
setX2 x' (Vec2 _ y) = Vec2 x' y

-- | Set Y component
setY2 :: forall a. a -> Vec2 a -> Vec2 a
setY2 y' (Vec2 x _) = Vec2 x y'
