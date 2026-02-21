-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // dimension // vector // 4d
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | 4D vector type parameterized by component type.
-- | Used for homogeneous coordinates and quaternions.

module Hydrogen.Schema.Dimension.Vector.Vec4
  ( Vec4(..)
  , vec4
  , vec4Zero
  , vec4One
  , addVec4
  , subtractVec4
  , scaleVec4
  , negateVec4
  , dotVec4
  , lengthSquaredVec4
  , lengthVec4
  , normalizeVec4
  , lerpVec4
  , getX4
  , getY4
  , getZ4
  , getW4
  , setX4
  , setY4
  , setZ4
  , setW4
  ) where

import Prelude

import Hydrogen.Math.Core as Math

-- | 4D vector parameterized by component type
data Vec4 a = Vec4 a a a a

derive instance eqVec4 :: Eq a => Eq (Vec4 a)

instance showVec4 :: Show a => Show (Vec4 a) where
  show (Vec4 x y z w) = "Vec4(" <> show x <> ", " <> show y <> ", " <> show z <> ", " <> show w <> ")"

instance functorVec4 :: Functor Vec4 where
  map f (Vec4 x y z w) = Vec4 (f x) (f y) (f z) (f w)

-- | Create a 4D vector
vec4 :: forall a. a -> a -> a -> a -> Vec4 a
vec4 = Vec4

-- | Zero vector
vec4Zero :: forall a. Semiring a => Vec4 a
vec4Zero = Vec4 zero zero zero zero

-- | Unit vector (1,1,1,1)
vec4One :: forall a. Semiring a => Vec4 a
vec4One = Vec4 one one one one

-- | Add two 4D vectors
addVec4 :: forall a. Semiring a => Vec4 a -> Vec4 a -> Vec4 a
addVec4 (Vec4 x1 y1 z1 w1) (Vec4 x2 y2 z2 w2) = Vec4 (x1 + x2) (y1 + y2) (z1 + z2) (w1 + w2)

-- | Subtract two 4D vectors
subtractVec4 :: forall a. Ring a => Vec4 a -> Vec4 a -> Vec4 a
subtractVec4 (Vec4 x1 y1 z1 w1) (Vec4 x2 y2 z2 w2) = Vec4 (x1 - x2) (y1 - y2) (z1 - z2) (w1 - w2)

-- | Scale a 4D vector by a scalar
scaleVec4 :: forall a. Semiring a => a -> Vec4 a -> Vec4 a
scaleVec4 s (Vec4 x y z w) = Vec4 (s * x) (s * y) (s * z) (s * w)

-- | Negate a 4D vector
negateVec4 :: forall a. Ring a => Vec4 a -> Vec4 a
negateVec4 (Vec4 x y z w) = Vec4 (negate x) (negate y) (negate z) (negate w)

-- | Dot product of two 4D vectors
dotVec4 :: forall a. Semiring a => Vec4 a -> Vec4 a -> a
dotVec4 (Vec4 x1 y1 z1 w1) (Vec4 x2 y2 z2 w2) = x1 * x2 + y1 * y2 + z1 * z2 + w1 * w2

-- | Squared length of a 4D Number vector
lengthSquaredVec4 :: Vec4 Number -> Number
lengthSquaredVec4 v = dotVec4 v v

-- | Length of a 4D Number vector
lengthVec4 :: Vec4 Number -> Number
lengthVec4 v = Math.sqrt (lengthSquaredVec4 v)

-- | Normalize a 4D Number vector to unit length
normalizeVec4 :: Vec4 Number -> Vec4 Number
normalizeVec4 v =
  let len = lengthVec4 v
  in if len == 0.0 then v else scaleVec4 (1.0 / len) v

-- | Linear interpolation between two 4D vectors
lerpVec4 :: Number -> Vec4 Number -> Vec4 Number -> Vec4 Number
lerpVec4 t (Vec4 x1 y1 z1 w1) (Vec4 x2 y2 z2 w2) = 
  Vec4 (Math.lerp x1 x2 t) (Math.lerp y1 y2 t) (Math.lerp z1 z2 t) (Math.lerp w1 w2 t)

-- | Get X component
getX4 :: forall a. Vec4 a -> a
getX4 (Vec4 x _ _ _) = x

-- | Get Y component
getY4 :: forall a. Vec4 a -> a
getY4 (Vec4 _ y _ _) = y

-- | Get Z component
getZ4 :: forall a. Vec4 a -> a
getZ4 (Vec4 _ _ z _) = z

-- | Get W component
getW4 :: forall a. Vec4 a -> a
getW4 (Vec4 _ _ _ w) = w

-- | Set X component
setX4 :: forall a. a -> Vec4 a -> Vec4 a
setX4 x' (Vec4 _ y z w) = Vec4 x' y z w

-- | Set Y component
setY4 :: forall a. a -> Vec4 a -> Vec4 a
setY4 y' (Vec4 x _ z w) = Vec4 x y' z w

-- | Set Z component
setZ4 :: forall a. a -> Vec4 a -> Vec4 a
setZ4 z' (Vec4 x y _ w) = Vec4 x y z' w

-- | Set W component
setW4 :: forall a. a -> Vec4 a -> Vec4 a
setW4 w' (Vec4 x y z _) = Vec4 x y z w'
