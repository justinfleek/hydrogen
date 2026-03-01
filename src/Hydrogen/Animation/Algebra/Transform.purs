-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // animation // algebra // transform
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Transform types for 2D and 3D animations.
-- |
-- | Transforms compose via matrix multiplication (Semigroup).
-- | Identity transforms are the Monoid identity.

module Hydrogen.Animation.Algebra.Transform
  ( Transform2D(Transform2D)
  , Transform3D(Transform3D)
  , TransformOrigin(TransformOrigin)
  , Opacity(Opacity)
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Semigroup
  , class Monoid
  , (+)
  , (*)
  )

import Data.Newtype (class Newtype)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 2D Transform
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | 2D affine transform represented as a 3x3 matrix (6 values).
-- | [ a c e ]
-- | [ b d f ]
-- | [ 0 0 1 ]
newtype Transform2D = Transform2D
  { a :: Number  -- scale x
  , b :: Number  -- skew y
  , c :: Number  -- skew x
  , d :: Number  -- scale y
  , e :: Number  -- translate x
  , f :: Number  -- translate y
  }

derive instance Eq Transform2D

-- | Transform composition is matrix multiplication.
-- | This is associative but NOT commutative.
instance Semigroup Transform2D where
  append (Transform2D t1) (Transform2D t2) = Transform2D
    { a: t1.a * t2.a + t1.c * t2.b
    , b: t1.b * t2.a + t1.d * t2.b
    , c: t1.a * t2.c + t1.c * t2.d
    , d: t1.b * t2.c + t1.d * t2.d
    , e: t1.a * t2.e + t1.c * t2.f + t1.e
    , f: t1.b * t2.e + t1.d * t2.f + t1.f
    }

-- | Identity transform.
instance Monoid Transform2D where
  mempty = Transform2D { a: 1.0, b: 0.0, c: 0.0, d: 1.0, e: 0.0, f: 0.0 }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 3D Transform
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | 3D transform for perspective and rotation.
-- | Represented as a 4x4 matrix (16 values).
newtype Transform3D = Transform3D
  { m11 :: Number, m12 :: Number, m13 :: Number, m14 :: Number
  , m21 :: Number, m22 :: Number, m23 :: Number, m24 :: Number
  , m31 :: Number, m32 :: Number, m33 :: Number, m34 :: Number
  , m41 :: Number, m42 :: Number, m43 :: Number, m44 :: Number
  }

derive instance Eq Transform3D

instance Semigroup Transform3D where
  append (Transform3D a) (Transform3D b) = Transform3D
    { m11: a.m11*b.m11 + a.m12*b.m21 + a.m13*b.m31 + a.m14*b.m41
    , m12: a.m11*b.m12 + a.m12*b.m22 + a.m13*b.m32 + a.m14*b.m42
    , m13: a.m11*b.m13 + a.m12*b.m23 + a.m13*b.m33 + a.m14*b.m43
    , m14: a.m11*b.m14 + a.m12*b.m24 + a.m13*b.m34 + a.m14*b.m44
    , m21: a.m21*b.m11 + a.m22*b.m21 + a.m23*b.m31 + a.m24*b.m41
    , m22: a.m21*b.m12 + a.m22*b.m22 + a.m23*b.m32 + a.m24*b.m42
    , m23: a.m21*b.m13 + a.m22*b.m23 + a.m23*b.m33 + a.m24*b.m43
    , m24: a.m21*b.m14 + a.m22*b.m24 + a.m23*b.m34 + a.m24*b.m44
    , m31: a.m31*b.m11 + a.m32*b.m21 + a.m33*b.m31 + a.m34*b.m41
    , m32: a.m31*b.m12 + a.m32*b.m22 + a.m33*b.m32 + a.m34*b.m42
    , m33: a.m31*b.m13 + a.m32*b.m23 + a.m33*b.m33 + a.m34*b.m43
    , m34: a.m31*b.m14 + a.m32*b.m24 + a.m33*b.m34 + a.m34*b.m44
    , m41: a.m41*b.m11 + a.m42*b.m21 + a.m43*b.m31 + a.m44*b.m41
    , m42: a.m41*b.m12 + a.m42*b.m22 + a.m43*b.m32 + a.m44*b.m42
    , m43: a.m41*b.m13 + a.m42*b.m23 + a.m43*b.m33 + a.m44*b.m43
    , m44: a.m41*b.m14 + a.m42*b.m24 + a.m43*b.m34 + a.m44*b.m44
    }

instance Monoid Transform3D where
  mempty = Transform3D
    { m11: 1.0, m12: 0.0, m13: 0.0, m14: 0.0
    , m21: 0.0, m22: 1.0, m23: 0.0, m24: 0.0
    , m31: 0.0, m32: 0.0, m33: 1.0, m34: 0.0
    , m41: 0.0, m42: 0.0, m43: 0.0, m44: 1.0
    }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- Transform Origin
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Transform origin point for rotations and scaling.
newtype TransformOrigin = TransformOrigin
  { x :: Number  -- 0.0 = left, 0.5 = center, 1.0 = right
  , y :: Number  -- 0.0 = top, 0.5 = center, 1.0 = bottom
  }

derive instance Eq TransformOrigin

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- Opacity
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Opacity value, bounded [0, 1].
newtype Opacity = Opacity Number

derive instance Newtype Opacity _
derive instance Eq Opacity
derive instance Ord Opacity

-- | Opacity composes multiplicatively.
-- | This models layered transparency: 0.5 * 0.5 = 0.25.
instance Semigroup Opacity where
  append (Opacity a) (Opacity b) = Opacity (a * b)

-- | Full opacity (1.0) is the identity.
instance Monoid Opacity where
  mempty = Opacity 1.0
