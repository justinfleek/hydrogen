-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                      // hydrogen // schema // geometry // symmetry // rotational
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Rotational Symmetry — N-fold rotation invariance.
-- |
-- | ## Design Philosophy
-- |
-- | An N-fold rotational symmetry means the shape looks identical after
-- | rotation by 360°/N. For example:
-- | - 2-fold: looks same after 180° rotation (rectangle)
-- | - 3-fold: looks same after 120° rotation (equilateral triangle)
-- | - 4-fold: looks same after 90° rotation (square)
-- | - ∞-fold: looks same after any rotation (circle)
-- |
-- | ## Use Cases
-- |
-- | - Radial UI elements (color wheels, dials)
-- | - Regular polygon generation
-- | - Mandala and snowflake patterns
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)
-- | - Geometry.Angle (Degrees)
-- | - Data.Maybe (Maybe)

module Hydrogen.Schema.Geometry.Symmetry.Rotational
  ( RotationalSymmetry(RotationalSymmetry)
  , rotationalSymmetry
  , noRotationalSymmetry
  , bilateral
  , trilateral
  , quadrilateral
  , pentagonal
  , hexagonal
  , octagonal
  , circular
  , foldCount
  , rotationAngle
  , isNFold
  , hasRotationalSymmetry
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (==)
  , (||)
  , (<>)
  , (/)
  , (<)
  , (>=)
  , negate
  , otherwise
  )

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Geometry.Angle 
  ( Degrees
  , degrees
  )

import Hydrogen.Schema.Geometry.Symmetry.Internal (intToNumber)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // rotational symmetry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rotational symmetry with N-fold rotation.
-- |
-- | We use `folds = 0` to represent no rotational symmetry,
-- | and `folds = -1` to represent continuous (circular) symmetry.
newtype RotationalSymmetry = RotationalSymmetry { folds :: Int }

derive instance eqRotationalSymmetry :: Eq RotationalSymmetry
derive instance ordRotationalSymmetry :: Ord RotationalSymmetry

instance showRotationalSymmetry :: Show RotationalSymmetry where
  show (RotationalSymmetry r) = "(RotationalSymmetry folds:" <> show r.folds <> ")"

-- | Create rotational symmetry with N folds.
-- | Values < 1 are treated as no symmetry, except -1 means circular.
rotationalSymmetry :: Int -> RotationalSymmetry
rotationalSymmetry n
  | n < 0 = RotationalSymmetry { folds: -1 }  -- circular
  | n < 2 = RotationalSymmetry { folds: 0 }   -- no symmetry (1-fold is trivial)
  | otherwise = RotationalSymmetry { folds: n }

-- | No rotational symmetry
noRotationalSymmetry :: RotationalSymmetry
noRotationalSymmetry = RotationalSymmetry { folds: 0 }

-- | 2-fold rotational symmetry (180° rotation)
bilateral :: RotationalSymmetry
bilateral = RotationalSymmetry { folds: 2 }

-- | 3-fold rotational symmetry (120° rotation)
trilateral :: RotationalSymmetry
trilateral = RotationalSymmetry { folds: 3 }

-- | 4-fold rotational symmetry (90° rotation)
quadrilateral :: RotationalSymmetry
quadrilateral = RotationalSymmetry { folds: 4 }

-- | 5-fold rotational symmetry (72° rotation)
pentagonal :: RotationalSymmetry
pentagonal = RotationalSymmetry { folds: 5 }

-- | 6-fold rotational symmetry (60° rotation)
hexagonal :: RotationalSymmetry
hexagonal = RotationalSymmetry { folds: 6 }

-- | 8-fold rotational symmetry (45° rotation)
octagonal :: RotationalSymmetry
octagonal = RotationalSymmetry { folds: 8 }

-- | Continuous rotational symmetry (circle)
circular :: RotationalSymmetry
circular = RotationalSymmetry { folds: -1 }

-- | Get the number of folds (0 = none, -1 = continuous)
foldCount :: RotationalSymmetry -> Int
foldCount (RotationalSymmetry r) = r.folds

-- | Get the rotation angle for this symmetry
rotationAngle :: RotationalSymmetry -> Maybe Degrees
rotationAngle (RotationalSymmetry r)
  | r.folds < 0 = Nothing  -- continuous, any angle works
  | r.folds < 2 = Nothing  -- no symmetry
  | otherwise = Just (degrees (360.0 / intToNumber r.folds))

-- | Check if this is exactly N-fold symmetry
isNFold :: Int -> RotationalSymmetry -> Boolean
isNFold n (RotationalSymmetry r) = r.folds == n

-- | Check if shape has any rotational symmetry
hasRotationalSymmetry :: RotationalSymmetry -> Boolean
hasRotationalSymmetry (RotationalSymmetry r) = r.folds >= 2 || r.folds < 0
