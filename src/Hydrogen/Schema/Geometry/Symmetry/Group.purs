-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // geometry // symmetry // group
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Symmetry Group — Combined symmetry types for a shape.
-- |
-- | ## Design Philosophy
-- |
-- | A shape can have multiple types of symmetry simultaneously.
-- | This type captures all symmetries present in a single structure.
-- |
-- | ## Use Cases
-- |
-- | - Complete symmetry specification for shapes
-- | - Symmetry comparison and combination
-- | - Accessibility analysis (symmetric UI aids comprehension)
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Show)
-- | - Data.Maybe (Maybe)
-- | - Symmetry.Reflection (ReflectionAxis)
-- | - Symmetry.Rotational (RotationalSymmetry)
-- | - Symmetry.Dihedral (DihedralSymmetry)
-- | - Symmetry.Translational (TranslationalSymmetry)
-- | - Symmetry.Glide (GlideReflection)

module Hydrogen.Schema.Geometry.Symmetry.Group
  ( SymmetryGroup(..)
  , noSymmetry
  , identitySymmetry
  , reflectionOnly
  , rotationOnly
  , dihedralOnly
  , translationOnly
  , fullSymmetry
  , hasReflection
  , hasRotation
  , hasDihedral
  , hasTranslation
  , hasGlide
  , combineSymmetry
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (>=)
  , (<>)
  , (<)
  , (||)
  , otherwise
  )

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Geometry.Symmetry.Reflection (ReflectionAxis)

import Hydrogen.Schema.Geometry.Symmetry.Rotational 
  ( RotationalSymmetry(..)
  , rotationalSymmetry
  , noRotationalSymmetry
  , hasRotationalSymmetry
  , circular
  , foldCount
  )

import Hydrogen.Schema.Geometry.Symmetry.Dihedral 
  ( DihedralSymmetry(..)
  , dihedralFoldCount
  )

import Hydrogen.Schema.Geometry.Symmetry.Translational 
  ( TranslationalSymmetry
  , hasTranslationalSymmetry
  )

import Hydrogen.Schema.Geometry.Symmetry.Glide (GlideReflection)

import Hydrogen.Schema.Geometry.Symmetry.Internal (showMaybe)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // symmetry group
-- ═════════════════════════════════════════════════════════════════════════════

-- | Combined symmetry group for a shape.
-- |
-- | A shape can have multiple types of symmetry simultaneously.
-- | This type captures all symmetries present.
data SymmetryGroup = SymmetryGroup
  { reflection :: Maybe ReflectionAxis
  , rotation :: RotationalSymmetry
  , dihedral :: Maybe DihedralSymmetry
  , translation :: Maybe TranslationalSymmetry
  , glide :: Maybe GlideReflection
  }

derive instance eqSymmetryGroup :: Eq SymmetryGroup

instance showSymmetryGroup :: Show SymmetryGroup where
  show (SymmetryGroup s) = 
    "(SymmetryGroup " 
      <> "reflection:" <> showMaybe s.reflection
      <> " rotation:" <> show s.rotation
      <> " dihedral:" <> showMaybe s.dihedral
      <> ")"

-- | No symmetry at all
noSymmetry :: SymmetryGroup
noSymmetry = SymmetryGroup
  { reflection: Nothing
  , rotation: noRotationalSymmetry
  , dihedral: Nothing
  , translation: Nothing
  , glide: Nothing
  }

-- | Identity symmetry (trivial, all shapes have this)
identitySymmetry :: SymmetryGroup
identitySymmetry = noSymmetry

-- | Reflection symmetry only
reflectionOnly :: ReflectionAxis -> SymmetryGroup
reflectionOnly axis = SymmetryGroup
  { reflection: Just axis
  , rotation: noRotationalSymmetry
  , dihedral: Nothing
  , translation: Nothing
  , glide: Nothing
  }

-- | Rotational symmetry only
rotationOnly :: RotationalSymmetry -> SymmetryGroup
rotationOnly rot = SymmetryGroup
  { reflection: Nothing
  , rotation: rot
  , dihedral: Nothing
  , translation: Nothing
  , glide: Nothing
  }

-- | Dihedral symmetry only
dihedralOnly :: DihedralSymmetry -> SymmetryGroup
dihedralOnly dih = SymmetryGroup
  { reflection: Nothing
  , rotation: rotationalSymmetry (dihedralFoldCount dih)
  , dihedral: Just dih
  , translation: Nothing
  , glide: Nothing
  }

-- | Translational symmetry only
translationOnly :: TranslationalSymmetry -> SymmetryGroup
translationOnly trans = SymmetryGroup
  { reflection: Nothing
  , rotation: noRotationalSymmetry
  , dihedral: Nothing
  , translation: Just trans
  , glide: Nothing
  }

-- | Full symmetry group with all components
fullSymmetry :: Maybe ReflectionAxis 
             -> RotationalSymmetry 
             -> Maybe DihedralSymmetry 
             -> Maybe TranslationalSymmetry 
             -> Maybe GlideReflection 
             -> SymmetryGroup
fullSymmetry reflection rotation dihedral translation glide = SymmetryGroup
  { reflection, rotation, dihedral, translation, glide }

-- | Check if group has reflection symmetry
hasReflection :: SymmetryGroup -> Boolean
hasReflection (SymmetryGroup s) = case s.reflection of
  Just _ -> true
  Nothing -> case s.dihedral of
    Just _ -> true  -- dihedral includes reflections
    Nothing -> false

-- | Check if group has rotational symmetry
hasRotation :: SymmetryGroup -> Boolean
hasRotation (SymmetryGroup s) = hasRotationalSymmetry s.rotation

-- | Check if group has dihedral symmetry
hasDihedral :: SymmetryGroup -> Boolean
hasDihedral (SymmetryGroup s) = case s.dihedral of
  Just _ -> true
  Nothing -> false

-- | Check if group has translational symmetry
hasTranslation :: SymmetryGroup -> Boolean
hasTranslation (SymmetryGroup s) = case s.translation of
  Just t -> hasTranslationalSymmetry t
  Nothing -> false

-- | Check if group has glide reflection
hasGlide :: SymmetryGroup -> Boolean
hasGlide (SymmetryGroup s) = case s.glide of
  Just _ -> true
  Nothing -> false

-- | Combine two symmetry groups (union of symmetries)
combineSymmetry :: SymmetryGroup -> SymmetryGroup -> SymmetryGroup
combineSymmetry (SymmetryGroup a) (SymmetryGroup b) = SymmetryGroup
  { reflection: combineReflection a.reflection b.reflection
  , rotation: combineRotation a.rotation b.rotation
  , dihedral: combineDihedral a.dihedral b.dihedral
  , translation: combineTranslation a.translation b.translation
  , glide: combineGlide a.glide b.glide
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // combine helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Helper: combine optional reflections
combineReflection :: Maybe ReflectionAxis -> Maybe ReflectionAxis -> Maybe ReflectionAxis
combineReflection Nothing b = b
combineReflection a Nothing = a
combineReflection a _ = a  -- prefer first

-- | Helper: combine rotations (take higher fold count)
combineRotation :: RotationalSymmetry -> RotationalSymmetry -> RotationalSymmetry
combineRotation ra rb =
  let a = foldCount ra
      b = foldCount rb
  in if a < 0 || b < 0 
     then circular  -- either circular -> circular
     else if a >= b 
          then ra
          else rb

-- | Helper: combine dihedral (take higher n)
combineDihedral :: Maybe DihedralSymmetry -> Maybe DihedralSymmetry -> Maybe DihedralSymmetry
combineDihedral Nothing b = b
combineDihedral a Nothing = a
combineDihedral (Just (DihedralSymmetry a)) (Just (DihedralSymmetry b))
  | a.n >= b.n = Just (DihedralSymmetry a)
  | otherwise = Just (DihedralSymmetry b)

-- | Helper: combine translations
combineTranslation :: Maybe TranslationalSymmetry -> Maybe TranslationalSymmetry -> Maybe TranslationalSymmetry
combineTranslation Nothing b = b
combineTranslation a Nothing = a
combineTranslation a _ = a  -- prefer first

-- | Helper: combine glides
combineGlide :: Maybe GlideReflection -> Maybe GlideReflection -> Maybe GlideReflection
combineGlide Nothing b = b
combineGlide a Nothing = a
combineGlide a _ = a  -- prefer first
