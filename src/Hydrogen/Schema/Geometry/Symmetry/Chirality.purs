-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                      // hydrogen // schema // geometry // symmetry // chirality
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Chirality — Handedness of shapes.
-- |
-- | ## Design Philosophy
-- |
-- | A chiral shape cannot be superimposed on its mirror image.
-- | An achiral shape has reflection symmetry.
-- |
-- | ## Use Cases
-- |
-- | - Determining if a shape needs left/right variants
-- | - Accessibility considerations
-- | - Symmetry classification
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)
-- | - Symmetry.Group (SymmetryGroup, hasReflection)

module Hydrogen.Schema.Geometry.Symmetry.Chirality
  ( Chirality(..)
  , isChiral
  , isAchiral
  , chiralityOf
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  )

import Hydrogen.Schema.Geometry.Symmetry.Group (SymmetryGroup, hasReflection)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // chirality
-- ═════════════════════════════════════════════════════════════════════════════

-- | Chirality: handedness of a shape.
-- |
-- | A chiral shape cannot be superimposed on its mirror image.
-- | An achiral shape is identical to its mirror image.
data Chirality
  = Chiral        -- ^ Shape differs from its mirror image
  | Achiral       -- ^ Shape is identical to its mirror image

derive instance eqChirality :: Eq Chirality
derive instance ordChirality :: Ord Chirality

instance showChirality :: Show Chirality where
  show Chiral = "Chiral"
  show Achiral = "Achiral"

-- | Check if a shape is chiral (no reflection symmetry)
isChiral :: Chirality -> Boolean
isChiral Chiral = true
isChiral Achiral = false

-- | Check if a shape is achiral (has reflection symmetry)
isAchiral :: Chirality -> Boolean
isAchiral Achiral = true
isAchiral Chiral = false

-- | Determine chirality from symmetry group
chiralityOf :: SymmetryGroup -> Chirality
chiralityOf group = if hasReflection group then Achiral else Chiral
