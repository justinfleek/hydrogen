-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                   // hydrogen // schema // geometry // symmetry // translational
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Translational Symmetry — Periodic repetition.
-- |
-- | ## Design Philosophy
-- |
-- | A shape has translational symmetry if it looks the same when shifted
-- | by a fixed distance. This is the foundation of:
-- | - Patterns and tiles
-- | - Repeating backgrounds
-- | - Infinite scroll illusions
-- |
-- | ## Use Cases
-- |
-- | - Tiling patterns
-- | - Repeating UI elements
-- | - Wallpaper and fabric design
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)

module Hydrogen.Schema.Geometry.Symmetry.Translational
  ( TranslationalSymmetry(TranslationalSymmetry)
  , translationalSymmetry
  , periodicX
  , periodicY
  , periodicXY
  , latticeSymmetry
  , periodX
  , periodY
  , hasTranslationalSymmetry
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (||)
  , (<>)
  , (>)
  )

import Hydrogen.Schema.Geometry.Symmetry.Internal (absNumber)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // translational symmetry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Translational symmetry: periodic repetition.
-- |
-- | A shape has translational symmetry if it looks the same when shifted
-- | by a fixed distance.
newtype TranslationalSymmetry = TranslationalSymmetry 
  { periodX :: Number
  , periodY :: Number
  }

derive instance eqTranslationalSymmetry :: Eq TranslationalSymmetry
derive instance ordTranslationalSymmetry :: Ord TranslationalSymmetry

instance showTranslationalSymmetry :: Show TranslationalSymmetry where
  show (TranslationalSymmetry t) = 
    "(TranslationalSymmetry periodX:" <> show t.periodX <> " periodY:" <> show t.periodY <> ")"

-- | Create translational symmetry with given periods
translationalSymmetry :: Number -> Number -> TranslationalSymmetry
translationalSymmetry px py = TranslationalSymmetry 
  { periodX: absNumber px
  , periodY: absNumber py
  }

-- | Horizontal periodic symmetry only
periodicX :: Number -> TranslationalSymmetry
periodicX px = TranslationalSymmetry { periodX: absNumber px, periodY: 0.0 }

-- | Vertical periodic symmetry only
periodicY :: Number -> TranslationalSymmetry
periodicY py = TranslationalSymmetry { periodX: 0.0, periodY: absNumber py }

-- | Both horizontal and vertical periodic symmetry
periodicXY :: Number -> Number -> TranslationalSymmetry
periodicXY = translationalSymmetry

-- | Alias for periodicXY (lattice terminology)
latticeSymmetry :: Number -> Number -> TranslationalSymmetry
latticeSymmetry = translationalSymmetry

-- | Get the X period (0 means no X symmetry)
periodX :: TranslationalSymmetry -> Number
periodX (TranslationalSymmetry t) = t.periodX

-- | Get the Y period (0 means no Y symmetry)
periodY :: TranslationalSymmetry -> Number
periodY (TranslationalSymmetry t) = t.periodY

-- | Check if shape has any translational symmetry
hasTranslationalSymmetry :: TranslationalSymmetry -> Boolean
hasTranslationalSymmetry (TranslationalSymmetry t) = 
  t.periodX > 0.0 || t.periodY > 0.0
