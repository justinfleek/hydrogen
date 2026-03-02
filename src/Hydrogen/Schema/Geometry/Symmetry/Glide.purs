-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // geometry // symmetry // glide
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Glide Reflection — Reflection combined with translation along axis.
-- |
-- | ## Design Philosophy
-- |
-- | A glide reflection combines:
-- | 1. Reflection across an axis
-- | 2. Translation along that axis
-- |
-- | Common in: footprints, frieze patterns, DNA helix
-- |
-- | ## Use Cases
-- |
-- | - Frieze patterns
-- | - Border designs
-- | - Biological structures
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)
-- | - Symmetry.Reflection (ReflectionAxis)

module Hydrogen.Schema.Geometry.Symmetry.Glide
  ( GlideReflection(GlideReflection)
  , glideReflection
  , horizontalGlide
  , verticalGlide
  , glideAxis
  , glideDistance
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Hydrogen.Schema.Geometry.Symmetry.Reflection
  ( ReflectionAxis
  , horizontalAxis
  , verticalAxis
  )

import Hydrogen.Schema.Geometry.Symmetry.Internal (absNumber)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // glide reflection
-- ═════════════════════════════════════════════════════════════════════════════

-- | Glide reflection: reflection + translation along the axis.
newtype GlideReflection = GlideReflection
  { axis :: ReflectionAxis
  , distance :: Number
  }

derive instance eqGlideReflection :: Eq GlideReflection
derive instance ordGlideReflection :: Ord GlideReflection

instance showGlideReflection :: Show GlideReflection where
  show (GlideReflection g) = 
    "(GlideReflection axis:" <> show g.axis <> " distance:" <> show g.distance <> ")"

-- | Create a glide reflection
glideReflection :: ReflectionAxis -> Number -> GlideReflection
glideReflection axis distance = GlideReflection { axis, distance: absNumber distance }

-- | Horizontal glide reflection
horizontalGlide :: Number -> GlideReflection
horizontalGlide distance = GlideReflection 
  { axis: horizontalAxis
  , distance: absNumber distance
  }

-- | Vertical glide reflection
verticalGlide :: Number -> GlideReflection
verticalGlide distance = GlideReflection 
  { axis: verticalAxis
  , distance: absNumber distance
  }

-- | Get the axis of a glide reflection
glideAxis :: GlideReflection -> ReflectionAxis
glideAxis (GlideReflection g) = g.axis

-- | Get the distance of a glide reflection
glideDistance :: GlideReflection -> Number
glideDistance (GlideReflection g) = g.distance
