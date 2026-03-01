-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--             // hydrogen // schema // motion // animated-transform // transform
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Transform — Complete AnimatedTransform2D and AnimatedTransform3D types.
-- |
-- | ## Design Philosophy
-- |
-- | The AnimatedTransform types combine all individual animated properties
-- | (position, scale, rotation, anchor, opacity) into a single coherent
-- | transform model matching After Effects' Layer Transform.
-- |
-- | ## Dependencies
-- |
-- | - AnimatedTransform.Properties (all property types)

module Hydrogen.Schema.Motion.AnimatedTransform.Transform
  ( -- * Animated Transform 2D
    AnimatedTransform2D(..)
  , defaultAnimatedTransform2D
  , identityAnimatedTransform2D
  
  -- * Animated Transform 3D
  , AnimatedTransform3D(..)
  , defaultAnimatedTransform3D
  , identityAnimatedTransform3D
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Hydrogen.Schema.Motion.AnimatedTransform.Properties
  ( AnimatedPosition2D
  , AnimatedPosition3D
  , AnimatedScale2D
  , AnimatedScale3D
  , AnimatedRotation
  , AnimatedRotation3D
  , AnimatedAnchor2D
  , AnimatedAnchor3D
  , AnimatedOpacity
  , defaultAnimatedPosition2D
  , defaultAnimatedPosition3D
  , defaultAnimatedScale2D
  , defaultAnimatedScale3D
  , defaultAnimatedRotation
  , defaultAnimatedRotation3D
  , defaultAnimatedAnchor2D
  , defaultAnimatedAnchor3D
  , defaultAnimatedOpacity
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                               // animated // transform // 2d
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete animated 2D transform.
-- |
-- | Contains all transform properties with full animation support.
-- | This is the After Effects Layer Transform model.
newtype AnimatedTransform2D = AnimatedTransform2D
  { position :: AnimatedPosition2D
  , scale :: AnimatedScale2D
  , rotation :: AnimatedRotation
  , anchor :: AnimatedAnchor2D
  , opacity :: AnimatedOpacity
  }

derive instance eqAnimatedTransform2D :: Eq AnimatedTransform2D

instance showAnimatedTransform2D :: Show AnimatedTransform2D where
  show (AnimatedTransform2D t) = 
    "AnimatedTransform2D { pos: " <> show t.position <>
    ", scale: " <> show t.scale <>
    ", rot: " <> show t.rotation <>
    ", anchor: " <> show t.anchor <>
    ", opacity: " <> show t.opacity <> " }"

-- | Default animated 2D transform.
defaultAnimatedTransform2D :: AnimatedTransform2D
defaultAnimatedTransform2D = AnimatedTransform2D
  { position: defaultAnimatedPosition2D
  , scale: defaultAnimatedScale2D
  , rotation: defaultAnimatedRotation
  , anchor: defaultAnimatedAnchor2D
  , opacity: defaultAnimatedOpacity
  }

-- | Identity animated transform (alias for default).
identityAnimatedTransform2D :: AnimatedTransform2D
identityAnimatedTransform2D = defaultAnimatedTransform2D

-- ═════════════════════════════════════════════════════════════════════════════
--                                               // animated // transform // 3d
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete animated 3D transform.
newtype AnimatedTransform3D = AnimatedTransform3D
  { position :: AnimatedPosition3D
  , scale :: AnimatedScale3D
  , rotation :: AnimatedRotation3D
  , anchor :: AnimatedAnchor3D
  , opacity :: AnimatedOpacity
  }

derive instance eqAnimatedTransform3D :: Eq AnimatedTransform3D

instance showAnimatedTransform3D :: Show AnimatedTransform3D where
  show (AnimatedTransform3D t) = 
    "AnimatedTransform3D { pos: " <> show t.position <>
    ", scale: " <> show t.scale <>
    ", rot: " <> show t.rotation <>
    ", anchor: " <> show t.anchor <>
    ", opacity: " <> show t.opacity <> " }"

-- | Default animated 3D transform.
defaultAnimatedTransform3D :: AnimatedTransform3D
defaultAnimatedTransform3D = AnimatedTransform3D
  { position: defaultAnimatedPosition3D
  , scale: defaultAnimatedScale3D
  , rotation: defaultAnimatedRotation3D
  , anchor: defaultAnimatedAnchor3D
  , opacity: defaultAnimatedOpacity
  }

-- | Identity animated 3D transform.
identityAnimatedTransform3D :: AnimatedTransform3D
identityAnimatedTransform3D = defaultAnimatedTransform3D
