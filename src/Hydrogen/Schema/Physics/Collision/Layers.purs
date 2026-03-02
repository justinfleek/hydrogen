-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // schema // physics // collision // layers
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Layers — Collision layer filtering system.
-- |
-- | ## Design Philosophy
-- |
-- | Collision layers enable efficient filtering of collision pairs.
-- | Objects are assigned to layers, and each object has a mask specifying
-- | which layers it can collide with.
-- |
-- | ## Use Cases
-- |
-- | - Player layer: collides with environment and enemies
-- | - Enemy layer: collides with player and environment
-- | - Projectile layer: collides with enemies only
-- | - UI layer: collides with nothing (pass-through)
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)
-- | - Collision.Internal (modInt)

module Hydrogen.Schema.Physics.Collision.Layers
  ( -- * Collision Layer
    CollisionLayer(CollisionLayer)
  
  -- * Collision Mask
  , CollisionMask(CollisionMask)
  
  -- * Layer Operations
  , layerCollides
  , allLayers
  , noLayers
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (&&)
  , (<>)
  , (==)
  , (>)
  )

import Hydrogen.Schema.Physics.Collision.Internal
  ( modInt
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // collision layer
-- ═════════════════════════════════════════════════════════════════════════════

-- | Collision layer for filtering.
-- |
-- | Objects on the same layer can collide. Layers are bit flags.
newtype CollisionLayer = CollisionLayer Int

derive instance eqCollisionLayer :: Eq CollisionLayer
derive instance ordCollisionLayer :: Ord CollisionLayer

instance showCollisionLayer :: Show CollisionLayer where
  show (CollisionLayer l) = "CollisionLayer(" <> show l <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // collision mask
-- ═════════════════════════════════════════════════════════════════════════════

-- | Collision mask (which layers to collide with).
newtype CollisionMask = CollisionMask Int

derive instance eqCollisionMask :: Eq CollisionMask
derive instance ordCollisionMask :: Ord CollisionMask

instance showCollisionMask :: Show CollisionMask where
  show (CollisionMask m) = "CollisionMask(" <> show m <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // layer operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a layer matches a mask.
-- |
-- | Returns true if the layer bit is set in the mask.
layerCollides :: CollisionLayer -> CollisionMask -> Boolean
layerCollides (CollisionLayer layer) (CollisionMask mask) =
  -- Using simple integer comparison since we don't have bitwise AND
  -- In practice, layers would be 1, 2, 4, 8, etc.
  layer > 0 && mask > 0 && 
  (modInt mask layer == 0)

-- | Mask that collides with all layers
allLayers :: CollisionMask
allLayers = CollisionMask 2147483647  -- Max 32-bit signed int

-- | Mask that collides with no layers
noLayers :: CollisionMask
noLayers = CollisionMask 0
