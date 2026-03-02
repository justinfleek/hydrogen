-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // physics // collision // state
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | State — Collision state tracking.
-- |
-- | ## Design Philosophy
-- |
-- | Tracks the current collision state between two objects over time.
-- | This enables different behaviors based on collision phase:
-- | - OnEnter: just started colliding (play sound, trigger event)
-- | - OnStay: continuing to collide (apply damage over time)
-- | - OnExit: just stopped colliding (cleanup)
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)

module Hydrogen.Schema.Physics.Collision.State
  ( -- * Collision State
    CollisionState(NotColliding, Colliding, Separating, Resting, Sliding, Rolling)
  
  -- * State Queries
  , isColliding
  , isSeparating
  , isResting
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // collision state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Current collision state between two objects.
data CollisionState
  = NotColliding       -- ^ Objects are separated
  | Colliding          -- ^ Objects are overlapping
  | Separating         -- ^ Objects were colliding, now separating
  | Resting            -- ^ Objects in stable contact (not moving relative)
  | Sliding            -- ^ Objects in contact, sliding past each other
  | Rolling            -- ^ One object rolling on another

derive instance eqCollisionState :: Eq CollisionState
derive instance ordCollisionState :: Ord CollisionState

instance showCollisionState :: Show CollisionState where
  show NotColliding = "NotColliding"
  show Colliding = "Colliding"
  show Separating = "Separating"
  show Resting = "Resting"
  show Sliding = "Sliding"
  show Rolling = "Rolling"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // state queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if currently colliding.
-- |
-- | Returns true for any active contact state.
isColliding :: CollisionState -> Boolean
isColliding Colliding = true
isColliding Resting = true
isColliding Sliding = true
isColliding Rolling = true
isColliding NotColliding = false
isColliding Separating = false

-- | Check if separating.
-- |
-- | Returns true only during the frame when contact ends.
isSeparating :: CollisionState -> Boolean
isSeparating Separating = true
isSeparating NotColliding = false
isSeparating Colliding = false
isSeparating Resting = false
isSeparating Sliding = false
isSeparating Rolling = false

-- | Check if resting contact.
-- |
-- | Returns true for stable, non-moving contact.
isResting :: CollisionState -> Boolean
isResting Resting = true
isResting NotColliding = false
isResting Colliding = false
isResting Separating = false
isResting Sliding = false
isResting Rolling = false
