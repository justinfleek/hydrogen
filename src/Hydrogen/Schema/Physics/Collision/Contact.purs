-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                      // hydrogen // schema // physics // collision // contact
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Contact — Collision contact information.
-- |
-- | ## Design Philosophy
-- |
-- | Contact information captures everything needed to resolve a collision:
-- | - Where the collision happened (contact point)
-- | - Which direction to push apart (normal)
-- | - How much they overlap (penetration depth)
-- |
-- | ## Bounded Design
-- |
-- | All contact values are bounded:
-- | - Contact normals are always unit vectors
-- | - Penetration depth is clamped to prevent numerical explosion
-- |
-- | ## Dependencies
-- |
-- | - Collision.Point (Point2D)
-- | - Collision.Internal (clampDepth)

module Hydrogen.Schema.Physics.Collision.Contact
  ( -- * Contact Type
    Contact(NoContact, Contact)
  
  -- * Construction
  , contact
  , noContact
  
  -- * Queries
  , hasContact
  , contactPoint
  , contactNormal
  , contactDepth
  
  -- * Operations
  , flipContact
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

import Hydrogen.Schema.Physics.Collision.Point
  ( Point2D(Point2D)
  , origin2D
  , normalizePoint
  , negatePoint
  )

import Hydrogen.Schema.Physics.Collision.Internal
  ( clampDepth
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // contact
-- ═════════════════════════════════════════════════════════════════════════════

-- | Contact information from collision detection.
-- |
-- | Contains everything needed to resolve a collision:
-- | - Where the collision happened (contact point)
-- | - Which direction to push apart (normal)
-- | - How much they overlap (penetration depth)
data Contact
  = NoContact
  | Contact
      { point :: Point2D     -- ^ Contact point (on surface of first object)
      , normal :: Point2D    -- ^ Contact normal (unit vector, points from first to second)
      , depth :: Number      -- ^ Penetration depth (positive = overlapping)
      }

derive instance eqContact :: Eq Contact

instance showContact :: Show Contact where
  show NoContact = "NoContact"
  show (Contact c) = "Contact(depth=" <> show c.depth <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a contact with normalized normal and clamped depth
contact :: Point2D -> Point2D -> Number -> Contact
contact point normal depth = Contact
  { point
  , normal: normalizePoint normal
  , depth: clampDepth depth
  }

-- | No contact result
noContact :: Contact
noContact = NoContact

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if there is a contact
hasContact :: Contact -> Boolean
hasContact NoContact = false
hasContact (Contact _) = true

-- | Get contact point (origin if no contact)
contactPoint :: Contact -> Point2D
contactPoint NoContact = origin2D
contactPoint (Contact c) = c.point

-- | Get contact normal (zero if no contact)
contactNormal :: Contact -> Point2D
contactNormal NoContact = origin2D
contactNormal (Contact c) = c.normal

-- | Get penetration depth (0 if no contact)
contactDepth :: Contact -> Number
contactDepth NoContact = 0.0
contactDepth (Contact c) = c.depth

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Flip contact (swap which object is "first")
flipContact :: Contact -> Contact
flipContact NoContact = NoContact
flipContact (Contact c) = Contact
  { point: c.point
  , normal: negatePoint c.normal
  , depth: c.depth
  }
