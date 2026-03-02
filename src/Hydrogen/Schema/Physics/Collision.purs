-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // physics // collision
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Collision — Collision detection and contact resolution primitives.
-- |
-- | ## Design Philosophy
-- |
-- | Collision detection is fundamental to physics simulation and UI interaction.
-- | This module provides bounded, composable collision primitives that work at
-- | billion-agent scale — deterministic detection with no edge cases.
-- |
-- | ## Collision Categories
-- |
-- | **Bounding Volumes**: AABB, Sphere, Capsule, OBB
-- | **Detection Results**: Contact points, normals, penetration depth
-- | **Response Types**: Bounce, slide, stick, separate
-- |
-- | ## Bounded Design
-- |
-- | All collision results are bounded:
-- | - Penetration depth is clamped to prevent numerical explosion
-- | - Contact normals are always unit vectors
-- | - Contact counts are finite and bounded
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from submodules:
-- | - Collision.Point — 2D point primitives
-- | - Collision.Volumes — Bounding volume types (AABB, Circle, Capsule, OBB)
-- | - Collision.Contact — Contact information
-- | - Collision.Detection — Collision detection algorithms
-- | - Collision.Response — Response types and calculations
-- | - Collision.Layers — Layer filtering system
-- | - Collision.State — Collision state tracking
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)
-- | - Data.Number (sqrt, abs)
-- |
-- | ## Dependents
-- |
-- | - Motion.Physics (physics engine)
-- | - Component.Draggable (drag boundaries)
-- | - Component.Sortable (item collision)

module Hydrogen.Schema.Physics.Collision
  ( -- * 2D Points
    module Point
  
  -- * Bounding Volumes
  , module Volumes
  
  -- * Contact Information
  , module Contact
  
  -- * Collision Detection
  , module Detection
  
  -- * Collision Response
  , module Response
  
  -- * Collision Layers
  , module Layers
  
  -- * Collision State
  , module State
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Physics.Collision.Point
  ( Point2D(Point2D)
  , point2D
  , origin2D
  , distance
  , distanceSquared
  , midpoint
  , offsetPoint
  , normalizePoint
  , negatePoint
  ) as Point

import Hydrogen.Schema.Physics.Collision.Volumes
  ( AABB(AABB)
  , aabb
  , aabbFromPoints
  , aabbCenter
  , aabbSize
  , aabbHalfSize
  , aabbContains
  , aabbExpand
  , aabbMerge
  , BoundingCircle(BoundingCircle)
  , boundingCircle
  , circleContains
  , circleExpand
  , circleMerge
  , BoundingCapsule(BoundingCapsule)
  , boundingCapsule
  , capsuleContains
  , pointToSegmentDistance
  , OBB(OBB)
  , obb
  , obbCorners
  , obbContains
  ) as Volumes

import Hydrogen.Schema.Physics.Collision.Contact
  ( Contact(NoContact, Contact)
  , contact
  , noContact
  , hasContact
  , contactPoint
  , contactNormal
  , contactDepth
  , flipContact
  ) as Contact

import Hydrogen.Schema.Physics.Collision.Detection
  ( aabbVsAABB
  , aabbVsPoint
  , aabbVsCircle
  , circleVsCircle
  , circleVsPoint
  , circleVsAABB
  , capsuleVsPoint
  , capsuleVsCapsule
  , segmentSegmentDistance
  ) as Detection

import Hydrogen.Schema.Physics.Collision.Response
  ( CollisionResponse(ResponseNone, ResponseBounce, ResponseSlide, ResponseStick, ResponseCustom)
  , responseNone
  , responseBounce
  , responseSlide
  , responseStick
  , resolveOverlap
  , calculateBounce
  , calculateSlide
  ) as Response

import Hydrogen.Schema.Physics.Collision.Layers
  ( CollisionLayer(CollisionLayer)
  , CollisionMask(CollisionMask)
  , layerCollides
  , allLayers
  , noLayers
  ) as Layers

import Hydrogen.Schema.Physics.Collision.State
  ( CollisionState(NotColliding, Colliding, Separating, Resting, Sliding, Rolling)
  , isColliding
  , isSeparating
  , isResting
  ) as State
