-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                     // hydrogen // schema // physics // collision // response
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Response — Collision response types and calculations.
-- |
-- | ## Design Philosophy
-- |
-- | Collision response determines what happens when two objects collide.
-- | Different response types enable different physical behaviors:
-- | - Bounce: elastic collision (balls, pinball)
-- | - Slide: friction-based movement (boxes on ground)
-- | - Stick: adhesion (sticky surfaces, grappling hooks)
-- |
-- | ## Bounded Design
-- |
-- | All response parameters are bounded:
-- | - Restitution: 0-1 (inelastic to perfectly elastic)
-- | - Friction: 0-2 (frictionless to high friction)
-- |
-- | ## Dependencies
-- |
-- | - Collision.Point (Point2D)
-- | - Collision.Contact (Contact)
-- | - Collision.Internal (clampUnit, maxNum)

module Hydrogen.Schema.Physics.Collision.Response
  ( -- * Response Types
    CollisionResponse(ResponseNone, ResponseBounce, ResponseSlide, ResponseStick, ResponseCustom)
  , responseNone
  , responseBounce
  , responseSlide
  , responseStick
  
  -- * Response Calculation
  , resolveOverlap
  , calculateBounce
  , calculateSlide
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (*)
  , (+)
  , (-)
  , (<>)
  , (>=)
  )

import Hydrogen.Schema.Physics.Collision.Point
  ( Point2D(Point2D)
  )

import Hydrogen.Schema.Physics.Collision.Contact
  ( Contact(NoContact, Contact)
  )

import Hydrogen.Schema.Physics.Collision.Internal
  ( clampUnit
  , maxNum
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // response type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Collision response type.
data CollisionResponse
  = ResponseNone     -- ^ No response (pass through)
  | ResponseBounce   -- ^ Elastic bounce
      { restitution :: Number }  -- ^ Bounciness (0 = no bounce, 1 = perfect bounce)
  | ResponseSlide    -- ^ Slide along surface
      { friction :: Number }     -- ^ Friction coefficient
  | ResponseStick    -- ^ Stick to surface
  | ResponseCustom   -- ^ Custom response (handled by application)
      { id :: Int }

derive instance eqCollisionResponse :: Eq CollisionResponse

instance showCollisionResponse :: Show CollisionResponse where
  show ResponseNone = "ResponseNone"
  show (ResponseBounce r) = "ResponseBounce(e=" <> show r.restitution <> ")"
  show (ResponseSlide r) = "ResponseSlide(μ=" <> show r.friction <> ")"
  show ResponseStick = "ResponseStick"
  show (ResponseCustom r) = "ResponseCustom(" <> show r.id <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // response factories
-- ═════════════════════════════════════════════════════════════════════════════

-- | No collision response
responseNone :: CollisionResponse
responseNone = ResponseNone

-- | Bounce response with restitution coefficient
responseBounce :: Number -> CollisionResponse
responseBounce e = ResponseBounce { restitution: clampUnit 1.0 e }

-- | Slide response with friction coefficient
responseSlide :: Number -> CollisionResponse
responseSlide f = ResponseSlide { friction: clampUnit 2.0 f }

-- | Stick response (no sliding)
responseStick :: CollisionResponse
responseStick = ResponseStick

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // response calculation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate position offset to resolve overlap.
-- |
-- | Returns (dx, dy) to add to position to separate objects.
resolveOverlap :: Contact -> { dx :: Number, dy :: Number }
resolveOverlap NoContact = { dx: 0.0, dy: 0.0 }
resolveOverlap (Contact c) =
  let Point2D n = c.normal
  in { dx: n.x * c.depth, dy: n.y * c.depth }

-- | Calculate bounce velocity.
-- |
-- | Reflects velocity around contact normal with restitution.
calculateBounce 
  :: { vx :: Number, vy :: Number }  -- ^ Incoming velocity
  -> Contact                          -- ^ Contact information
  -> Number                           -- ^ Restitution (0-1)
  -> { vx :: Number, vy :: Number }   -- ^ Outgoing velocity
calculateBounce vel NoContact _ = vel
calculateBounce vel (Contact c) restitution =
  let
    Point2D n = c.normal
    -- Velocity component along normal
    vn = vel.vx * n.x + vel.vy * n.y
  in if vn >= 0.0
     then vel  -- Already separating
     else
       -- Reflect: v' = v - (1 + e) * (v · n) * n
       let factor = (1.0 + restitution) * vn
       in { vx: vel.vx - factor * n.x
          , vy: vel.vy - factor * n.y
          }

-- | Calculate slide velocity.
-- |
-- | Projects velocity onto surface tangent with friction.
calculateSlide
  :: { vx :: Number, vy :: Number }  -- ^ Incoming velocity
  -> Contact                          -- ^ Contact information
  -> Number                           -- ^ Friction coefficient
  -> { vx :: Number, vy :: Number }   -- ^ Outgoing velocity
calculateSlide vel NoContact _ = vel
calculateSlide vel (Contact c) friction =
  let
    Point2D n = c.normal
    -- Velocity component along normal
    vn = vel.vx * n.x + vel.vy * n.y
  in if vn >= 0.0
     then vel  -- Already separating
     else
       -- Remove normal component, apply friction to tangent
       let
         -- Tangent velocity
         tvx = vel.vx - vn * n.x
         tvy = vel.vy - vn * n.y
         -- Apply friction (reduce tangent velocity)
         frictionFactor = maxNum 0.0 (1.0 - friction)
       in { vx: tvx * frictionFactor
          , vy: tvy * frictionFactor
          }
