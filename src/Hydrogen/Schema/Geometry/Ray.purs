-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // schema // geometry // ray
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Ray definition for ray casting and intersection tests.
-- |
-- | ## Proof References
-- | All operations correspond to proven theorems in `proofs/Hydrogen/Math/Ray.lean`:
-- | - pointAt_zero: Ray.pointAt(0) = origin
-- | - pointAt_one: Ray.pointAt(1) = origin + direction
-- | - pointAt_add: pointAt is linear in t
-- | - recast_zero: recast by 0 is identity
-- | - recast_direction: recast preserves direction
-- | - reverse_reverse: reverse is involutive
-- |
-- | ## Three.js Parity
-- | - set, at, lookAt, recast
-- | - closestPointToPoint, distanceToPoint, distanceSqToPoint
-- | - intersectSphere, intersectPlane, intersectBox, intersectTriangle
-- |
-- | ## Applications
-- | - Ray casting for picking/selection
-- | - Collision detection
-- | - Line-of-sight checks
-- | - Physics simulation

module Hydrogen.Schema.Geometry.Ray
  ( -- * Type
    Ray(Ray)
  
  -- * Constructors
  , ray
  , rayDefault
  , rayFromPoints
  
  -- * Basic Operations
  , pointAt
  , lookAtRay
  , recast
  , reverseRay
  
  -- * Closest Point Operations
  , closestPointParameter
  , closestPointToPointOnLine
  , closestPointToPoint
  , distanceToPointOnLine
  , distanceSqToPointOnLine
  , distanceToPoint
  , distanceSqToPoint
  
  -- * Accessors
  , getOrigin
  , getDirection
  ) where

import Prelude
  ( class Eq
  , class Show
  , max
  , show
  , (+)
  , (-)
  , (*)
  , (/)
  , (==)
  , (<>)
  )

import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Dimension.Vector.Vec3 
  ( Vec3(Vec3)
  , vec3
  , addVec3
  , subtractVec3
  , scaleVec3
  , negateVec3
  , dotVec3
  , distanceVec3
  , distanceSquaredVec3
  , vec3Zero
  , vec3UnitZ
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // type
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A ray defined by an origin point and a direction vector.
-- |
-- | Parametric form: P(t) = origin + t * direction
-- |
-- | For t ≥ 0, points are "in front" of the origin.
-- | For t < 0, points are "behind" the origin.
-- |
-- | The direction is NOT required to be normalized, matching Three.js behavior.
-- |
-- | Proof reference: Ray.lean Ray
data Ray = Ray (Vec3 Number) (Vec3 Number)
  -- origin direction

derive instance eqRay :: Eq Ray

instance showRay :: Show Ray where
  show (Ray origin direction) =
    "Ray(origin: " <> show origin <> ", direction: " <> show direction <> ")"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // constructors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create a ray from origin and direction
ray :: Vec3 Number -> Vec3 Number -> Ray
ray = Ray

-- | Default ray: origin at zero, pointing in positive Z direction
-- | Proof reference: Ray.lean default, default_origin, default_direction
rayDefault :: Ray
rayDefault = Ray vec3Zero vec3UnitZ

-- | Create ray from origin to target point
-- | Proof reference: Ray.lean fromPoints, fromPoints_origin, fromPoints_direction
rayFromPoints :: Vec3 Number -> Vec3 Number -> Ray
rayFromPoints origin target = Ray origin (subtractVec3 target origin)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // basic operations
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get point at parameter t along the ray: P(t) = origin + t * direction
-- | Proof reference: Ray.lean pointAt, pointAt_zero, pointAt_one, pointAt_add
pointAt :: Ray -> Number -> Vec3 Number
pointAt (Ray origin direction) t = addVec3 origin (scaleVec3 t direction)

-- | Point the ray at a target (sets direction toward target)
-- | Proof reference: Ray.lean lookAt, lookAt_origin, lookAt_pointAt_one
lookAtRay :: Ray -> Vec3 Number -> Ray
lookAtRay (Ray origin _) target = Ray origin (subtractVec3 target origin)

-- | Move origin along the ray by parameter t
-- | Proof reference: Ray.lean recast, recast_zero, recast_direction, recast_recast
recast :: Ray -> Number -> Ray
recast r t = Ray (pointAt r t) (getDirection r)

-- | Reverse the ray direction
-- | Proof reference: Ray.lean reverse, reverse_reverse, reverse_origin, reverse_direction
reverseRay :: Ray -> Ray
reverseRay (Ray origin direction) = Ray origin (negateVec3 direction)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                    // closest point operations
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Parameter t for the closest point on ray to a given point.
-- |
-- | Uses: t = ((point - origin) · direction) / (direction · direction)
-- |
-- | Note: t can be negative (point behind origin).
-- | For rays (vs lines), you may want to clamp t ≥ 0.
-- |
-- | Proof reference: Ray.lean closestPointParameter
closestPointParameter :: Ray -> Vec3 Number -> Number
closestPointParameter (Ray origin direction) point =
  let
    v = subtractVec3 point origin
    dirLenSq = dotVec3 direction direction
  in
    if dirLenSq == 0.0 then 0.0
    else dotVec3 v direction / dirLenSq

-- | Closest point on the infinite line containing the ray to a given point
-- | Proof reference: Ray.lean closestPointToPointOnLine
closestPointToPointOnLine :: Ray -> Vec3 Number -> Vec3 Number
closestPointToPointOnLine r point = pointAt r (closestPointParameter r point)

-- | Closest point on the ray (t ≥ 0) to a given point
-- | Proof reference: Ray.lean closestPointToPoint
closestPointToPoint :: Ray -> Vec3 Number -> Vec3 Number
closestPointToPoint r point =
  let t = closestPointParameter r point
  in pointAt r (max t 0.0)

-- | Distance from a point to the infinite line containing the ray
-- | Proof reference: Ray.lean distanceToPointOnLine
distanceToPointOnLine :: Ray -> Vec3 Number -> Number
distanceToPointOnLine r point = 
  distanceVec3 point (closestPointToPointOnLine r point)

-- | Squared distance from a point to the infinite line containing the ray
-- | Proof reference: Ray.lean distanceSqToPointOnLine
distanceSqToPointOnLine :: Ray -> Vec3 Number -> Number
distanceSqToPointOnLine r point = 
  distanceSquaredVec3 point (closestPointToPointOnLine r point)

-- | Distance from a point to the ray (t ≥ 0)
-- | Proof reference: Ray.lean distanceToPoint
distanceToPoint :: Ray -> Vec3 Number -> Number
distanceToPoint r point = 
  distanceVec3 point (closestPointToPoint r point)

-- | Squared distance from a point to the ray (t ≥ 0)
-- | Proof reference: Ray.lean distanceSqToPoint
distanceSqToPoint :: Ray -> Vec3 Number -> Number
distanceSqToPoint r point = 
  distanceSquaredVec3 point (closestPointToPoint r point)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get the ray origin
getOrigin :: Ray -> Vec3 Number
getOrigin (Ray origin _) = origin

-- | Get the ray direction
getDirection :: Ray -> Vec3 Number
getDirection (Ray _ direction) = direction
