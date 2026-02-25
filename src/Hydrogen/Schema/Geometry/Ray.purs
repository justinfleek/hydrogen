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
  
  -- * Intersection Tests
  , intersectSphereParameter
  , intersectPlaneParameter
  , intersectBoxParameter
  , intersectTriangleParameter
  
  -- * Accessors
  , getOrigin
  , getDirection
  ) where

import Prelude
  ( class Eq
  , class Show
  , max
  , min
  , negate
  , show
  , not
  , (||)
  , (&&)
  , (+)
  , (-)
  , (*)
  , (/)
  , (==)
  , (<)
  , (>)
  , (>=)
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Dimension.Vector.Vec3 
  ( Vec3
  , addVec3
  , subtractVec3
  , scaleVec3
  , negateVec3
  , dotVec3
  , crossVec3
  , distanceVec3
  , distanceSquaredVec3
  , getX3
  , getY3
  , getZ3
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
    "(Ray origin:" <> show origin <> " direction:" <> show direction <> ")"

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

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // intersection tests
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Intersect ray with a sphere, returning the parameter t at intersection.
-- |
-- | Returns Nothing if ray misses the sphere.
-- | Returns the nearest positive t (front-facing intersection).
-- |
-- | Algorithm: Solve quadratic |origin + t*dir - center|² = radius²
-- |   a = dir·dir, b = 2*(origin-center)·dir, c = |origin-center|² - r²
-- |   discriminant = b² - 4ac
-- |
-- | Three.js parity: Ray.intersectSphere
-- | Proof reference: Ray.lean intersectSphereParameter (pending)
intersectSphereParameter
  :: Ray
  -> Vec3 Number  -- center
  -> Number       -- radius
  -> Maybe Number
intersectSphereParameter (Ray origin direction) center radius =
  let
    oc = subtractVec3 origin center
    a = dotVec3 direction direction
    halfB = dotVec3 oc direction
    c = dotVec3 oc oc - radius * radius
    discriminant = halfB * halfB - a * c
  in
    if discriminant < 0.0 then Nothing
    else if a == 0.0 then Nothing  -- Degenerate ray (zero direction)
    else
      let
        sqrtD = Math.sqrt discriminant
        t1 = (negate halfB - sqrtD) / a
        t2 = (negate halfB + sqrtD) / a
      in
        -- Return nearest positive t
        if t1 >= 0.0 then Just t1
        else if t2 >= 0.0 then Just t2
        else Nothing

-- | Intersect ray with an infinite plane, returning the parameter t at intersection.
-- |
-- | Plane is defined by: normal · P = constant
-- | (i.e., all points P where dot(normal, P) = constant)
-- |
-- | Returns Nothing if ray is parallel to plane or intersection is behind origin.
-- |
-- | Algorithm: t = (constant - normal·origin) / (normal·direction)
-- |
-- | Three.js parity: Ray.intersectPlane
-- | Proof reference: Ray.lean intersectPlaneParameter (pending)
intersectPlaneParameter
  :: Ray
  -> Vec3 Number  -- planeNormal (should be normalized)
  -> Number       -- planeConstant
  -> Maybe Number
intersectPlaneParameter (Ray origin direction) planeNormal planeConstant =
  let
    denom = dotVec3 planeNormal direction
  in
    if Math.abs denom < epsilon then Nothing  -- Ray parallel to plane
    else
      let
        t = (planeConstant - dotVec3 planeNormal origin) / denom
      in
        if t < 0.0 then Nothing  -- Intersection behind ray origin
        else Just t
  where
    epsilon = 1.0e-10

-- | Intersect ray with an axis-aligned bounding box (AABB).
-- |
-- | Returns Nothing if ray misses the box.
-- | Returns the parameter t at the nearest intersection point.
-- |
-- | Algorithm: Slab method - compute entry/exit for each axis and find overlap.
-- |
-- | Three.js parity: Ray.intersectBox
-- | Proof reference: Ray.lean intersectBoxParameter (pending)
intersectBoxParameter
  :: Ray
  -> Vec3 Number  -- boxMin
  -> Vec3 Number  -- boxMax
  -> Maybe Number
intersectBoxParameter (Ray origin direction) boxMin boxMax =
  let
    -- Decompose into components
    ox = getX3 origin
    oy = getY3 origin
    oz = getZ3 origin
    dx = getX3 direction
    dy = getY3 direction
    dz = getZ3 direction
    minX = getX3 boxMin
    minY = getY3 boxMin
    minZ = getZ3 boxMin
    maxX = getX3 boxMax
    maxY = getY3 boxMax
    maxZ = getZ3 boxMax
    
    -- Compute t values for each slab
    -- Handle division by zero: if direction component is 0, check if origin is inside slab
    computeSlab :: Number -> Number -> Number -> Number -> { tMin :: Number, tMax :: Number }
    computeSlab o d lo hi =
      if Math.abs d < epsilon then
        -- Ray parallel to slab - check if origin is inside
        if o < lo || o > hi then
          { tMin: infinity, tMax: negInfinity }  -- No intersection possible
        else
          { tMin: negInfinity, tMax: infinity }  -- Always inside this slab
      else
        let
          invD = 1.0 / d
          t1 = (lo - o) * invD
          t2 = (hi - o) * invD
        in
          if invD < 0.0 then { tMin: t2, tMax: t1 }
          else { tMin: t1, tMax: t2 }
    
    slabX = computeSlab ox dx minX maxX
    slabY = computeSlab oy dy minY maxY
    slabZ = computeSlab oz dz minZ maxZ
    
    -- Intersection is the overlap of all three slabs
    tNear = max slabX.tMin (max slabY.tMin slabZ.tMin)
    tFar = min slabX.tMax (min slabY.tMax slabZ.tMax)
  in
    -- No intersection if tNear > tFar or tFar < 0
    if tNear > tFar || tFar < 0.0 then Nothing
    -- If tNear < 0, we're inside the box; return tFar (exit point) or 0
    else if tNear < 0.0 then Just 0.0
    else Just tNear
  where
    epsilon = 1.0e-10
    infinity = 1.0e30
    negInfinity = negate 1.0e30

-- | Intersect ray with a triangle using Möller–Trumbore algorithm.
-- |
-- | Returns Nothing if ray misses the triangle or (optionally) if backface.
-- | Returns the parameter t at the intersection point.
-- |
-- | Algorithm: Möller–Trumbore intersection
-- |   edge1 = v1 - v0, edge2 = v2 - v0
-- |   h = direction × edge2, a = edge1 · h
-- |   if |a| < ε, ray is parallel to triangle
-- |   f = 1/a, s = origin - v0, u = f * (s · h)
-- |   if u < 0 or u > 1, miss
-- |   q = s × edge1, v = f * (direction · q)
-- |   if v < 0 or u + v > 1, miss
-- |   t = f * (edge2 · q)
-- |
-- | Three.js parity: Ray.intersectTriangle
-- | Proof reference: Ray.lean intersectTriangleParameter (pending)
intersectTriangleParameter
  :: Ray
  -> Vec3 Number  -- v0 (vertex A)
  -> Vec3 Number  -- v1 (vertex B)
  -> Vec3 Number  -- v2 (vertex C)
  -> Boolean      -- backfaceCulling: if true, ignore back-facing triangles
  -> Maybe Number
intersectTriangleParameter (Ray origin direction) v0 v1 v2 backfaceCulling =
  let
    edge1 = subtractVec3 v1 v0
    edge2 = subtractVec3 v2 v0
    h = crossVec3 direction edge2
    a = dotVec3 edge1 h
  in
    -- Check if ray is parallel to triangle (or backface culling)
    if backfaceCulling && a < epsilon then Nothing  -- Backface (or parallel)
    else if not backfaceCulling && Math.abs a < epsilon then Nothing  -- Parallel
    else
      let
        f = 1.0 / a
        s = subtractVec3 origin v0
        u = f * dotVec3 s h
      in
        if u < 0.0 || u > 1.0 then Nothing
        else
          let
            q = crossVec3 s edge1
            v = f * dotVec3 direction q
          in
            if v < 0.0 || u + v > 1.0 then Nothing
            else
              let
                t = f * dotVec3 edge2 q
              in
                if t < epsilon then Nothing  -- Intersection behind ray
                else Just t
  where
    epsilon = 1.0e-10
