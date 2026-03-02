-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                    // hydrogen // schema // physics // collision // detection
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Detection — Collision detection algorithms.
-- |
-- | ## Design Philosophy
-- |
-- | Narrow-phase collision detection algorithms for determining exact
-- | contact information between pairs of bounding volumes.
-- |
-- | ## Detection Pairs
-- |
-- | - AABB vs AABB, Point, Circle
-- | - Circle vs Circle, Point, AABB
-- | - Capsule vs Point, Capsule
-- |
-- | ## Dependencies
-- |
-- | - Collision.Point (Point2D)
-- | - Collision.Volumes (AABB, BoundingCircle, BoundingCapsule)
-- | - Collision.Contact (Contact)
-- | - Collision.Internal (minNum, maxNum)

module Hydrogen.Schema.Physics.Collision.Detection
  ( -- * AABB Detection
    aabbVsAABB
  , aabbVsPoint
  , aabbVsCircle
  
  -- * Circle Detection
  , circleVsCircle
  , circleVsPoint
  , circleVsAABB
  
  -- * Capsule Detection
  , capsuleVsPoint
  , capsuleVsCapsule
  
  -- * Segment Distance
  , segmentSegmentDistance
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( negate
  , (&&)
  , (*)
  , (+)
  , (-)
  , (/)
  , (<)
  , (<=)
  , (>=)
  , (||)
  )

import Hydrogen.Schema.Physics.Collision.Point
  ( Point2D(Point2D)
  , point2D
  , distance
  , midpoint
  )

import Hydrogen.Schema.Physics.Collision.Volumes
  ( AABB(AABB)
  , BoundingCircle(BoundingCircle)
  , BoundingCapsule(BoundingCapsule)
  , aabbContains
  , pointToSegmentDistance
  )

import Hydrogen.Schema.Physics.Collision.Contact
  ( Contact(NoContact, Contact)
  , flipContact
  )

import Hydrogen.Schema.Physics.Collision.Internal
  ( minNum
  , maxNum
  , clampNum
  , clampUnit
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // aabb detection
-- ═════════════════════════════════════════════════════════════════════════════

-- | AABB vs AABB collision test
aabbVsAABB :: AABB -> AABB -> Contact
aabbVsAABB (AABB a) (AABB b) =
  -- Check for separation on each axis
  if a.maxX < b.minX || b.maxX < a.minX ||
     a.maxY < b.minY || b.maxY < a.minY
  then NoContact
  else
    let
      -- Calculate overlap on each axis
      overlapX = minNum (a.maxX - b.minX) (b.maxX - a.minX)
      overlapY = minNum (a.maxY - b.minY) (b.maxY - a.minY)
      -- Minimum overlap axis is the contact normal
      centerAX = (a.minX + a.maxX) / 2.0
      centerAY = (a.minY + a.maxY) / 2.0
      centerBX = (b.minX + b.maxX) / 2.0
      centerBY = (b.minY + b.maxY) / 2.0
    in if overlapX < overlapY
       then
         let normalX = if centerBX >= centerAX then 1.0 else -1.0
             contactX = if normalX >= 0.0 then a.maxX else a.minX
             contactY = (maxNum a.minY b.minY + minNum a.maxY b.maxY) / 2.0
         in Contact
              { point: point2D contactX contactY
              , normal: point2D normalX 0.0
              , depth: overlapX
              }
       else
         let normalY = if centerBY >= centerAY then 1.0 else -1.0
             contactY = if normalY >= 0.0 then a.maxY else a.minY
             contactX = (maxNum a.minX b.minX + minNum a.maxX b.maxX) / 2.0
         in Contact
              { point: point2D contactX contactY
              , normal: point2D 0.0 normalY
              , depth: overlapY
              }

-- | AABB vs Point collision test
aabbVsPoint :: AABB -> Point2D -> Contact
aabbVsPoint box point =
  if aabbContains box point
  then
    let 
      AABB b = box
      Point2D p = point
      -- Distance to each edge
      distLeft = p.x - b.minX
      distRight = b.maxX - p.x
      distTop = p.y - b.minY
      distBottom = b.maxY - p.y
      -- Find minimum distance (closest edge)
      minDist = minNum (minNum distLeft distRight) (minNum distTop distBottom)
    in if minDist <= distLeft && distLeft <= distRight
       then Contact { point, normal: point2D (-1.0) 0.0, depth: distLeft }
       else if minDist <= distRight
       then Contact { point, normal: point2D 1.0 0.0, depth: distRight }
       else if minDist <= distTop
       then Contact { point, normal: point2D 0.0 (-1.0), depth: distTop }
       else Contact { point, normal: point2D 0.0 1.0, depth: distBottom }
  else NoContact

-- | AABB vs Circle collision test
aabbVsCircle :: AABB -> BoundingCircle -> Contact
aabbVsCircle (AABB box) (BoundingCircle circle) =
  let
    Point2D c = circle.center
    -- Find closest point on AABB to circle center
    closestX = clampNum box.minX box.maxX c.x
    closestY = clampNum box.minY box.maxY c.y
    closest = point2D closestX closestY
    -- Distance from circle center to closest point
    dist = distance circle.center closest
  in if dist < circle.radius
     then
       let 
         depth = circle.radius - dist
         normal = if dist < 0.0001
                  then point2D 1.0 0.0  -- Circle center inside AABB
                  else point2D ((c.x - closestX) / dist) ((c.y - closestY) / dist)
       in Contact { point: closest, normal, depth }
     else NoContact

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // circle detection
-- ═════════════════════════════════════════════════════════════════════════════

-- | Circle vs Circle collision test
circleVsCircle :: BoundingCircle -> BoundingCircle -> Contact
circleVsCircle (BoundingCircle a) (BoundingCircle b) =
  let
    dist = distance a.center b.center
    radiusSum = a.radius + b.radius
  in if dist < radiusSum
     then
       let
         Point2D ac = a.center
         Point2D bc = b.center
         depth = radiusSum - dist
         normal = if dist < 0.0001
                  then point2D 1.0 0.0  -- Coincident centers
                  else point2D ((bc.x - ac.x) / dist) ((bc.y - ac.y) / dist)
         -- Contact point is on surface of first circle
         Point2D n = normal
         contactPt = point2D (ac.x + n.x * a.radius) (ac.y + n.y * a.radius)
       in Contact { point: contactPt, normal, depth }
     else NoContact

-- | Circle vs Point collision test
circleVsPoint :: BoundingCircle -> Point2D -> Contact
circleVsPoint (BoundingCircle c) point =
  let dist = distance c.center point
  in if dist < c.radius
     then
       let
         Point2D cc = c.center
         Point2D p = point
         depth = c.radius - dist
         normal = if dist < 0.0001
                  then point2D 1.0 0.0
                  else point2D ((p.x - cc.x) / dist) ((p.y - cc.y) / dist)
       in Contact { point, normal, depth }
     else NoContact

-- | Circle vs AABB (flipped aabbVsCircle)
circleVsAABB :: BoundingCircle -> AABB -> Contact
circleVsAABB circle box = flipContact (aabbVsCircle box circle)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // capsule detection
-- ═════════════════════════════════════════════════════════════════════════════

-- | Capsule vs Point collision test
capsuleVsPoint :: BoundingCapsule -> Point2D -> Contact
capsuleVsPoint (BoundingCapsule cap) point =
  let dist = pointToSegmentDistance point cap.pointA cap.pointB
  in if dist < cap.radius
     then
       -- Find closest point on segment for normal calculation
       let
         Point2D p = point
         Point2D a = cap.pointA
         Point2D b = cap.pointB
         abx = b.x - a.x
         aby = b.y - a.y
         apx = p.x - a.x
         apy = p.y - a.y
         abSquared = abx * abx + aby * aby
         t = if abSquared < 0.0001 
             then 0.0 
             else clampUnit 1.0 ((apx * abx + apy * aby) / abSquared)
         closestX = a.x + t * abx
         closestY = a.y + t * aby
         dx = p.x - closestX
         dy = p.y - closestY
         depth = cap.radius - dist
         normal = if dist < 0.0001
                  then point2D 1.0 0.0
                  else point2D (dx / dist) (dy / dist)
       in Contact { point, normal, depth }
     else NoContact

-- | Capsule vs Capsule collision test
capsuleVsCapsule :: BoundingCapsule -> BoundingCapsule -> Contact
capsuleVsCapsule (BoundingCapsule a) (BoundingCapsule b) =
  let
    -- Find closest points between the two line segments
    dist = segmentSegmentDistance a.pointA a.pointB b.pointA b.pointB
    radiusSum = a.radius + b.radius
  in if dist < radiusSum
     then
       -- Simplified: use midpoints for contact point
       let
         midA = midpoint a.pointA a.pointB
         midB = midpoint b.pointA b.pointB
         d = distance midA midB
         Point2D ma = midA
         Point2D mb = midB
         depth = radiusSum - dist
         normal = if d < 0.0001
                  then point2D 1.0 0.0
                  else point2D ((mb.x - ma.x) / d) ((mb.y - ma.y) / d)
         Point2D n = normal
         contactPt = point2D (ma.x + n.x * a.radius) (ma.y + n.y * a.radius)
       in Contact { point: contactPt, normal, depth }
     else NoContact

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // segment distance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Distance between two line segments.
-- |
-- | Calculates minimum distance by checking all four point-to-segment
-- | combinations and taking the minimum.
segmentSegmentDistance :: Point2D -> Point2D -> Point2D -> Point2D -> Number
segmentSegmentDistance a1 a2 b1 b2 =
  -- Check all four point-to-segment distances and take minimum
  let
    d1 = pointToSegmentDistance a1 b1 b2
    d2 = pointToSegmentDistance a2 b1 b2
    d3 = pointToSegmentDistance b1 a1 a2
    d4 = pointToSegmentDistance b2 a1 a2
  in minNum (minNum d1 d2) (minNum d3 d4)
