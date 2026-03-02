-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                  // hydrogen // schema // motion // path-operations // insertion
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Insertion — Point insertion and subdivision operations.
-- |
-- | ## Design Philosophy
-- |
-- | Professional motion graphics requires precise control over path density:
-- |
-- | - **Add points**: Insert control points without changing curve shape
-- | - **Subdivide**: Add points for finer control
-- | - **Adaptive subdivision**: More points in high-curvature areas
-- |
-- | These operations mirror tools in:
-- | - professional vector graphics (Add Anchor Point)
-- | - Professional 3D (Spline subdivision)
-- | - Professional motion graphics (path operations)
-- |
-- | ## Dependencies
-- |
-- | - Schema.Geometry.Point (Point2D)
-- | - PathOperations.Internal (helpers)

module Hydrogen.Schema.Motion.PathOperations.Insertion
  ( -- * Point Insertion
    insertPoint
  , insertPointAtLength
  
  -- * Subdivision
  , subdivide
  , subdivideOnce
  , subdivideAdaptive
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (<=)
  , (==)
  , (&&)
  , otherwise
  )

import Data.Array (length, index, snoc, head, take, drop, concat, foldl)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Number (abs)
import Data.Int (toNumber) as Int

import Hydrogen.Schema.Geometry.Point (Point2D(Point2D), point2D)
import Hydrogen.Schema.Motion.PathOperations.Internal
  ( epsilon
  , buildArray
  , buildIntArray
  , clamp01
  , floorInt
  , mod
  , computeCurvatures
  , sumSegmentLengths
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // point insertion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Insert a point at parameter t (0-1) on the path.
-- |
-- | The point is interpolated between existing points.
insertPoint :: Number -> Array Point2D -> Array Point2D
insertPoint t pts =
  if length pts < 2 then pts
  else
    let
      n = length pts
      tScaled = clamp01 t * Int.toNumber (n - 1)
      insertIdx = floorInt tScaled + 1
      localT = tScaled - Int.toNumber (floorInt tScaled)
      
      newPoint = case { p1: index pts (insertIdx - 1), p2: index pts insertIdx } of
        { p1: Just (Point2D a), p2: Just (Point2D b) } ->
          point2D (a.x + localT * (b.x - a.x)) (a.y + localT * (b.y - a.y))
        _ -> fromMaybe (point2D 0.0 0.0) (head pts)
      
      before = take insertIdx pts
      after = drop insertIdx pts
    in
      concat [before, [newPoint], after]

-- | Insert point at specific arc length.
insertPointAtLength :: Number -> Array Point2D -> Array Point2D
insertPointAtLength targetLen pts =
  let totalLen = sumSegmentLengths pts
      t = if totalLen < epsilon then 0.0 else clamp01 (targetLen / totalLen)
  in insertPoint t pts

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // subdivision
-- ═════════════════════════════════════════════════════════════════════════════

-- | Subdivide path by inserting midpoints.
subdivide :: Int -> Array Point2D -> Array Point2D
subdivide iterations pts =
  if iterations <= 0 then pts
  else subdivide (iterations - 1) (subdivideOnce pts)

-- | Single subdivision pass.
subdivideOnce :: Array Point2D -> Array Point2D
subdivideOnce pts =
  let n = length pts
  in if n < 2 then pts
     else buildArray (n * 2 - 1) (\i ->
       if i `mod` 2 == 0 then
         index pts (i / 2)
       else
         case { p1: index pts (i / 2), p2: index pts (i / 2 + 1) } of
           { p1: Just (Point2D a), p2: Just (Point2D b) } ->
             Just (point2D ((a.x + b.x) / 2.0) ((a.y + b.y) / 2.0))
           _ -> Nothing
     )

-- | Adaptive subdivision based on curvature.
-- |
-- | Adds more points in high-curvature areas.
subdivideAdaptive :: Number -> Array Point2D -> Array Point2D
subdivideAdaptive threshold pts =
  if length pts < 3 then pts
  else
    let curvatures = computeCurvatures pts
    in foldl (\acc i ->
         case { p: index pts i, c: index curvatures i } of
           { p: Just pt, c: Just curv } ->
             if abs curv > threshold && i > 0 then
               -- Insert midpoint before this sharp corner
               case index pts (i - 1) of
                 Just (Point2D prev) ->
                   let (Point2D curr) = pt
                       mid = point2D ((prev.x + curr.x) / 2.0) ((prev.y + curr.y) / 2.0)
                   in snoc (snoc acc mid) pt
                 Nothing -> snoc acc pt
             else snoc acc pt
           _ -> acc
       ) [] (buildIntArray (length pts))
