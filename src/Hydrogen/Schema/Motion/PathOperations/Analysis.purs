-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                   // hydrogen // schema // motion // path-operations // analysis
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Analysis — Path analysis, filtering, utilities, and display operations.
-- |
-- | ## Design Philosophy
-- |
-- | Professional motion graphics requires comprehensive path analysis:
-- |
-- | - **Analysis**: Segment lengths, curvatures, sharp corners
-- | - **Utilities**: Close/open paths, split, join
-- | - **Filtering**: Remove points by distance or angle criteria
-- | - **Display**: Path visualization and debugging
-- |
-- | These operations provide the foundation for intelligent path manipulation.
-- |
-- | ## Dependencies
-- |
-- | - Schema.Geometry.Point (Point2D)
-- | - PathOperations.Internal (helpers)

module Hydrogen.Schema.Motion.PathOperations.Analysis
  ( -- * Analysis
    pathSegmentLengths
  , pathCurvatures
  , findSharpCorners
  , totalCurvature
  
  -- * Utilities
  , closePathLoop
  , openPath
  , splitAtPoint
  , joinPaths
  
  -- * Filtering
  , filterByDistance
  , filterByAngle
  , removeConsecutiveDuplicates
  
  -- * Display
  , showPath
  , showPathCompact
  
  -- * Pair Processing
  , pairAdjacentPoints
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , (+)
  , (-)
  , (*)
  , (<>)
  , (==)
  , (<)
  , (>)
  , (>=)
  , (||)
  )

import Data.Array (length, index, snoc, head, last, take, drop, concat, foldl, filter, cons, zipWith)
import Data.Maybe (Maybe(..))
import Data.Number (sqrt, abs)
import Data.Int (toNumber) as Int

import Hydrogen.Schema.Geometry.Point (Point2D(Point2D), point2D)
import Hydrogen.Schema.Motion.PathOperations.Internal
  ( epsilon
  , buildArray
  , buildIntArray
  , clamp01
  , floorInt
  , computeCurvatures
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // analysis
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get lengths of each path segment.
pathSegmentLengths :: Array Point2D -> Array Number
pathSegmentLengths pts =
  let n = length pts
  in buildArray (max 0 (n - 1)) (\i ->
       case { p1: index pts i, p2: index pts (i + 1) } of
         { p1: Just (Point2D a), p2: Just (Point2D b) } ->
           let dx = b.x - a.x
               dy = b.y - a.y
           in Just (sqrt (dx * dx + dy * dy))
         _ -> Nothing
     )
  where
    max :: Int -> Int -> Int
    max a b = if a > b then a else b

-- | Get curvature at each point.
pathCurvatures :: Array Point2D -> Array Number
pathCurvatures = computeCurvatures

-- | Find sharp corners (high curvature points).
-- |
-- | Returns indices of points where curvature exceeds threshold.
findSharpCorners :: Number -> Array Point2D -> Array Int
findSharpCorners threshold pts =
  let curvatures = computeCurvatures pts
  in foldl (\acc i ->
       case index curvatures i of
         Just c -> if abs c > threshold then snoc acc i else acc
         Nothing -> acc
     ) [] (buildIntArray (length curvatures))

-- | Total absolute curvature along path.
totalCurvature :: Array Point2D -> Number
totalCurvature pts =
  let curvatures = computeCurvatures pts
  in foldl (\acc c -> acc + abs c) 0.0 curvatures

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Close path by connecting last point to first.
closePathLoop :: Array Point2D -> Array Point2D
closePathLoop pts =
  case head pts of
    Nothing -> pts
    Just firstPt -> 
      case last pts of
        Nothing -> pts
        Just (Point2D lastP) ->
          let (Point2D firstP) = firstPt
              dx = firstP.x - lastP.x
              dy = firstP.y - lastP.y
              dist = sqrt (dx * dx + dy * dy)
          in if dist < epsilon then pts  -- Already closed
             else snoc pts firstPt

-- | Remove closing point if path is closed.
openPath :: Array Point2D -> Array Point2D
openPath pts =
  let n = length pts
  in if n < 2 then pts
     else case { first: head pts, lst: last pts } of
       { first: Just (Point2D f), lst: Just (Point2D l) } ->
         let dx = f.x - l.x
             dy = f.y - l.y
             dist = sqrt (dx * dx + dy * dy)
         in if dist < epsilon then take (n - 1) pts else pts
       _ -> pts

-- | Split path at parameter t.
splitAtPoint :: Number -> Array Point2D -> { before :: Array Point2D, after :: Array Point2D }
splitAtPoint t pts =
  let
    n = length pts
    tScaled = clamp01 t * Int.toNumber (n - 1)
    splitIdx = floorInt tScaled + 1
    localT = tScaled - Int.toNumber (floorInt tScaled)
    
    midPoint = case { p1: index pts (splitIdx - 1), p2: index pts splitIdx } of
      { p1: Just (Point2D a), p2: Just (Point2D b) } ->
        point2D (a.x + localT * (b.x - a.x)) (a.y + localT * (b.y - a.y))
      _ -> case head pts of
        Just pt -> pt
        Nothing -> point2D 0.0 0.0
  in
    { before: snoc (take splitIdx pts) midPoint
    , after: cons midPoint (drop splitIdx pts)
    }

-- | Join two paths end-to-end.
joinPaths :: Array Point2D -> Array Point2D -> Array Point2D
joinPaths a b = concat [a, b]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // filtering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Filter points by minimum distance from previous.
filterByDistance :: Number -> Array Point2D -> Array Point2D
filterByDistance minDist pts =
  foldl (\acc pt ->
    case last acc of
      Nothing -> snoc acc pt
      Just (Point2D prev) ->
        let (Point2D curr) = pt
            dx = curr.x - prev.x
            dy = curr.y - prev.y
            dist = sqrt (dx * dx + dy * dy)
        in if dist >= minDist then snoc acc pt else acc
  ) [] pts

-- | Filter out points where angle change is below threshold.
filterByAngle :: Number -> Array Point2D -> Array Point2D
filterByAngle minAngle pts =
  let 
    n = length pts
    curvatures = computeCurvatures pts
    -- Always keep first and last
    kept = filter (\i ->
      i == 0 || i == n - 1 || 
      case index curvatures i of
        Just c -> abs c >= minAngle
        Nothing -> alwaysTrue
    ) (buildIntArray n)
  in
    buildArray (length kept) (\i ->
      case index kept i of
        Just idx -> index pts idx
        Nothing -> Nothing
    )

-- | Constant true value.
alwaysTrue :: Boolean
alwaysTrue = 0 == 0

-- | Remove consecutive duplicate points.
removeConsecutiveDuplicates :: Array Point2D -> Array Point2D
removeConsecutiveDuplicates pts =
  foldl (\acc pt ->
    case last acc of
      Nothing -> snoc acc pt
      Just (Point2D prev) ->
        let (Point2D curr) = pt
            dx = curr.x - prev.x
            dy = curr.y - prev.y
            dist = sqrt (dx * dx + dy * dy)
        in if dist > epsilon then snoc acc pt else acc
  ) [] pts

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // display
-- ═════════════════════════════════════════════════════════════════════════════

-- | Show path as readable string.
showPath :: Array Point2D -> String
showPath pts =
  "Path [" <> showPointList pts <> "]"

-- | Show path in compact format.
showPathCompact :: Array Point2D -> String
showPathCompact pts =
  let n = length pts
  in "Path(" <> show n <> " points)"

-- | Show list of points.
showPointList :: Array Point2D -> String
showPointList pts =
  let n = length pts
  in if n == 0 then ""
     else foldl (\acc i ->
       case index pts i of
         Just (Point2D p) ->
           let separator = if acc == "" then "" else ", "
           in acc <> separator <> "(" <> show p.x <> "," <> show p.y <> ")"
         Nothing -> acc
     ) "" (buildIntArray n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // pair processing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pair up adjacent points with zipWith for edge processing.
pairAdjacentPoints :: Array Point2D -> Array { p1 :: Point2D, p2 :: Point2D }
pairAdjacentPoints pts =
  let pts2 = drop 1 pts
  in zipWith (\a b -> { p1: a, p2: b }) pts pts2
