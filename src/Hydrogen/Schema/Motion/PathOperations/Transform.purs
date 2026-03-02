-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                  // hydrogen // schema // motion // path-operations // transform
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Transform — Path transformation operations.
-- |
-- | ## Design Philosophy
-- |
-- | Professional motion graphics requires precise control over path shape:
-- |
-- | - **Spacing**: Equalize or resample point distribution
-- | - **Smoothing**: Reduce sharp corners while maintaining shape
-- | - **Direction**: Reverse path direction
-- | - **Offset**: Create parallel paths
-- |
-- | These operations mirror tools in:
-- | - professional vector graphics (Smooth Tool, Simplify)
-- | - Professional 3D (Spline tools, Resample, Smooth)
-- | - Professional motion graphics (path operations)
-- |
-- | ## Dependencies
-- |
-- | - Schema.Geometry.Point (Point2D)
-- | - Schema.Geometry.Vector (Vector2D)
-- | - PathOperations.Internal (helpers)

module Hydrogen.Schema.Motion.PathOperations.Transform
  ( -- * Spacing
    equalizeSpacing
  , resample
  , resampleByLength
  
  -- * Smoothing
  , smooth
  , chaikinSmooth
  , smoothLaplacian
  , laplacianPass
  , simplify
  , simplifyRDP
  
  -- * Direction
  , reversePath
  , flipPath
  
  -- * Offset
  , offsetPath
  , outlinePath
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
  , (>=)
  , (==)
  , (||)
  , otherwise
  , negate
  , max
  , map
  )

import Data.Array (length, index, snoc, reverse, head, last, take, concat, foldl)
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Data.Number (sqrt, abs)
import Data.Int (toNumber) as Int

import Hydrogen.Schema.Geometry.Point (Point2D(Point2D), point2D)
import Hydrogen.Schema.Geometry.Vector (getVX, getVY)
import Hydrogen.Schema.Motion.PathOperations.Internal
  ( epsilon
  , buildArray
  , buildIntArray
  , buildIntRange
  , clamp01
  , floorInt
  , pointToLineDistance
  , sumSegmentLengths
  , pointAtArcLength
  , computeNormalAt
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // spacing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Equalize spacing between points (C4D Resample).
-- |
-- | Creates n evenly-spaced points along the path.
equalizeSpacing :: Int -> Array Point2D -> Array Point2D
equalizeSpacing n pts =
  if n < 2 || length pts < 2 then pts
  else
    let
      totalLen = sumSegmentLengths pts
      segmentLen = totalLen / Int.toNumber (n - 1)
    in
      buildArray n (\i ->
        let targetLen = Int.toNumber i * segmentLen
        in Just (pointAtArcLength targetLen pts)
      )

-- | Resample path to have n points.
resample :: Int -> Array Point2D -> Array Point2D
resample = equalizeSpacing

-- | Resample with target segment length.
resampleByLength :: Number -> Array Point2D -> Array Point2D
resampleByLength segLen pts =
  let 
    totalLen = sumSegmentLengths pts
    numSegs = max 1 (floorInt (totalLen / segLen))
  in equalizeSpacing (numSegs + 1) pts

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // smoothing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Smooth path with Chaikin's algorithm.
-- |
-- | Each iteration doubles points and moves them toward smoother positions.
-- | - iterations: number of smoothing passes
-- | - factor: 0-1, how much to smooth (0.25 = classic Chaikin)
smooth :: Int -> Number -> Array Point2D -> Array Point2D
smooth iterations factor pts =
  if iterations <= 0 || length pts < 3 then pts
  else smooth (iterations - 1) factor (chaikinSmooth factor pts)

-- | Single Chaikin smoothing pass.
chaikinSmooth :: Number -> Array Point2D -> Array Point2D
chaikinSmooth factor pts =
  let 
    n = length pts
    f = clamp01 factor
    mf = 1.0 - f
  in
    if n < 2 then pts
    else
      let 
        -- Keep first point
        result = fromMaybe [] (map (\p -> [p]) (head pts))
        
        -- Add smoothed interior points
        interior = foldl (\acc i ->
          case { p1: index pts i, p2: index pts (i + 1) } of
            { p1: Just (Point2D a), p2: Just (Point2D b) } ->
              let 
                q = point2D (mf * a.x + f * b.x) (mf * a.y + f * b.y)
                r = point2D (f * a.x + mf * b.x) (f * a.y + mf * b.y)
              in snoc (snoc acc q) r
            _ -> acc
        ) [] (buildIntArray (n - 1))
        
        -- Keep last point
        lastPt = fromMaybe [] (map (\p -> [p]) (last pts))
      in
        concat [result, interior, lastPt]

-- | Laplacian smoothing (moves points toward neighbor average).
smoothLaplacian :: Int -> Number -> Array Point2D -> Array Point2D
smoothLaplacian iterations strength pts =
  if iterations <= 0 || length pts < 3 then pts
  else smoothLaplacian (iterations - 1) strength (laplacianPass strength pts)

-- | Single Laplacian smoothing pass.
laplacianPass :: Number -> Array Point2D -> Array Point2D
laplacianPass strength pts =
  let n = length pts
  in buildArray n (\i ->
       if i == 0 || i == n - 1 then
         -- Keep endpoints fixed
         index pts i
       else
         case { prev: index pts (i - 1), curr: index pts i, next: index pts (i + 1) } of
           { prev: Just (Point2D p), curr: Just (Point2D c), next: Just (Point2D nx) } ->
             let
               avgX = (p.x + nx.x) / 2.0
               avgY = (p.y + nx.y) / 2.0
               newX = c.x + strength * (avgX - c.x)
               newY = c.y + strength * (avgY - c.y)
             in Just (point2D newX newY)
           _ -> index pts i
     )

-- | Simplify path by removing redundant points.
-- |
-- | Uses distance threshold to determine which points to keep.
simplify :: Number -> Array Point2D -> Array Point2D
simplify tolerance pts =
  if length pts < 3 then pts
  else
    foldl (\acc i ->
      case { curr: index pts i, prev: last acc } of
        { curr: Just (Point2D c), prev: Just (Point2D p) } ->
          let 
            dx = c.x - p.x
            dy = c.y - p.y
            dist = sqrt (dx * dx + dy * dy)
          in if dist >= tolerance then snoc acc (point2D c.x c.y) else acc
        { curr: Just pt, prev: Nothing } -> snoc acc pt
        _ -> acc
    ) [] (buildIntArray (length pts))

-- | Ramer-Douglas-Peucker simplification.
-- |
-- | Removes points that deviate less than tolerance from the line
-- | between kept points. Preserves overall shape better than simple
-- | distance thresholding.
simplifyRDP :: Number -> Array Point2D -> Array Point2D
simplifyRDP tolerance pts =
  let n = length pts
  in if n < 3 then pts
     else rdpRecursive tolerance pts 0 (n - 1)

-- | Recursive RDP implementation.
rdpRecursive :: Number -> Array Point2D -> Int -> Int -> Array Point2D
rdpRecursive tolerance pts startIdx endIdx =
  if endIdx <= startIdx + 1 then
    case { s: index pts startIdx, e: index pts endIdx } of
      { s: Just sp, e: Just ep } -> [sp, ep]
      { s: Just sp, e: Nothing } -> [sp]
      _ -> []
  else
    let
      -- Find point with maximum distance from line
      maxResult = findMaxDistance pts startIdx endIdx
      maxDist = maxResult.distance
      maxIdx = maxResult.index
    in
      if maxDist > tolerance then
        -- Recursively simplify both halves
        let 
          left = rdpRecursive tolerance pts startIdx maxIdx
          right = rdpRecursive tolerance pts maxIdx endIdx
        in 
          -- Remove duplicate point at split
          concat [take (length left - 1) left, right]
      else
        -- Just keep endpoints
        case { s: index pts startIdx, e: index pts endIdx } of
          { s: Just sp, e: Just ep } -> [sp, ep]
          _ -> []

-- | Find point with maximum distance from line.
findMaxDistance :: Array Point2D -> Int -> Int -> { distance :: Number, index :: Int }
findMaxDistance pts startIdx endIdx =
  case { s: index pts startIdx, e: index pts endIdx } of
    { s: Just (Point2D start), e: Just (Point2D end) } ->
      foldl (\acc i ->
        case index pts i of
          Just (Point2D p) ->
            let dist = pointToLineDistance p.x p.y start.x start.y end.x end.y
            in if dist > acc.distance then { distance: dist, index: i } else acc
          Nothing -> acc
      ) { distance: 0.0, index: startIdx } (buildIntRange (startIdx + 1) (endIdx - 1))
    _ -> { distance: 0.0, index: startIdx }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // direction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Reverse path direction.
reversePath :: Array Point2D -> Array Point2D
reversePath = reverse

-- | Flip path (same as reverse).
flipPath :: Array Point2D -> Array Point2D
flipPath = reverse

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // offset
-- ═════════════════════════════════════════════════════════════════════════════

-- | Offset path perpendicular to direction.
-- |
-- | Positive distance = left side, negative = right side.
offsetPath :: Number -> Array Point2D -> Array Point2D
offsetPath distance pts =
  let n = length pts
  in buildArray n (\i ->
       case index pts i of
         Nothing -> Nothing
         Just (Point2D p) ->
           let 
             normal = computeNormalAt i pts
             (Point2D offset) = point2D (getVX normal * distance) (getVY normal * distance)
           in Just (point2D (p.x + offset.x) (p.y + offset.y))
     )

-- | Create outline (offset both sides and connect).
outlinePath :: Number -> Array Point2D -> Array Point2D
outlinePath width pts =
  let
    halfWidth = width / 2.0
    left = offsetPath halfWidth pts
    right = offsetPath (negate halfWidth) pts
  in
    concat [left, reverse right]
