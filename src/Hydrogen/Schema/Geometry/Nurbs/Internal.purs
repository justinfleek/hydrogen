-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // nurbs // internal
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Internal helper functions for NURBS computation.
-- |
-- | This module contains low-level algorithms used by other NURBS modules:
-- | - De Boor's algorithm for curve evaluation
-- | - Knot span finding
-- | - Oslo algorithm for knot insertion
-- | - Array building utilities
-- | - Homogeneous coordinate conversion
-- |
-- | ## Note
-- |
-- | These functions are exported for use by sibling NURBS modules.
-- | End users should prefer the high-level API in the main Nurbs module.
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Geometry.Point (Point2D)
-- | - Hydrogen.Schema.Geometry.Nurbs.Types (ControlPoint, KnotVector)

module Hydrogen.Schema.Geometry.Nurbs.Internal
  ( -- * Constants
    epsilon
  , origin
  
  -- * Numeric Utilities
  , clampNumber
  , absNum
  , toNumber
  
  -- * Array Utilities
  , buildArray
  , buildIntArray
  , insertIntoSortedArray
  
  -- * Knot Operations
  , nurbsParamRange
  , findKnotSpan
  , isNonDecreasing
  , uniformKnotVector
  
  -- * Control Point Utilities
  , allWeightsPositive
  
  -- * Homogeneous Coordinates
  , toHomogeneous
  , fromHomogeneous
  
  -- * De Boor Algorithm
  , deBoorRational
  
  -- * Oslo Algorithm
  , osloInsert
  
  -- * Bounding Box
  , initialBounds
  , updateBounds
  , mergeBounds
  
  -- * Arc Construction
  , buildArcControlPoints
  , buildArcKnots
  
  -- * Distance Computation
  , sumDistances
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
  , (&&)
  , otherwise
  , negate
  , min
  , max
  , map
  )

import Data.Array (length, index, snoc, foldl, take, drop)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Number (sqrt, cos, sin)
import Data.Int (toNumber) as Int

import Hydrogen.Schema.Geometry.Point (Point2D(Point2D), point2D)
import Hydrogen.Schema.Geometry.Nurbs.Types (ControlPoint(ControlPoint), KnotVector)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Small epsilon for floating point comparisons.
epsilon :: Number
epsilon = 1.0e-10

-- | Origin point (0, 0).
origin :: Point2D
origin = point2D 0.0 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // numeric utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp value to range [lo, hi].
-- | Named clampNumber to avoid shadowing Prelude.clamp
clampNumber :: Number -> Number -> Number -> Number
clampNumber lo hi v
  | v < lo = lo
  | v > hi = hi
  | otherwise = v

-- | Absolute value of a Number.
absNum :: Number -> Number
absNum n = if n < 0.0 then negate n else n

-- | Convert Int to Number.
toNumber :: Int -> Number
toNumber = Int.toNumber

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // array utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Build array from function.
-- |
-- | Calls f(0), f(1), ..., f(n-1) and collects Just values.
buildArray :: forall a. Int -> (Int -> Maybe a) -> Array a
buildArray n f = buildArrayImpl 0 n f []

buildArrayImpl :: forall a. Int -> Int -> (Int -> Maybe a) -> Array a -> Array a
buildArrayImpl i n f acc =
  if i >= n then acc
  else case f i of
    Nothing -> buildArrayImpl (i + 1) n f acc
    Just x -> buildArrayImpl (i + 1) n f (snoc acc x)

-- | Build integer array [0, 1, ..., n-1].
buildIntArray :: Int -> Array Int
buildIntArray n = buildArray n Just

-- | Insert value into sorted array, maintaining sort order.
insertIntoSortedArray :: Number -> Array Number -> Array Number
insertIntoSortedArray v arr =
  let
    n = length arr
    insertIdx = findInsertIndex v arr 0 n
    before = take insertIdx arr
    after = drop insertIdx arr
  in
    appendArrays (appendArrays before [v]) after

findInsertIndex :: Number -> Array Number -> Int -> Int -> Int
findInsertIndex v arr i n =
  if i >= n then n
  else case index arr i of
    Nothing -> i
    Just x -> if v <= x then i else findInsertIndex v arr (i + 1) n

-- | Append two arrays.
appendArrays :: forall a. Array a -> Array a -> Array a
appendArrays a b = foldl snoc a b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // knot operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get parameter range from knots and degree.
-- |
-- | For clamped NURBS, returns [knots[degree], knots[n-degree-1]].
nurbsParamRange :: KnotVector -> Int -> { start :: Number, end :: Number }
nurbsParamRange knots degree =
  let
    n = length knots
  in
    { start: fromMaybe 0.0 (index knots degree)
    , end: fromMaybe 1.0 (index knots (n - degree - 1))
    }

-- | Find the knot span index for parameter u.
-- |
-- | Returns i such that knots[i] ≤ u < knots[i+1].
findKnotSpan :: Number -> KnotVector -> Int -> Int
findKnotSpan u knots degree =
  let
    n = length knots - degree - 2
    range = nurbsParamRange knots degree
  in
    if u >= range.end then n
    else if u <= range.start then degree
    else findSpanBinary u knots degree n

-- | Binary search for knot span.
findSpanBinary :: Number -> KnotVector -> Int -> Int -> Int
findSpanBinary u knots low high =
  if high - low <= 1 then low
  else
    let mid = (low + high) / 2
    in case index knots mid of
      Nothing -> low
      Just kMid ->
        if u < kMid then findSpanBinary u knots low mid
        else findSpanBinary u knots mid high

-- | Check if array is non-decreasing.
isNonDecreasing :: Array Number -> Boolean
isNonDecreasing arr =
  let n = length arr
  in foldl (\acc i ->
       case { a: index arr i, b: index arr (i + 1) } of
         { a: Just va, b: Just vb } -> acc && va <= vb
         _ -> acc
     ) true (buildIntArray (n - 1))

-- | Create uniform clamped knot vector.
-- |
-- | For n control points and given degree, creates knot vector
-- | with clamped ends and uniform internal spacing.
uniformKnotVector :: Int -> Int -> KnotVector
uniformKnotVector n degree =
  let
    numKnots = n + degree + 1
    numInternalKnots = numKnots - 2 * (degree + 1)
  in
    buildArray numKnots (\i ->
      if i <= degree then Just 0.0
      else if i >= numKnots - degree - 1 then Just 1.0
      else Just (toNumber (i - degree) / toNumber (numInternalKnots + 1))
    )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // control point utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check all control point weights are positive.
allWeightsPositive :: Array ControlPoint -> Boolean
allWeightsPositive cps = foldl (\acc (ControlPoint cp) -> acc && cp.weight > 0.0) true cps

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // homogeneous coordinates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert control point to homogeneous coordinates (x*w, y*w, w).
toHomogeneous :: ControlPoint -> { x :: Number, y :: Number, w :: Number }
toHomogeneous (ControlPoint cp) =
  let (Point2D p) = cp.position
  in { x: p.x * cp.weight, y: p.y * cp.weight, w: cp.weight }

-- | Convert homogeneous coordinates back to Point2D.
fromHomogeneous :: { x :: Number, y :: Number, w :: Number } -> Point2D
fromHomogeneous h =
  if h.w < epsilon then origin
  else point2D (h.x / h.w) (h.y / h.w)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // de boor algorithm
-- ═════════════════════════════════════════════════════════════════════════════

-- | De Boor's algorithm for rational NURBS evaluation.
-- |
-- | Evaluates the NURBS curve at parameter u using the de Boor recursion
-- | with rational (weighted) control points.
deBoorRational :: Number -> Int -> Int -> Array ControlPoint -> KnotVector -> Point2D
deBoorRational u span degree cps knots =
  let
    -- Extract relevant control points (p+1 points starting at span-degree)
    startIdx = span - degree
    relevantCps = take (degree + 1) (drop startIdx cps)
    
    -- Convert to homogeneous coordinates (x*w, y*w, w)
    homogeneous = map toHomogeneous relevantCps
    
    -- Apply de Boor recursively
    result = deBoorRecursive u span degree degree homogeneous knots
  in
    case index result 0 of
      Nothing -> origin
      Just h -> fromHomogeneous h

-- | Recursive de Boor evaluation.
deBoorRecursive 
  :: Number 
  -> Int 
  -> Int 
  -> Int 
  -> Array { x :: Number, y :: Number, w :: Number } 
  -> KnotVector 
  -> Array { x :: Number, y :: Number, w :: Number }
deBoorRecursive u span degree r pts knots =
  if r <= 0 then pts
  else
    let
      newPts = buildArray (length pts - 1) (\j ->
        let
          i = span - degree + 1 + j
          knotI = fromMaybe 0.0 (index knots i)
          knotIPR = fromMaybe 1.0 (index knots (i + degree + 1 - r))
          denom = knotIPR - knotI
          alpha = if denom < epsilon then 0.0 else (u - knotI) / denom
        in
          case { p0: index pts j, p1: index pts (j + 1) } of
            { p0: Just pt0, p1: Just pt1 } ->
              Just { x: (1.0 - alpha) * pt0.x + alpha * pt1.x
                   , y: (1.0 - alpha) * pt0.y + alpha * pt1.y
                   , w: (1.0 - alpha) * pt0.w + alpha * pt1.w
                   }
            _ -> Nothing
      )
    in
      deBoorRecursive u span degree (r - 1) newPts knots

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // oslo algorithm
-- ═════════════════════════════════════════════════════════════════════════════

-- | Oslo algorithm for knot insertion.
-- |
-- | Computes new control points when inserting knot u at span k.
osloInsert :: Number -> Int -> Int -> Array ControlPoint -> KnotVector -> Array ControlPoint
osloInsert u k degree cps knots =
  let
    n = length cps
  in
    buildArray (n + 1) (\i ->
      if i <= k - degree then index cps i
      else if i >= k + 1 then index cps (i - 1)
      else
        let
          knotI = fromMaybe 0.0 (index knots i)
          knotIPD = fromMaybe 1.0 (index knots (i + degree))
          denom = knotIPD - knotI
          alpha = if denom < epsilon then 0.0 else (u - knotI) / denom
        in
          case { p0: index cps (i - 1), p1: index cps i } of
            { p0: Just (ControlPoint cp0), p1: Just (ControlPoint cp1) } ->
              let
                (Point2D pos0) = cp0.position
                (Point2D pos1) = cp1.position
                newX = (1.0 - alpha) * pos0.x + alpha * pos1.x
                newY = (1.0 - alpha) * pos0.y + alpha * pos1.y
                newW = (1.0 - alpha) * cp0.weight + alpha * cp1.weight
              in Just (ControlPoint { position: point2D newX newY, weight: newW })
            _ -> index cps i
    )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // bounding box
-- ═════════════════════════════════════════════════════════════════════════════

-- | Initial bounding box (inverted, ready for point accumulation).
initialBounds :: { minX :: Number, minY :: Number, maxX :: Number, maxY :: Number }
initialBounds = 
  { minX: 1.0e308
  , minY: 1.0e308
  , maxX: negate 1.0e308
  , maxY: negate 1.0e308
  }

-- | Update bounding box with a point.
updateBounds 
  :: { minX :: Number, minY :: Number, maxX :: Number, maxY :: Number } 
  -> Point2D 
  -> { minX :: Number, minY :: Number, maxX :: Number, maxY :: Number }
updateBounds bounds (Point2D p) =
  { minX: min bounds.minX p.x
  , minY: min bounds.minY p.y
  , maxX: max bounds.maxX p.x
  , maxY: max bounds.maxY p.y
  }

-- | Merge two bounding boxes.
mergeBounds 
  :: { minX :: Number, minY :: Number, maxX :: Number, maxY :: Number }
  -> { minX :: Number, minY :: Number, maxX :: Number, maxY :: Number }
  -> { minX :: Number, minY :: Number, maxX :: Number, maxY :: Number }
mergeBounds a b =
  { minX: min a.minX b.minX
  , minY: min a.minY b.minY
  , maxX: max a.maxX b.maxX
  , maxY: max a.maxY b.maxY
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // arc construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Build arc control points recursively.
-- |
-- | Creates control points for a NURBS arc with given parameters.
buildArcControlPoints :: Number -> Number -> Int -> Number -> Number -> Array ControlPoint -> Array ControlPoint
buildArcControlPoints radius startAngle numSegs segAngle w acc =
  if numSegs <= 0 then acc
  else
    let
      -- Start point of this segment
      angle0 = startAngle + toNumber (length acc / 2) * segAngle
      angle1 = angle0 + segAngle
      midAngle = (angle0 + angle1) / 2.0
      
      -- Control point at middle (off-curve, weighted)
      cpAngle = midAngle
      -- The control point is at radius/cos(halfAngle) distance
      cpRadius = radius / cos (segAngle / 2.0)
      
      p0 = ControlPoint { position: point2D (radius * cos angle0) (radius * sin angle0), weight: 1.0 }
      pMid = ControlPoint { position: point2D (cpRadius * cos cpAngle) (cpRadius * sin cpAngle), weight: w }
      
      newAcc = if length acc == 0 
               then [p0, pMid]
               else snoc acc pMid
    in
      if numSegs == 1 then
        snoc newAcc (ControlPoint { position: point2D (radius * cos angle1) (radius * sin angle1), weight: 1.0 })
      else
        buildArcControlPoints radius startAngle (numSegs - 1) segAngle w newAcc

-- | Build knot vector for arc.
-- |
-- | Creates appropriate knot vector for degree-2 arc with given segments.
buildArcKnots :: Int -> KnotVector
buildArcKnots numSegs =
  let
    -- For degree 2 with numSegs segments, we need 2*numSegs + 3 knots
    numKnots = 2 * numSegs + 3
  in
    buildArray numKnots (\i ->
      if i <= 2 then Just 0.0
      else if i >= numKnots - 2 then Just 1.0
      else 
        let segIdx = (i - 2) / 2
        in Just (toNumber segIdx / toNumber numSegs)
    )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // distance computation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sum distances between consecutive points in an array.
-- |
-- | Used for computing approximate arc length via sampling.
sumDistances :: Array Point2D -> Int -> Number -> Int -> Number
sumDistances pts i acc n =
  if i >= n - 1 then acc
  else case { p0: index pts i, p1: index pts (i + 1) } of
    { p0: Just (Point2D a), p1: Just (Point2D b) } ->
      let 
        dx = b.x - a.x
        dy = b.y - a.y
        d = sqrt (dx * dx + dy * dy)
      in sumDistances pts (i + 1) (acc + d) n
    _ -> acc
