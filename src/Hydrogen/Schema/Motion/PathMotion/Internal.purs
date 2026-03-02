-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // motion // pathmotion // internal
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | PathMotion Internal — Helper functions for path evaluation.
-- |
-- | ## Exports
-- |
-- | - Path evaluation functions (position, tangent, length)
-- | - Point array interpolation
-- | - Math utilities (clamp, floor, epsilon)
-- | - Array building utilities
-- | - Angle conversion
-- |
-- | ## Dependencies
-- |
-- | - Schema.Geometry.Point (Point2D)
-- | - Schema.Geometry.Vector (Vector2D)
-- | - Schema.Geometry.Angle (Degrees)
-- | - Schema.Geometry.Spline (spline evaluation functions)
-- | - PathMotion.Types (PathSource)

module Hydrogen.Schema.Motion.PathMotion.Internal
  ( -- * Path Evaluation
    evaluatePathPosition
  , evaluatePathTangent
  , evaluatePathLength
  
  -- * Point Array Interpolation
  , interpolatePointArray
  , interpolatePointArrayTangent
  , pointArrayLength
  
  -- * Angle Utilities
  , vectorToAngle
  , addDegrees
  
  -- * Banking Calculation
  , calculateBank
  
  -- * Math Utilities
  , clamp01
  , clampNumber
  , floorNum
  , floorInt
  , epsilon
  
  -- * Array Utilities
  , buildArray
  , buildIntArray
  , (!!)
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
  , (>=)
  , (<=)
  , otherwise
  , negate
  , min
  , max
  )

import Data.Array (length, snoc, foldl, index)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Number (sqrt, atan2, pi, floor)
import Data.Int (toNumber, floor) as Int

import Hydrogen.Schema.Geometry.Point (Point2D(Point2D), point2D)
import Hydrogen.Schema.Geometry.Vector (Vector2D, vec2, normalize2, getVX, getVY)
import Hydrogen.Schema.Geometry.Angle (Degrees(Degrees))
import Hydrogen.Schema.Geometry.Spline 
  ( CatmullRomSpline
  , BSpline
  , catmullRomPointAt
  , catmullRomTangentAt
  , catmullRomLength
  , bSplinePointAt
  , bSplineTangentAt
  , bSplineLength
  )
import Hydrogen.Schema.Motion.PathMotion.Types (PathSource(CatmullRomSource, BSplineSource, PointArraySource))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // path evaluation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Evaluate position on path source.
evaluatePathPosition :: PathSource -> Number -> Point2D
evaluatePathPosition source t = case source of
  CatmullRomSource spline -> catmullRomPointAt t spline
  BSplineSource spline -> bSplinePointAt t spline
  PointArraySource pts -> interpolatePointArray t pts

-- | Evaluate tangent on path source.
evaluatePathTangent :: PathSource -> Number -> Vector2D
evaluatePathTangent source t = case source of
  CatmullRomSource spline -> catmullRomTangentAt t spline
  BSplineSource spline -> bSplineTangentAt t spline
  PointArraySource pts -> interpolatePointArrayTangent t pts

-- | Get path length.
evaluatePathLength :: PathSource -> Number
evaluatePathLength source = case source of
  CatmullRomSource spline -> catmullRomLength spline
  BSplineSource spline -> bSplineLength spline
  PointArraySource pts -> pointArrayLength pts

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // point array interpolation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Linear interpolation in point array.
interpolatePointArray :: Number -> Array Point2D -> Point2D
interpolatePointArray t pts =
  let 
    n = length pts
  in
    if n <= 0 then point2D 0.0 0.0
    else if n <= 1 then case pts !! 0 of
      Nothing -> point2D 0.0 0.0
      Just p -> p
    else
      let
        tScaled = clamp01 t * Int.toNumber (n - 1)
        i = floorInt tScaled
        frac = tScaled - Int.toNumber i
        idx1 = min i (n - 1)
        idx2 = min (i + 1) (n - 1)
      in
        case { p1: pts !! idx1, p2: pts !! idx2 } of
          { p1: Just (Point2D a), p2: Just (Point2D b) } ->
            point2D (a.x + frac * (b.x - a.x)) (a.y + frac * (b.y - a.y))
          _ -> point2D 0.0 0.0

-- | Tangent for point array (direction between adjacent points).
interpolatePointArrayTangent :: Number -> Array Point2D -> Vector2D
interpolatePointArrayTangent t pts =
  let 
    n = length pts
  in
    if n < 2 then vec2 1.0 0.0
    else
      let
        tScaled = clamp01 t * Int.toNumber (n - 1)
        i = floorInt tScaled
        idx1 = min i (n - 2)
        idx2 = idx1 + 1
      in
        case { p1: pts !! idx1, p2: pts !! idx2 } of
          { p1: Just (Point2D a), p2: Just (Point2D b) } ->
            normalize2 (vec2 (b.x - a.x) (b.y - a.y))
          _ -> vec2 1.0 0.0

-- | Total length of point array path.
pointArrayLength :: Array Point2D -> Number
pointArrayLength pts =
  let n = length pts
  in foldl (\acc i ->
       case { p1: pts !! i, p2: pts !! (i + 1) } of
         { p1: Just (Point2D a), p2: Just (Point2D b) } ->
           let dx = b.x - a.x
               dy = b.y - a.y
           in acc + sqrt (dx * dx + dy * dy)
         _ -> acc
     ) 0.0 (buildIntArray (n - 1))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // angle utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert vector to angle in degrees.
vectorToAngle :: Vector2D -> Degrees
vectorToAngle v =
  let radians = atan2 (getVY v) (getVX v)
  in Degrees (radians * 180.0 / pi)

-- | Add degrees.
addDegrees :: Degrees -> Degrees -> Degrees
addDegrees (Degrees a) (Degrees b) = Degrees (a + b)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // banking calculation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate banking angle based on curvature.
calculateBank :: Number -> PathSource -> Degrees -> Number -> Degrees
calculateBank t source maxBank smoothing =
  let
    -- Sample tangents before and after
    h = 0.01
    t1 = max 0.0 (t - h)
    t2 = min 1.0 (t + h)
    
    tan1 = evaluatePathTangent source t1
    tan2 = evaluatePathTangent source t2
    
    -- Angular change (approximates curvature)
    angle1 = vectorToAngle tan1
    angle2 = vectorToAngle tan2
    (Degrees a1) = angle1
    (Degrees a2) = angle2
    
    -- Normalize angle difference
    angleDiff = a2 - a1
    normalizedDiff = 
      if angleDiff > 180.0 then angleDiff - 360.0
      else if angleDiff < negate 180.0 then angleDiff + 360.0
      else angleDiff
    
    -- Scale by smoothing and max bank
    (Degrees maxB) = maxBank
    bankAmount = clampNumber (negate maxB) maxB (normalizedDiff * smoothing * 0.5)
  in
    Degrees bankAmount

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // math utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp to [0, 1]
clamp01 :: Number -> Number
clamp01 n
  | n < 0.0 = 0.0
  | n > 1.0 = 1.0
  | otherwise = n

-- | Clamp to range
-- | Named clampNumber to avoid shadowing Prelude.clamp
clampNumber :: Number -> Number -> Number -> Number
clampNumber lo hi n
  | n < lo = lo
  | n > hi = hi
  | otherwise = n

-- | Floor for Number
floorNum :: Number -> Number
floorNum n = floor n

-- | Floor to Int
floorInt :: Number -> Int
floorInt n = Int.floor n

-- | Small epsilon
epsilon :: Number
epsilon = 1.0e-10

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // array utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Array indexing operator (re-export from Data.Array)
infixl 8 index as !!

-- | Build array from function
buildArray :: forall a. Int -> (Int -> Maybe a) -> Array a
buildArray n f = buildArrayImpl 0 n f []

buildArrayImpl :: forall a. Int -> Int -> (Int -> Maybe a) -> Array a -> Array a
buildArrayImpl i n f acc =
  if i >= n then acc
  else case f i of
    Nothing -> buildArrayImpl (i + 1) n f acc
    Just x -> buildArrayImpl (i + 1) n f (snoc acc x)

-- | Build integer array
buildIntArray :: Int -> Array Int
buildIntArray n = buildArray n Just
