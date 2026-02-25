-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // geometry // spline
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Spline — Catmull-Rom and B-Spline curves for smooth interpolation.
-- |
-- | ## Design Philosophy
-- |
-- | While Bezier curves define shape through control points (some off-curve),
-- | splines provide different tradeoffs:
-- |
-- | - **Catmull-Rom**: Interpolating spline that passes through ALL control points.
-- |   Perfect for smooth paths through waypoints, camera motion, character animation.
-- |
-- | - **B-Spline**: Approximating spline with local control. Moving one point
-- |   only affects nearby curve segments. Ideal for modeling and design work.
-- |
-- | ## Mathematical Foundation
-- |
-- | ### Catmull-Rom
-- | Given 4 points P0, P1, P2, P3, the curve between P1 and P2 is:
-- |
-- | ```
-- | Q(t) = 0.5 * [(2*P1) +
-- |               (-P0 + P2) * t +
-- |               (2*P0 - 5*P1 + 4*P2 - P3) * t² +
-- |               (-P0 + 3*P1 - 3*P2 + P3) * t³]
-- | ```
-- |
-- | ### B-Spline (Cubic Uniform)
-- | Given 4 points P0, P1, P2, P3:
-- |
-- | ```
-- | Q(t) = (1/6) * [(1-t)³*P0 + 
-- |                 (3t³ - 6t² + 4)*P1 +
-- |                 (-3t³ + 3t² + 3t + 1)*P2 +
-- |                 t³*P3]
-- | ```
-- |
-- | ## Use Cases
-- |
-- | - Camera paths in 3D scenes
-- | - Character motion curves
-- | - Smooth scrolling trajectories
-- | - Generative art contours
-- | - Tool paths for CNC/robotics
-- |
-- | ## Dependencies
-- |
-- | - Schema.Geometry.Point (Point2D, Point3D)
-- | - Schema.Geometry.Vector (Vector2D for tangents)
-- | - Data.Array (control point sequences)

module Hydrogen.Schema.Geometry.Spline
  ( -- * Catmull-Rom Spline
    CatmullRomSpline(CatmullRomSpline)
  , catmullRomSpline
  , catmullRomClosed
  , catmullRomTension
  
  -- * B-Spline
  , BSpline(BSpline)
  , bSpline
  , bSplineClosed
  
  -- * Accessors
  , splinePoints
  , splineIsClosed
  , splineTension
  , bSplinePoints
  , bSplineIsClosed
  
  -- * Evaluation
  , catmullRomPointAt
  , catmullRomTangentAt
  , bSplinePointAt
  , bSplineTangentAt
  
  -- * Segment Extraction
  , catmullRomSegmentCount
  , catmullRomSegment
  , bSplineSegmentCount
  , bSplineSegment
  
  -- * Conversion
  , catmullRomToBeziers
  , bSplineToBeziers
  
  -- * Geometry
  , catmullRomLength
  , bSplineLength
  , catmullRomBoundingBox
  , bSplineBoundingBox
  
  -- * Sampling
  , sampleCatmullRom
  , sampleBSpline
  
  -- * Subspline Extraction
  , catmullRomSubspline
  , bSplineSubspline
  , catmullRomHead
  , catmullRomTail
  , bSplineHead
  , bSplineTail
  
  -- * Validation
  , isValidCatmullRom
  , isValidBSpline
  
  -- * Point Access
  , catmullRomFirstPoint
  , catmullRomLastPoint
  , bSplineFirstPoint
  , bSplineLastPoint
  
  -- * Arc Length Parameterization
  , catmullRomPointAtLength
  , bSplinePointAtLength
  
  -- * Tangent Sampling
  , sampleCatmullRomTangents
  , sampleBSplineTangents
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  , (==)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (&&)
  , (||)
  , otherwise
  , negate
  , min
  , max
  , map
  )

import Data.Array (length, index, (!!), drop, take, snoc, head, last, foldl)
import Data.Maybe (Maybe(..))
import Data.Number (sqrt)
import Data.Int (toNumber, floor) as Int
import Data.EuclideanRing (mod) as Ring

import Hydrogen.Schema.Geometry.Point (Point2D(Point2D), point2D)
import Hydrogen.Schema.Geometry.Vector (Vector2D, vec2)
import Hydrogen.Schema.Geometry.Bezier 
  ( CubicBezier
  , cubicBezier
  , cubicPointAt
  , cubicTangentAt
  , cubicLength
  , cubicBoundingBox
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // catmull-rom spline
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Catmull-Rom spline — interpolating spline through control points.
-- |
-- | The curve passes through every control point (except possibly first/last
-- | for open splines). Tension parameter controls curvature tightness.
-- |
-- | Minimum 4 points required for valid spline.
newtype CatmullRomSpline = CatmullRomSpline
  { points :: Array Point2D
  , closed :: Boolean
  , tension :: Number  -- 0.0 = Catmull-Rom, 0.5 = centripetal, 1.0 = chordal
  }

derive instance eqCatmullRomSpline :: Eq CatmullRomSpline

instance showCatmullRomSpline :: Show CatmullRomSpline where
  show (CatmullRomSpline s) = "(CatmullRomSpline points:" <> show (length s.points)
    <> " closed:" <> show s.closed
    <> " tension:" <> show s.tension <> ")"

-- | Create an open Catmull-Rom spline with standard tension (0.5).
-- |
-- | Returns Nothing if fewer than 4 points provided.
catmullRomSpline :: Array Point2D -> Maybe CatmullRomSpline
catmullRomSpline pts =
  if length pts < 4 then Nothing
  else Just (CatmullRomSpline { points: pts, closed: false, tension: 0.5 })

-- | Create a closed Catmull-Rom spline (loop).
-- |
-- | Returns Nothing if fewer than 4 points provided.
catmullRomClosed :: Array Point2D -> Maybe CatmullRomSpline
catmullRomClosed pts =
  if length pts < 4 then Nothing
  else Just (CatmullRomSpline { points: pts, closed: true, tension: 0.5 })

-- | Create a Catmull-Rom spline with custom tension.
-- |
-- | - tension = 0.0: Uniform (standard Catmull-Rom)
-- | - tension = 0.5: Centripetal (prevents cusps and self-intersection)
-- | - tension = 1.0: Chordal (follows chord lengths)
-- |
-- | Returns Nothing if fewer than 4 points provided.
catmullRomTension :: Number -> Array Point2D -> Maybe CatmullRomSpline
catmullRomTension t pts =
  if length pts < 4 then Nothing
  else Just (CatmullRomSpline { points: pts, closed: false, tension: clamp01 t })

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // b-spline
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Cubic uniform B-Spline — approximating spline with local control.
-- |
-- | The curve does NOT pass through control points (except possibly endpoints).
-- | Moving a control point only affects the nearby curve segments, making
-- | B-splines excellent for interactive design.
-- |
-- | Minimum 4 points required for valid spline.
newtype BSpline = BSpline
  { points :: Array Point2D
  , closed :: Boolean
  }

derive instance eqBSpline :: Eq BSpline

instance showBSpline :: Show BSpline where
  show (BSpline s) = "(BSpline points:" <> show (length s.points)
    <> " closed:" <> show s.closed <> ")"

-- | Create an open cubic B-spline.
-- |
-- | Returns Nothing if fewer than 4 points provided.
bSpline :: Array Point2D -> Maybe BSpline
bSpline pts =
  if length pts < 4 then Nothing
  else Just (BSpline { points: pts, closed: false })

-- | Create a closed cubic B-spline (loop).
-- |
-- | Returns Nothing if fewer than 4 points provided.
bSplineClosed :: Array Point2D -> Maybe BSpline
bSplineClosed pts =
  if length pts < 4 then Nothing
  else Just (BSpline { points: pts, closed: true })

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // accessors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get control points of Catmull-Rom spline.
splinePoints :: CatmullRomSpline -> Array Point2D
splinePoints (CatmullRomSpline s) = s.points

-- | Check if Catmull-Rom spline is closed.
splineIsClosed :: CatmullRomSpline -> Boolean
splineIsClosed (CatmullRomSpline s) = s.closed

-- | Get tension parameter of Catmull-Rom spline.
splineTension :: CatmullRomSpline -> Number
splineTension (CatmullRomSpline s) = s.tension

-- | Get control points of B-spline.
bSplinePoints :: BSpline -> Array Point2D
bSplinePoints (BSpline s) = s.points

-- | Check if B-spline is closed.
bSplineIsClosed :: BSpline -> Boolean
bSplineIsClosed (BSpline s) = s.closed

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // evaluation
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Evaluate Catmull-Rom spline at parameter t ∈ [0, 1].
-- |
-- | t=0 corresponds to start of first segment (after first point for open spline).
-- | t=1 corresponds to end of last segment.
catmullRomPointAt :: Number -> CatmullRomSpline -> Point2D
catmullRomPointAt t spline =
  let
    segCount = catmullRomSegmentCount spline
    t' = clamp01 t
    
    -- Map t to segment index and local parameter
    tScaled = t' * toNumber segCount
    segIndex = Int.floor tScaled
    localT = tScaled - toNumber segIndex
    
    -- Handle edge case at t=1
    actualSegIndex = if segIndex >= segCount then segCount - 1 else segIndex
    actualLocalT = if segIndex >= segCount then 1.0 else localT
  in
    case catmullRomSegment actualSegIndex spline of
      Nothing -> origin  -- Fallback (shouldn't happen with valid spline)
      Just { p0, p1, p2, p3 } -> 
        catmullRomEvaluate actualLocalT p0 p1 p2 p3 (splineTension spline)

-- | Tangent vector at parameter t for Catmull-Rom spline.
catmullRomTangentAt :: Number -> CatmullRomSpline -> Vector2D
catmullRomTangentAt t spline =
  let
    segCount = catmullRomSegmentCount spline
    t' = clamp01 t
    tScaled = t' * toNumber segCount
    segIndex = Int.floor tScaled
    localT = tScaled - toNumber segIndex
    actualSegIndex = if segIndex >= segCount then segCount - 1 else segIndex
    actualLocalT = if segIndex >= segCount then 1.0 else localT
  in
    case catmullRomSegment actualSegIndex spline of
      Nothing -> vec2 1.0 0.0
      Just { p0, p1, p2, p3 } ->
        catmullRomTangentEvaluate actualLocalT p0 p1 p2 p3 (splineTension spline)

-- | Evaluate B-spline at parameter t ∈ [0, 1].
bSplinePointAt :: Number -> BSpline -> Point2D
bSplinePointAt t spline =
  let
    segCount = bSplineSegmentCount spline
    t' = clamp01 t
    tScaled = t' * toNumber segCount
    segIndex = Int.floor tScaled
    localT = tScaled - toNumber segIndex
    actualSegIndex = if segIndex >= segCount then segCount - 1 else segIndex
    actualLocalT = if segIndex >= segCount then 1.0 else localT
  in
    case bSplineSegment actualSegIndex spline of
      Nothing -> origin
      Just { p0, p1, p2, p3 } -> bSplineEvaluate actualLocalT p0 p1 p2 p3

-- | Tangent vector at parameter t for B-spline.
bSplineTangentAt :: Number -> BSpline -> Vector2D
bSplineTangentAt t spline =
  let
    segCount = bSplineSegmentCount spline
    t' = clamp01 t
    tScaled = t' * toNumber segCount
    segIndex = Int.floor tScaled
    localT = tScaled - toNumber segIndex
    actualSegIndex = if segIndex >= segCount then segCount - 1 else segIndex
    actualLocalT = if segIndex >= segCount then 1.0 else localT
  in
    case bSplineSegment actualSegIndex spline of
      Nothing -> vec2 1.0 0.0
      Just { p0, p1, p2, p3 } -> bSplineTangentEvaluate actualLocalT p0 p1 p2 p3

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // segment extraction
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Number of segments in Catmull-Rom spline.
-- |
-- | For open spline with n points: n - 3 segments
-- | For closed spline with n points: n segments
catmullRomSegmentCount :: CatmullRomSpline -> Int
catmullRomSegmentCount (CatmullRomSpline s) =
  let n = length s.points
  in if s.closed then n else n - 3

-- | Get the 4 control points for segment i of Catmull-Rom spline.
-- |
-- | Returns Nothing if index out of bounds.
catmullRomSegment :: Int -> CatmullRomSpline -> Maybe { p0 :: Point2D, p1 :: Point2D, p2 :: Point2D, p3 :: Point2D }
catmullRomSegment i (CatmullRomSpline s) =
  let
    n = length s.points
    segCount = if s.closed then n else n - 3
  in
    if i < 0 || i >= segCount then Nothing
    else if s.closed then
      -- Closed: wrap around
      let
        i0 = i
        i1 = wrapIndex (i + 1) n
        i2 = wrapIndex (i + 2) n
        i3 = wrapIndex (i + 3) n
      in
        case { p0: s.points !! i0, p1: s.points !! i1, p2: s.points !! i2, p3: s.points !! i3 } of
          { p0: Just pp0, p1: Just pp1, p2: Just pp2, p3: Just pp3 } ->
            Just { p0: pp0, p1: pp1, p2: pp2, p3: pp3 }
          _ -> Nothing
    else
      -- Open: segment i uses points i, i+1, i+2, i+3
      case { p0: s.points !! i, p1: s.points !! (i+1), p2: s.points !! (i+2), p3: s.points !! (i+3) } of
        { p0: Just pp0, p1: Just pp1, p2: Just pp2, p3: Just pp3 } ->
          Just { p0: pp0, p1: pp1, p2: pp2, p3: pp3 }
        _ -> Nothing

-- | Number of segments in B-spline.
-- |
-- | For open spline with n points: n - 3 segments
-- | For closed spline with n points: n segments
bSplineSegmentCount :: BSpline -> Int
bSplineSegmentCount (BSpline s) =
  let n = length s.points
  in if s.closed then n else n - 3

-- | Get the 4 control points for segment i of B-spline.
bSplineSegment :: Int -> BSpline -> Maybe { p0 :: Point2D, p1 :: Point2D, p2 :: Point2D, p3 :: Point2D }
bSplineSegment i (BSpline s) =
  let
    n = length s.points
    segCount = if s.closed then n else n - 3
  in
    if i < 0 || i >= segCount then Nothing
    else if s.closed then
      let
        i0 = i
        i1 = wrapIndex (i + 1) n
        i2 = wrapIndex (i + 2) n
        i3 = wrapIndex (i + 3) n
      in
        case { p0: s.points !! i0, p1: s.points !! i1, p2: s.points !! i2, p3: s.points !! i3 } of
          { p0: Just pp0, p1: Just pp1, p2: Just pp2, p3: Just pp3 } ->
            Just { p0: pp0, p1: pp1, p2: pp2, p3: pp3 }
          _ -> Nothing
    else
      case { p0: s.points !! i, p1: s.points !! (i+1), p2: s.points !! (i+2), p3: s.points !! (i+3) } of
        { p0: Just pp0, p1: Just pp1, p2: Just pp2, p3: Just pp3 } ->
          Just { p0: pp0, p1: pp1, p2: pp2, p3: pp3 }
        _ -> Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // conversion
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Convert Catmull-Rom spline to array of cubic Bezier curves.
-- |
-- | Each segment becomes one Bezier. This allows using existing Bezier
-- | infrastructure for rendering, hit-testing, etc.
catmullRomToBeziers :: CatmullRomSpline -> Array CubicBezier
catmullRomToBeziers spline =
  let
    segCount = catmullRomSegmentCount spline
    tension = splineTension spline
  in
    buildArray segCount (\i ->
      case catmullRomSegment i spline of
        Nothing -> Nothing
        Just { p0, p1, p2, p3 } -> Just (catmullRomToBezier p0 p1 p2 p3 tension)
    )

-- | Convert B-spline to array of cubic Bezier curves.
bSplineToBeziers :: BSpline -> Array CubicBezier
bSplineToBeziers spline =
  let segCount = bSplineSegmentCount spline
  in buildArray segCount (\i ->
       case bSplineSegment i spline of
         Nothing -> Nothing
         Just { p0, p1, p2, p3 } -> Just (bSplineToBezier p0 p1 p2 p3)
     )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // geometry
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Approximate arc length of Catmull-Rom spline.
-- |
-- | Converts to Beziers and sums their lengths.
catmullRomLength :: CatmullRomSpline -> Number
catmullRomLength spline =
  let beziers = catmullRomToBeziers spline
  in foldl (\acc b -> acc + cubicLength b) 0.0 beziers

-- | Approximate arc length of B-spline.
bSplineLength :: BSpline -> Number
bSplineLength spline =
  let beziers = bSplineToBeziers spline
  in foldl (\acc b -> acc + cubicLength b) 0.0 beziers

-- | Bounding box of Catmull-Rom spline.
catmullRomBoundingBox :: CatmullRomSpline -> { minX :: Number, minY :: Number, maxX :: Number, maxY :: Number }
catmullRomBoundingBox spline =
  let beziers = catmullRomToBeziers spline
  in foldl mergeBounds initialBounds (map cubicBoundingBox beziers)

-- | Bounding box of B-spline.
bSplineBoundingBox :: BSpline -> { minX :: Number, minY :: Number, maxX :: Number, maxY :: Number }
bSplineBoundingBox spline =
  let beziers = bSplineToBeziers spline
  in foldl mergeBounds initialBounds (map cubicBoundingBox beziers)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // sampling
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Sample Catmull-Rom spline at n evenly-spaced parameter values.
-- |
-- | Returns array of n+1 points from t=0 to t=1.
sampleCatmullRom :: Int -> CatmullRomSpline -> Array Point2D
sampleCatmullRom n spline =
  if n <= 0 then []
  else buildArray (n + 1) (\i ->
    let t = toNumber i / toNumber n
    in Just (catmullRomPointAt t spline)
  )

-- | Sample B-spline at n evenly-spaced parameter values.
sampleBSpline :: Int -> BSpline -> Array Point2D
sampleBSpline n spline =
  if n <= 0 then []
  else buildArray (n + 1) (\i ->
    let t = toNumber i / toNumber n
    in Just (bSplinePointAt t spline)
  )

-- | Sample tangent vectors along Catmull-Rom spline.
-- |
-- | Returns array of n+1 tangent vectors from t=0 to t=1.
-- | Uses Bezier conversion for accurate tangent computation.
sampleCatmullRomTangents :: Int -> CatmullRomSpline -> Array Vector2D
sampleCatmullRomTangents n spline =
  if n <= 0 then []
  else 
    let 
      beziers = catmullRomToBeziers spline
      segCount = catmullRomSegmentCount spline
    in buildArray (n + 1) (\i ->
      let 
        t = toNumber i / toNumber n
        tScaled = t * toNumber segCount
        segIndex = Int.floor tScaled
        localT = tScaled - toNumber segIndex
        actualSegIndex = if segIndex >= segCount then segCount - 1 else segIndex
        actualLocalT = if segIndex >= segCount then 1.0 else localT
      in case index beziers actualSegIndex of
        Nothing -> Just (vec2 1.0 0.0)
        Just bez -> Just (cubicTangentAt actualLocalT bez)
    )

-- | Sample tangent vectors along B-spline.
sampleBSplineTangents :: Int -> BSpline -> Array Vector2D
sampleBSplineTangents n spline =
  if n <= 0 then []
  else 
    let 
      beziers = bSplineToBeziers spline
      segCount = bSplineSegmentCount spline
    in buildArray (n + 1) (\i ->
      let 
        t = toNumber i / toNumber n
        tScaled = t * toNumber segCount
        segIndex = Int.floor tScaled
        localT = tScaled - toNumber segIndex
        actualSegIndex = if segIndex >= segCount then segCount - 1 else segIndex
        actualLocalT = if segIndex >= segCount then 1.0 else localT
      in case index beziers actualSegIndex of
        Nothing -> Just (vec2 1.0 0.0)
        Just bez -> Just (cubicTangentAt actualLocalT bez)
    )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // subspline extraction
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Extract a subspline from a Catmull-Rom spline.
-- |
-- | Takes first n points (minimum 4 required for valid spline).
catmullRomSubspline :: Int -> CatmullRomSpline -> Maybe CatmullRomSpline
catmullRomSubspline n (CatmullRomSpline s) =
  let pts = take n s.points
  in if length pts < 4 then Nothing
     else Just (CatmullRomSpline { points: pts, closed: false, tension: s.tension })

-- | Extract a subspline from a B-spline.
bSplineSubspline :: Int -> BSpline -> Maybe BSpline
bSplineSubspline n (BSpline s) =
  let pts = take n s.points
  in if length pts < 4 then Nothing
     else Just (BSpline { points: pts, closed: false })

-- | Get head portion of Catmull-Rom spline (first half of points).
catmullRomHead :: CatmullRomSpline -> Maybe CatmullRomSpline
catmullRomHead spline =
  let n = length (splinePoints spline)
      halfN = n / 2
  in if halfN < 4 then Nothing
     else catmullRomSubspline (halfN + 2) spline  -- +2 for overlap

-- | Get tail portion of Catmull-Rom spline (second half of points).
catmullRomTail :: CatmullRomSpline -> Maybe CatmullRomSpline
catmullRomTail (CatmullRomSpline s) =
  let n = length s.points
      halfN = n / 2
      pts = drop (halfN - 2) s.points  -- -2 for overlap
  in if length pts < 4 then Nothing
     else Just (CatmullRomSpline { points: pts, closed: false, tension: s.tension })

-- | Get head portion of B-spline.
bSplineHead :: BSpline -> Maybe BSpline
bSplineHead spline =
  let n = length (bSplinePoints spline)
      halfN = n / 2
  in if halfN < 4 then Nothing
     else bSplineSubspline (halfN + 2) spline

-- | Get tail portion of B-spline.
bSplineTail :: BSpline -> Maybe BSpline
bSplineTail (BSpline s) =
  let n = length s.points
      halfN = n / 2
      pts = drop (halfN - 2) s.points
  in if length pts < 4 then Nothing
     else Just (BSpline { points: pts, closed: false })

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // validation
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Check if Catmull-Rom spline is valid.
-- |
-- | Valid means: at least 4 points, all points are finite numbers.
isValidCatmullRom :: CatmullRomSpline -> Boolean
isValidCatmullRom (CatmullRomSpline s) =
  length s.points >= 4 && allPointsFinite s.points && s.tension >= 0.0 && s.tension <= 1.0

-- | Check if B-spline is valid.
isValidBSpline :: BSpline -> Boolean
isValidBSpline (BSpline s) =
  length s.points >= 4 && allPointsFinite s.points

-- | Check all points have finite coordinates.
allPointsFinite :: Array Point2D -> Boolean
allPointsFinite pts = foldl (\acc p -> acc && isFinitePoint p) true pts

-- | Check if a point has finite coordinates.
isFinitePoint :: Point2D -> Boolean
isFinitePoint (Point2D p) =
  isFiniteNumber p.x && isFiniteNumber p.y

-- | Check if a number is finite (not NaN or Infinity).
isFiniteNumber :: Number -> Boolean
isFiniteNumber n = n == n && n < 1.0e308 && n > negate 1.0e308

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // point access
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get first control point of Catmull-Rom spline.
catmullRomFirstPoint :: CatmullRomSpline -> Maybe Point2D
catmullRomFirstPoint (CatmullRomSpline s) = head s.points

-- | Get last control point of Catmull-Rom spline.
catmullRomLastPoint :: CatmullRomSpline -> Maybe Point2D
catmullRomLastPoint (CatmullRomSpline s) = last s.points

-- | Get first control point of B-spline.
bSplineFirstPoint :: BSpline -> Maybe Point2D
bSplineFirstPoint (BSpline s) = head s.points

-- | Get last control point of B-spline.
bSplineLastPoint :: BSpline -> Maybe Point2D
bSplineLastPoint (BSpline s) = last s.points

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                  // arc length parameterization
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Evaluate Catmull-Rom spline at a given arc length.
-- |
-- | Unlike pointAt which uses parameter t, this uses actual curve length.
-- | More expensive but gives uniform spacing along the curve.
catmullRomPointAtLength :: Number -> CatmullRomSpline -> Point2D
catmullRomPointAtLength targetLength spline =
  let
    totalLen = catmullRomLength spline
    normalizedLen = clamp01 (targetLength / totalLen)
    
    -- Use bisection search to find t that gives desired arc length
    t = bisectForLength normalizedLen spline 0.0 1.0 20
  in
    catmullRomPointAt t spline

-- | Evaluate B-spline at a given arc length.
bSplinePointAtLength :: Number -> BSpline -> Point2D
bSplinePointAtLength targetLength spline =
  let
    totalLen = bSplineLength spline
    normalizedLen = clamp01 (targetLength / totalLen)
    t = bisectForLengthB normalizedLen spline 0.0 1.0 20
  in
    bSplinePointAt t spline

-- | Bisection search for arc length parameterization (Catmull-Rom).
bisectForLength :: Number -> CatmullRomSpline -> Number -> Number -> Int -> Number
bisectForLength targetRatio spline lo hi iterations =
  if iterations <= 0 then (lo + hi) / 2.0
  else
    let
      mid = (lo + hi) / 2.0
      -- Sample spline up to mid and estimate length ratio
      midLen = catmullRomLengthUpTo mid spline
      totalLen = catmullRomLength spline
      midRatio = midLen / totalLen
    in
      if midRatio < targetRatio
      then bisectForLength targetRatio spline mid hi (iterations - 1)
      else bisectForLength targetRatio spline lo mid (iterations - 1)

-- | Bisection search for arc length parameterization (B-spline).
bisectForLengthB :: Number -> BSpline -> Number -> Number -> Int -> Number
bisectForLengthB targetRatio spline lo hi iterations =
  if iterations <= 0 then (lo + hi) / 2.0
  else
    let
      mid = (lo + hi) / 2.0
      midLen = bSplineLengthUpTo mid spline
      totalLen = bSplineLength spline
      midRatio = midLen / totalLen
    in
      if midRatio < targetRatio
      then bisectForLengthB targetRatio spline mid hi (iterations - 1)
      else bisectForLengthB targetRatio spline lo mid (iterations - 1)

-- | Approximate arc length up to parameter t.
catmullRomLengthUpTo :: Number -> CatmullRomSpline -> Number
catmullRomLengthUpTo t spline =
  let
    beziers = catmullRomToBeziers spline
    segCount = catmullRomSegmentCount spline
    t' = clamp01 t
    tScaled = t' * toNumber segCount
    fullSegs = Int.floor tScaled
    localT = tScaled - toNumber fullSegs
    
    -- Sum full segments
    fullLen = sumBezierLengths fullSegs beziers 0 0.0
    
    -- Add partial segment using Bezier pointAt for distance approximation
    partialLen = case index beziers fullSegs of
      Nothing -> 0.0
      Just bez -> 
        -- Approximate partial length by sampling
        let samples = 10
        in foldl (\acc i ->
             let 
               t1 = toNumber i / toNumber samples * localT
               t2 = toNumber (i + 1) / toNumber samples * localT
               (Point2D p1) = cubicPointAt t1 bez
               (Point2D p2) = cubicPointAt t2 bez
               dx = p2.x - p1.x
               dy = p2.y - p1.y
             in acc + sqrt (dx * dx + dy * dy)
           ) 0.0 (buildIntArray samples)
  in
    fullLen + partialLen

-- | Approximate arc length up to parameter t for B-spline.
bSplineLengthUpTo :: Number -> BSpline -> Number
bSplineLengthUpTo t spline =
  let
    beziers = bSplineToBeziers spline
    segCount = bSplineSegmentCount spline
    t' = clamp01 t
    tScaled = t' * toNumber segCount
    fullSegs = Int.floor tScaled
    localT = tScaled - toNumber fullSegs
    
    fullLen = sumBezierLengths fullSegs beziers 0 0.0
    
    partialLen = case index beziers fullSegs of
      Nothing -> 0.0
      Just bez -> 
        let samples = 10
        in foldl (\acc i ->
             let 
               t1 = toNumber i / toNumber samples * localT
               t2 = toNumber (i + 1) / toNumber samples * localT
               (Point2D p1) = cubicPointAt t1 bez
               (Point2D p2) = cubicPointAt t2 bez
               dx = p2.x - p1.x
               dy = p2.y - p1.y
             in acc + sqrt (dx * dx + dy * dy)
           ) 0.0 (buildIntArray samples)
  in
    fullLen + partialLen

-- | Sum lengths of first n beziers.
sumBezierLengths :: Int -> Array CubicBezier -> Int -> Number -> Number
sumBezierLengths n beziers i acc =
  if i >= n then acc
  else case index beziers i of
    Nothing -> acc
    Just bez -> sumBezierLengths n beziers (i + 1) (acc + cubicLength bez)

-- | Build array of integers [0, 1, ..., n-1].
buildIntArray :: Int -> Array Int
buildIntArray n = buildArray n (\i -> Just i)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Evaluate Catmull-Rom segment at local parameter t ∈ [0, 1].
-- |
-- | Uses centripetal parameterization with alpha = tension.
-- | - alpha = 0.0: Uniform (standard Catmull-Rom, can have cusps)
-- | - alpha = 0.5: Centripetal (prevents cusps and self-intersection)
-- | - alpha = 1.0: Chordal (follows chord lengths exactly)
-- |
-- | The centripetal variant is mathematically superior for most use cases
-- | as it guarantees no cusps or self-intersections while still being smooth.
catmullRomEvaluate :: Number -> Point2D -> Point2D -> Point2D -> Point2D -> Number -> Point2D
catmullRomEvaluate t (Point2D p0) (Point2D p1) (Point2D p2) (Point2D p3) alpha =
  let
    -- Compute knot intervals using |P_{i+1} - P_i|^alpha
    -- This is the key to centripetal parameterization
    d01 = chordLength p0 p1 alpha
    d12 = chordLength p1 p2 alpha
    d23 = chordLength p2 p3 alpha
    
    -- Knot values (cumulative)
    t0 = 0.0
    t1 = t0 + d01
    t2 = t1 + d12
    t3 = t2 + d23
    
    -- Map input t ∈ [0,1] to knot interval [t1, t2]
    tKnot = t1 + t * (t2 - t1)
    
    -- Barry-Goldman pyramid algorithm for Catmull-Rom
    -- This is a recursive interpolation scheme
    
    -- First level: linear interpolation between adjacent points
    a1x = interpolateKnot t0 t1 tKnot p0.x p1.x
    a1y = interpolateKnot t0 t1 tKnot p0.y p1.y
    a2x = interpolateKnot t1 t2 tKnot p1.x p2.x
    a2y = interpolateKnot t1 t2 tKnot p1.y p2.y
    a3x = interpolateKnot t2 t3 tKnot p2.x p3.x
    a3y = interpolateKnot t2 t3 tKnot p2.y p3.y
    
    -- Second level
    b1x = interpolateKnot t0 t2 tKnot a1x a2x
    b1y = interpolateKnot t0 t2 tKnot a1y a2y
    b2x = interpolateKnot t1 t3 tKnot a2x a3x
    b2y = interpolateKnot t1 t3 tKnot a2y a3y
    
    -- Third level (final point)
    cx = interpolateKnot t1 t2 tKnot b1x b2x
    cy = interpolateKnot t1 t2 tKnot b1y b2y
  in
    point2D cx cy

-- | Compute chord length raised to power alpha.
-- |
-- | |P1 - P0|^alpha where alpha controls the parameterization type.
chordLength :: { x :: Number, y :: Number } -> { x :: Number, y :: Number } -> Number -> Number
chordLength p0 p1 alpha =
  let
    dx = p1.x - p0.x
    dy = p1.y - p0.y
    distSq = dx * dx + dy * dy
  in
    -- Handle degenerate case (coincident points)
    if distSq < epsilon then epsilon
    -- For alpha = 0.5, we want sqrt(dist) = dist^0.5 = (distSq)^0.25
    -- For alpha = 1.0, we want dist = (distSq)^0.5
    -- General: dist^alpha = (distSq)^(alpha/2)
    else pow distSq (alpha / 2.0)

-- | Linear interpolation in knot space.
-- |
-- | Given knots ti and tj, and values vi and vj, compute value at t.
interpolateKnot :: Number -> Number -> Number -> Number -> Number -> Number
interpolateKnot ti tj t vi vj =
  let denom = tj - ti
  in if denom < epsilon then vi
     else vi + (t - ti) / denom * (vj - vi)

-- | Power function using exp/log.
-- |
-- | Computes x^y for positive x.
pow :: Number -> Number -> Number
pow x y =
  if x <= 0.0 then 0.0
  else exp (y * log x)

-- | Natural logarithm (imported via FFI-free approximation or Data.Number)
log :: Number -> Number
log x = logImpl x

-- | Exponential function
exp :: Number -> Number
exp x = expImpl x

-- | Log implementation using series expansion
-- | ln(x) = 2 * sum_{n=0}^∞ (1/(2n+1)) * ((x-1)/(x+1))^(2n+1)
logImpl :: Number -> Number
logImpl x =
  if x <= 0.0 then negate 1.0e308  -- -infinity approximation
  else if x < 0.5 || x > 2.0 then
    -- Range reduction: ln(x) = ln(x/e^k) + k for appropriate k
    let k = logEstimate x
        xReduced = x / expImpl k
    in logSeries xReduced + k
  else logSeries x

-- | Estimate log for range reduction
logEstimate :: Number -> Number
logEstimate x = 
  if x > 1.0 then logEstimatePositive x 0.0
  else negate (logEstimatePositive (1.0 / x) 0.0)

logEstimatePositive :: Number -> Number -> Number
logEstimatePositive x acc =
  if x < 2.718281828 then acc
  else logEstimatePositive (x / 2.718281828) (acc + 1.0)

-- | Log series for x near 1
logSeries :: Number -> Number
logSeries x =
  let
    y = (x - 1.0) / (x + 1.0)
    y2 = y * y
  in 2.0 * y * (1.0 + y2 / 3.0 + y2 * y2 / 5.0 + y2 * y2 * y2 / 7.0 + 
                y2 * y2 * y2 * y2 / 9.0 + y2 * y2 * y2 * y2 * y2 / 11.0)

-- | Exp implementation using series expansion
-- | e^x = sum_{n=0}^∞ x^n / n!
expImpl :: Number -> Number
expImpl x =
  if x > 700.0 then 1.0e308  -- overflow protection
  else if x < negate 700.0 then 0.0  -- underflow protection
  else if x < 0.0 then 1.0 / expImpl (negate x)
  else if x > 1.0 then
    -- Range reduction: e^x = (e^(x/n))^n
    let n = Int.floor x + 1
        xSmall = x / toNumber n
        eSmall = expSeries xSmall
    in powInt eSmall n
  else expSeries x

-- | Exp series for |x| < 1
expSeries :: Number -> Number
expSeries x =
  let
    x2 = x * x
    x3 = x2 * x
    x4 = x3 * x
    x5 = x4 * x
    x6 = x5 * x
    x7 = x6 * x
    x8 = x7 * x
  in 1.0 + x + x2 / 2.0 + x3 / 6.0 + x4 / 24.0 + x5 / 120.0 + 
     x6 / 720.0 + x7 / 5040.0 + x8 / 40320.0

-- | Integer power by repeated squaring
powInt :: Number -> Int -> Number
powInt base n =
  if n <= 0 then 1.0
  else if wrapIndex n 2 == 0 then
    let half = powInt base (n / 2)
    in half * half
  else base * powInt base (n - 1)

-- | Small epsilon for numerical stability
epsilon :: Number
epsilon = 1.0e-10

-- | Tangent of Catmull-Rom segment at local parameter t.
-- |
-- | Computed via numerical differentiation of the Barry-Goldman algorithm.
-- | Uses central difference for accuracy.
catmullRomTangentEvaluate :: Number -> Point2D -> Point2D -> Point2D -> Point2D -> Number -> Vector2D
catmullRomTangentEvaluate t pp0 pp1 pp2 pp3 alpha =
  let
    -- Use central difference for derivative
    h = 0.0001
    t1 = max 0.0 (t - h)
    t2 = min 1.0 (t + h)
    actualH = (t2 - t1) / 2.0
    
    (Point2D pMinus) = catmullRomEvaluate t1 pp0 pp1 pp2 pp3 alpha
    (Point2D pPlus) = catmullRomEvaluate t2 pp0 pp1 pp2 pp3 alpha
    
    -- Scale by knot interval to get proper velocity
    (Point2D p1) = pp1
    (Point2D p2) = pp2
    d12 = chordLength p1 p2 alpha
    
    dx = (pPlus.x - pMinus.x) / (2.0 * actualH) * d12
    dy = (pPlus.y - pMinus.y) / (2.0 * actualH) * d12
  in
    vec2 dx dy

-- | Convert Catmull-Rom segment to equivalent cubic Bezier.
-- |
-- | The Bezier control points are derived from the Catmull-Rom tangents
-- | at the endpoints.
catmullRomToBezier :: Point2D -> Point2D -> Point2D -> Point2D -> Number -> CubicBezier
catmullRomToBezier (Point2D p0) (Point2D p1) (Point2D p2) (Point2D p3) _ =
  let
    -- Catmull-Rom goes from p1 to p2
    -- Tangent at p1: 0.5 * (p2 - p0)
    -- Tangent at p2: 0.5 * (p3 - p1)
    
    -- Bezier control points: P0, P0 + T0/3, P1 - T1/3, P1
    t0x = 0.5 * (p2.x - p0.x)
    t0y = 0.5 * (p2.y - p0.y)
    t1x = 0.5 * (p3.x - p1.x)
    t1y = 0.5 * (p3.y - p1.y)
    
    bp0 = point2D p1.x p1.y
    bp1 = point2D (p1.x + t0x / 3.0) (p1.y + t0y / 3.0)
    bp2 = point2D (p2.x - t1x / 3.0) (p2.y - t1y / 3.0)
    bp3 = point2D p2.x p2.y
  in
    cubicBezier bp0 bp1 bp2 bp3

-- | Evaluate B-spline segment at local parameter t ∈ [0, 1].
-- |
-- | Uses cubic uniform B-spline basis.
bSplineEvaluate :: Number -> Point2D -> Point2D -> Point2D -> Point2D -> Point2D
bSplineEvaluate t (Point2D p0) (Point2D p1) (Point2D p2) (Point2D p3) =
  let
    t2 = t * t
    t3 = t2 * t
    mt = 1.0 - t
    mt3 = mt * mt * mt
    
    -- B-spline basis functions (cubic uniform)
    -- N0 = (1-t)³/6
    -- N1 = (3t³ - 6t² + 4)/6
    -- N2 = (-3t³ + 3t² + 3t + 1)/6
    -- N3 = t³/6
    
    b0 = mt3 / 6.0
    b1 = (3.0 * t3 - 6.0 * t2 + 4.0) / 6.0
    b2 = (negate 3.0 * t3 + 3.0 * t2 + 3.0 * t + 1.0) / 6.0
    b3 = t3 / 6.0
    
    x = b0 * p0.x + b1 * p1.x + b2 * p2.x + b3 * p3.x
    y = b0 * p0.y + b1 * p1.y + b2 * p2.y + b3 * p3.y
  in
    point2D x y

-- | Tangent of B-spline segment at local parameter t.
bSplineTangentEvaluate :: Number -> Point2D -> Point2D -> Point2D -> Point2D -> Vector2D
bSplineTangentEvaluate t (Point2D p0) (Point2D p1) (Point2D p2) (Point2D p3) =
  let
    t2 = t * t
    mt = 1.0 - t
    mt2 = mt * mt
    
    -- Derivatives of B-spline basis functions
    -- N0' = -3(1-t)²/6 = -(1-t)²/2
    -- N1' = (9t² - 12t)/6 = (3t² - 4t)/2
    -- N2' = (-9t² + 6t + 3)/6 = (-3t² + 2t + 1)/2
    -- N3' = 3t²/6 = t²/2
    
    db0 = negate mt2 / 2.0
    db1 = (3.0 * t2 - 4.0 * t) / 2.0
    db2 = (negate 3.0 * t2 + 2.0 * t + 1.0) / 2.0
    db3 = t2 / 2.0
    
    dx = db0 * p0.x + db1 * p1.x + db2 * p2.x + db3 * p3.x
    dy = db0 * p0.y + db1 * p1.y + db2 * p2.y + db3 * p3.y
  in
    vec2 dx dy

-- | Convert B-spline segment to equivalent cubic Bezier.
-- |
-- | B-spline to Bezier conversion uses the de Boor algorithm.
bSplineToBezier :: Point2D -> Point2D -> Point2D -> Point2D -> CubicBezier
bSplineToBezier (Point2D p0) (Point2D p1) (Point2D p2) (Point2D p3) =
  let
    -- B-spline to Bezier conversion matrix (for uniform cubic):
    -- B0 = (P0 + 4P1 + P2) / 6
    -- B1 = (4P1 + 2P2) / 6 = (2P1 + P2) / 3
    -- B2 = (2P1 + 4P2) / 6 = (P1 + 2P2) / 3
    -- B3 = (P1 + 4P2 + P3) / 6
    
    bp0 = point2D
      ((p0.x + 4.0 * p1.x + p2.x) / 6.0)
      ((p0.y + 4.0 * p1.y + p2.y) / 6.0)
    
    bp1 = point2D
      ((2.0 * p1.x + p2.x) / 3.0)
      ((2.0 * p1.y + p2.y) / 3.0)
    
    bp2 = point2D
      ((p1.x + 2.0 * p2.x) / 3.0)
      ((p1.y + 2.0 * p2.y) / 3.0)
    
    bp3 = point2D
      ((p1.x + 4.0 * p2.x + p3.x) / 6.0)
      ((p1.y + 4.0 * p2.y + p3.y) / 6.0)
  in
    cubicBezier bp0 bp1 bp2 bp3

-- | Clamp value to [0, 1]
clamp01 :: Number -> Number
clamp01 n
  | n < 0.0 = 0.0
  | n > 1.0 = 1.0
  | otherwise = n

-- | Origin point for fallbacks
origin :: Point2D
origin = point2D 0.0 0.0

-- | Integer to Number conversion
toNumber :: Int -> Number
toNumber = Int.toNumber

-- | Modulo for integers (using EuclideanRing)
wrapIndex :: Int -> Int -> Int
wrapIndex a b = Ring.mod a b

-- | Build array from function
buildArray :: forall a. Int -> (Int -> Maybe a) -> Array a
buildArray n f = buildArrayImpl 0 n f []

buildArrayImpl :: forall a. Int -> Int -> (Int -> Maybe a) -> Array a -> Array a
buildArrayImpl i n f acc =
  if i >= n then acc
  else case f i of
    Nothing -> buildArrayImpl (i + 1) n f acc
    Just x -> buildArrayImpl (i + 1) n f (snoc acc x)

-- | Initial bounding box (will be overwritten by first real bounds)
initialBounds :: { minX :: Number, minY :: Number, maxX :: Number, maxY :: Number }
initialBounds = 
  { minX: 1.0e308
  , minY: 1.0e308
  , maxX: negate 1.0e308
  , maxY: negate 1.0e308
  }

-- | Merge two bounding boxes
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
