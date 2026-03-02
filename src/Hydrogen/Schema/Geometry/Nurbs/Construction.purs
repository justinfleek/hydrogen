-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // nurbs // construction
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Construction functions for NURBS curves.
-- |
-- | ## Overview
-- |
-- | This module provides various ways to create NURBS curves:
-- | - From explicit control points and knot vectors
-- | - From unweighted points with uniform knots
-- | - Standard shapes: circles, arcs, ellipses
-- |
-- | ## Mathematical Notes
-- |
-- | For a NURBS curve of degree p with n control points:
-- | - Knot vector must have exactly n + p + 1 values
-- | - Knot vector must be non-decreasing
-- | - All weights must be positive
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Geometry.Point (Point2D)
-- | - Hydrogen.Schema.Geometry.Nurbs.Types (ControlPoint, NurbsCurve)
-- | - Hydrogen.Schema.Geometry.Nurbs.Internal (validation helpers)

module Hydrogen.Schema.Geometry.Nurbs.Construction
  ( -- * Primary Constructors
    nurbsCurve
  , nurbsFromPoints
  
  -- * Standard Shapes
  , nurbsCircle
  , nurbsArc
  , nurbsEllipse
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (+)
  , (-)
  , (*)
  , (/)
  , (<=)
  , (>=)
  , (==)
  , (&&)
  , negate
  , map
  )

import Data.Array (length)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Number (sqrt, pi, cos)

import Hydrogen.Schema.Geometry.Point (Point2D, point2D)
import Hydrogen.Schema.Geometry.Nurbs.Types 
  ( ControlPoint(ControlPoint)
  , KnotVector
  , NurbsCurve(NurbsCurve)
  )
import Hydrogen.Schema.Geometry.Nurbs.Internal
  ( isNonDecreasing
  , allWeightsPositive
  , uniformKnotVector
  , buildArcControlPoints
  , buildArcKnots
  , toNumber
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // primary constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a NURBS curve with explicit knot vector.
-- |
-- | Returns Nothing if:
-- | - Fewer than degree + 1 control points
-- | - Knot vector length ≠ n + p + 1
-- | - Any weight ≤ 0
-- | - Degree < 1
nurbsCurve :: Int -> Array ControlPoint -> KnotVector -> Maybe NurbsCurve
nurbsCurve degree cps knots =
  let 
    n = length cps
    m = length knots
    requiredKnots = n + degree + 1
    validDegree = degree >= 1
    validPoints = n >= degree + 1
    validKnots = m == requiredKnots && isNonDecreasing knots
    validWeights = allWeightsPositive cps
  in
    if validDegree && validPoints && validKnots && validWeights
    then Just (NurbsCurve { controlPoints: cps, knots: knots, degree: degree })
    else Nothing

-- | Create a NURBS curve from unweighted points with uniform knot vector.
-- |
-- | All weights are set to 1.0 (equivalent to B-spline).
nurbsFromPoints :: Int -> Array Point2D -> Maybe NurbsCurve
nurbsFromPoints degree pts =
  let 
    cps = map (\p -> ControlPoint { position: p, weight: 1.0 }) pts
    n = length pts
    knots = uniformKnotVector n degree
  in
    nurbsCurve degree cps knots

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // standard shapes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a NURBS circle centered at origin with given radius.
-- |
-- | Uses 9 control points (degree 2) with weights for exact circle.
-- | This is the standard NURBS representation of a full circle.
nurbsCircle :: Number -> NurbsCurve
nurbsCircle radius =
  let
    -- 9 control points for full circle (degree 2)
    w = sqrt 2.0 / 2.0  -- Weight for corner points
    r = radius
    
    cps = 
      [ ControlPoint { position: point2D r 0.0, weight: 1.0 }
      , ControlPoint { position: point2D r r, weight: w }
      , ControlPoint { position: point2D 0.0 r, weight: 1.0 }
      , ControlPoint { position: point2D (negate r) r, weight: w }
      , ControlPoint { position: point2D (negate r) 0.0, weight: 1.0 }
      , ControlPoint { position: point2D (negate r) (negate r), weight: w }
      , ControlPoint { position: point2D 0.0 (negate r), weight: 1.0 }
      , ControlPoint { position: point2D r (negate r), weight: w }
      , ControlPoint { position: point2D r 0.0, weight: 1.0 }  -- Closed
      ]
    
    -- Knot vector for closed degree-2 curve with 9 points
    knots = [0.0, 0.0, 0.0, 0.25, 0.25, 0.5, 0.5, 0.75, 0.75, 1.0, 1.0, 1.0]
  in
    NurbsCurve { controlPoints: cps, knots: knots, degree: 2 }

-- | Create a NURBS arc from start angle to end angle.
-- |
-- | Angles in radians. Arc is counter-clockwise from start to end.
nurbsArc :: Number -> Number -> Number -> NurbsCurve
nurbsArc radius startAngle endAngle =
  let
    -- Compute arc span
    span = endAngle - startAngle
    
    -- For spans ≤ π/2, we can use a single quadratic segment
    -- For larger spans, we need multiple segments
    numSegments = 
      if span <= pi / 2.0 then 1
      else if span <= pi then 2
      else if span <= 3.0 * pi / 2.0 then 3
      else 4
    
    segmentAngle = span / toNumber numSegments
    halfAngle = segmentAngle / 2.0
    w = cos halfAngle  -- Weight for middle control point
    
    -- Build control points for each segment
    cps = buildArcControlPoints radius startAngle numSegments segmentAngle w []
    
    -- Uniform knot vector for the arc
    knots = buildArcKnots numSegments
  in
    NurbsCurve { controlPoints: cps, knots: knots, degree: 2 }

-- | Create a NURBS ellipse centered at origin.
-- |
-- | rx = radius along X axis, ry = radius along Y axis.
nurbsEllipse :: Number -> Number -> NurbsCurve
nurbsEllipse rx ry =
  let
    w = sqrt 2.0 / 2.0
    
    cps = 
      [ ControlPoint { position: point2D rx 0.0, weight: 1.0 }
      , ControlPoint { position: point2D rx ry, weight: w }
      , ControlPoint { position: point2D 0.0 ry, weight: 1.0 }
      , ControlPoint { position: point2D (negate rx) ry, weight: w }
      , ControlPoint { position: point2D (negate rx) 0.0, weight: 1.0 }
      , ControlPoint { position: point2D (negate rx) (negate ry), weight: w }
      , ControlPoint { position: point2D 0.0 (negate ry), weight: 1.0 }
      , ControlPoint { position: point2D rx (negate ry), weight: w }
      , ControlPoint { position: point2D rx 0.0, weight: 1.0 }
      ]
    
    knots = [0.0, 0.0, 0.0, 0.25, 0.25, 0.5, 0.5, 0.75, 0.75, 1.0, 1.0, 1.0]
  in
    NurbsCurve { controlPoints: cps, knots: knots, degree: 2 }
