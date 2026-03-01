-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // nurbs // evaluation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Evaluation functions for NURBS curves.
-- |
-- | ## Overview
-- |
-- | This module provides functions to evaluate NURBS curves:
-- | - Point evaluation at parameter u
-- | - Tangent vector at parameter u
-- | - Normal vector at parameter u
-- | - Curvature at parameter u
-- |
-- | ## Mathematical Foundation
-- |
-- | Point evaluation uses de Boor's algorithm for numerical stability.
-- | Derivatives are computed via numerical differentiation.
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Geometry.Point (Point2D)
-- | - Hydrogen.Schema.Geometry.Vector (Vector2D)
-- | - Hydrogen.Schema.Geometry.Nurbs.Types (NurbsCurve)

module Hydrogen.Schema.Geometry.Nurbs.Evaluation
  ( -- * Point Evaluation
    nurbsPointAt
  
  -- * Derivatives
  , nurbsTangentAt
  , nurbsNormalAt
  , nurbsCurvatureAt
  
  -- * Parameter Range
  , nurbsParameterRange
  
  -- * Sampling
  , sampleNurbs
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
  , (<=)
  , max
  , min
  )

import Data.Maybe (Maybe(Just))
import Data.Number (sqrt)

import Hydrogen.Schema.Geometry.Point (Point2D(Point2D))
import Hydrogen.Schema.Geometry.Vector (Vector2D, vec2, normalize2, perpendicular2)
import Hydrogen.Schema.Geometry.Nurbs.Types 
  ( NurbsCurve(NurbsCurve)
  , nurbsKnots
  , nurbsDegree
  , nurbsControlPoints
  )
import Hydrogen.Schema.Geometry.Nurbs.Internal
  ( nurbsParamRange
  , findKnotSpan
  , deBoorRational
  , clampNumber
  , absNum
  , epsilon
  , toNumber
  , buildArray
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // point evaluation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Evaluate NURBS curve at parameter u.
-- |
-- | Parameter u should be within the valid parameter range (see nurbsParameterRange).
-- | Uses de Boor's algorithm for numerical stability.
nurbsPointAt :: Number -> NurbsCurve -> Point2D
nurbsPointAt u (NurbsCurve c) =
  let
    -- Clamp u to valid range
    range = nurbsParamRange c.knots c.degree
    u' = clampNumber range.start range.end u
    
    -- Find knot span
    span = findKnotSpan u' c.knots c.degree
    
    -- Evaluate using de Boor's algorithm with rational weights
    result = deBoorRational u' span c.degree c.controlPoints c.knots
  in
    result

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // derivatives
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tangent vector at parameter u.
-- |
-- | Computed via numerical differentiation for stability.
nurbsTangentAt :: Number -> NurbsCurve -> Vector2D
nurbsTangentAt u curve =
  let
    h = 0.0001
    range = nurbsParameterRange curve
    u1 = max range.start (u - h)
    u2 = min range.end (u + h)
    actualH = (u2 - u1) / 2.0
    
    (Point2D p1) = nurbsPointAt u1 curve
    (Point2D p2) = nurbsPointAt u2 curve
    
    dx = (p2.x - p1.x) / (2.0 * actualH)
    dy = (p2.y - p1.y) / (2.0 * actualH)
  in
    vec2 dx dy

-- | Normal vector at parameter u (perpendicular to tangent).
nurbsNormalAt :: Number -> NurbsCurve -> Vector2D
nurbsNormalAt u curve =
  let tangent = nurbsTangentAt u curve
  in perpendicular2 (normalize2 tangent)

-- | Curvature at parameter u.
-- |
-- | κ = |T'(u)| where T is the unit tangent.
-- | Computed via second-order numerical differentiation.
nurbsCurvatureAt :: Number -> NurbsCurve -> Number
nurbsCurvatureAt u curve =
  let
    h = 0.0001
    range = nurbsParameterRange curve
    u0 = clampNumber range.start range.end (u - h)
    u1 = clampNumber range.start range.end u
    u2 = clampNumber range.start range.end (u + h)
    
    (Point2D p0) = nurbsPointAt u0 curve
    (Point2D p1) = nurbsPointAt u1 curve
    (Point2D p2) = nurbsPointAt u2 curve
    
    -- First derivatives
    dx1 = (p1.x - p0.x) / h
    dy1 = (p1.y - p0.y) / h
    dx2 = (p2.x - p1.x) / h
    dy2 = (p2.y - p1.y) / h
    
    -- Second derivatives
    ddx = (dx2 - dx1) / h
    ddy = (dy2 - dy1) / h
    
    -- Average first derivative at u
    dx = (dx1 + dx2) / 2.0
    dy = (dy1 + dy2) / 2.0
    
    -- Curvature formula: κ = |x'y'' - y'x''| / (x'² + y'²)^(3/2)
    cross = dx * ddy - dy * ddx
    speedSq = dx * dx + dy * dy
    speed = sqrt speedSq
    speedCubed = speedSq * speed
  in
    if speedCubed < epsilon then 0.0
    else absNum cross / speedCubed

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // parameter range
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get valid parameter range for NURBS curve.
-- |
-- | For clamped NURBS, this is typically [0, 1] or [knots[p], knots[n]].
nurbsParameterRange :: NurbsCurve -> { start :: Number, end :: Number }
nurbsParameterRange curve = 
  nurbsParamRange (nurbsKnots curve) (nurbsDegree curve)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // sampling
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sample NURBS curve at n evenly-spaced parameter values.
-- |
-- | Returns n+1 points from start to end of parameter range.
sampleNurbs :: Int -> NurbsCurve -> Array Point2D
sampleNurbs n curve =
  if n <= 0 then []
  else
    let range = nurbsParameterRange curve
    in buildArray (n + 1) (\i ->
      let 
        t = toNumber i / toNumber n
        u = range.start + t * (range.end - range.start)
      in Just (nurbsPointAt u curve)
    )
