-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // geometry // bezier // geometry
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Bezier Geometry — Bounding boxes, arc length, and curvature.
-- |
-- | ## Overview
-- |
-- | This module provides geometric analysis functions for Bezier curves:
-- | - **Bounding Box**: Axis-aligned bounds by finding curve extrema
-- | - **Arc Length**: Numerical integration via Gaussian quadrature
-- | - **Curvature**: Signed curvature at any parameter value
-- |
-- | ## Bounding Box Algorithm
-- |
-- | For tight bounds, we find where the derivative equals zero on each axis.
-- | - Quadratic: Linear derivative, at most one extremum per axis
-- | - Cubic: Quadratic derivative, at most two extrema per axis
-- |
-- | ## Arc Length
-- |
-- | Bezier arc length has no closed-form solution (except degenerate cases).
-- | We use 5-point Gaussian quadrature which provides O(h^10) accuracy.
-- |
-- | ## Curvature
-- |
-- | Curvature κ = (x'y'' - y'x'') / (x'² + y'²)^(3/2)
-- | Positive = counter-clockwise bend, Negative = clockwise bend

module Hydrogen.Schema.Geometry.Bezier.Geometry
  ( -- * Bounding Box
    quadBoundingBox
  , cubicBoundingBox
  
  -- * Arc Length
  , quadLength
  , cubicLength
  
  -- * Curvature
  , quadCurvatureAt
  , cubicCurvatureAt
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (+)
  , (-)
  , (*)
  , (/)
  , (==)
  , (<)
  , (>)
  , (&&)
  , negate
  , min
  , max
  )

import Data.Number (sqrt)
import Data.Array (foldl)

import Hydrogen.Schema.Geometry.Point (Point2D(Point2D))
import Hydrogen.Schema.Geometry.Vector (magnitude2)

import Hydrogen.Schema.Geometry.Bezier.Types
  ( QuadBezier(QuadBezier)
  , CubicBezier(CubicBezier)
  , clamp01
  , epsilon
  , quadPointAtX
  , quadPointAtY
  , cubicExtrema
  , foldExtrema
  , getX
  , getY
  )

import Hydrogen.Schema.Geometry.Bezier.Evaluation
  ( quadTangentAt
  , cubicTangentAt
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // bounding box
-- ═════════════════════════════════════════════════════════════════════════════

-- | Axis-aligned bounding box for quadratic Bezier.
-- |
-- | Finds extrema by solving B'(t) = 0 for each axis.
quadBoundingBox :: QuadBezier -> { minX :: Number, minY :: Number, maxX :: Number, maxY :: Number }
quadBoundingBox (QuadBezier b) =
  let
    (Point2D p0) = b.p0
    (Point2D p1) = b.p1
    (Point2D p2) = b.p2
    
    -- Start with endpoints
    minX0 = min p0.x p2.x
    maxX0 = max p0.x p2.x
    minY0 = min p0.y p2.y
    maxY0 = max p0.y p2.y
    
    -- Find t where derivative is zero for each axis
    -- B'(t) = 2[(1-t)(P1-P0) + t(P2-P1)] = 0
    -- Solving: t = (P0-P1) / (P0 - 2P1 + P2)
    
    -- X axis extremum
    denomX = p0.x - 2.0 * p1.x + p2.x
    tX = if denomX == 0.0 then (-1.0) else (p0.x - p1.x) / denomX
    extremeX = if tX > 0.0 && tX < 1.0
      then quadPointAtX tX p0.x p1.x p2.x
      else p0.x  -- dummy, won't affect bounds
    
    -- Y axis extremum  
    denomY = p0.y - 2.0 * p1.y + p2.y
    tY = if denomY == 0.0 then (-1.0) else (p0.y - p1.y) / denomY
    extremeY = if tY > 0.0 && tY < 1.0
      then quadPointAtY tY p0.y p1.y p2.y
      else p0.y
    
    -- Expand bounds if extrema are within curve
    minX1 = if tX > 0.0 && tX < 1.0 then min minX0 extremeX else minX0
    maxX1 = if tX > 0.0 && tX < 1.0 then max maxX0 extremeX else maxX0
    minY1 = if tY > 0.0 && tY < 1.0 then min minY0 extremeY else minY0
    maxY1 = if tY > 0.0 && tY < 1.0 then max maxY0 extremeY else maxY0
  in
    { minX: minX1, minY: minY1, maxX: maxX1, maxY: maxY1 }

-- | Axis-aligned bounding box for cubic Bezier.
-- |
-- | Finds extrema by solving the quadratic B'(t) = 0 for each axis.
cubicBoundingBox :: CubicBezier -> { minX :: Number, minY :: Number, maxX :: Number, maxY :: Number }
cubicBoundingBox curve@(CubicBezier b) =
  let
    (Point2D p0) = b.p0
    (Point2D p3) = b.p3
    
    -- Start with endpoints
    minX0 = min p0.x p3.x
    maxX0 = max p0.x p3.x
    minY0 = min p0.y p3.y
    maxY0 = max p0.y p3.y
    
    -- X axis extrema
    (Point2D p1) = b.p1
    (Point2D p2) = b.p2
    xExtrema = cubicExtrema p0.x p1.x p2.x p3.x
    minX1 = foldExtrema min minX0 xExtrema curve getX
    maxX1 = foldExtrema max maxX0 xExtrema curve getX
    
    -- Y axis extrema
    yExtrema = cubicExtrema p0.y p1.y p2.y p3.y
    minY1 = foldExtrema min minY0 yExtrema curve getY
    maxY1 = foldExtrema max maxY0 yExtrema curve getY
  in
    { minX: minX1, minY: minY1, maxX: maxX1, maxY: maxY1 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // arc length
-- ═════════════════════════════════════════════════════════════════════════════

-- | Approximate arc length of quadratic Bezier.
-- |
-- | Uses Gaussian quadrature (5-point) for numerical integration.
-- | Accuracy is typically within 0.1% for well-behaved curves.
quadLength :: QuadBezier -> Number
quadLength curve =
  gaussianQuadrature5 (\t -> magnitude2 (quadTangentAt t curve)) 0.0 1.0

-- | Approximate arc length of cubic Bezier.
-- |
-- | Uses Gaussian quadrature (5-point) for numerical integration.
cubicLength :: CubicBezier -> Number
cubicLength curve =
  gaussianQuadrature5 (\t -> magnitude2 (cubicTangentAt t curve)) 0.0 1.0

-- | 5-point Gaussian quadrature for numerical integration.
-- |
-- | Integrates f over [a, b] using Legendre-Gauss weights.
-- | This provides O(h^10) accuracy for smooth functions.
gaussianQuadrature5 :: (Number -> Number) -> Number -> Number -> Number
gaussianQuadrature5 f a b =
  let
    -- Gauss-Legendre nodes and weights for n=5
    -- Nodes are roots of P_5(x) on [-1, 1]
    nodes = 
      [ { x: 0.0, w: 0.5688888888888889 }
      , { x: 0.5384693101056831, w: 0.47862867049936647 }
      , { x: (-0.5384693101056831), w: 0.47862867049936647 }
      , { x: 0.9061798459386640, w: 0.23692688505618908 }
      , { x: (-0.9061798459386640), w: 0.23692688505618908 }
      ]
    
    -- Transform from [-1, 1] to [a, b]
    halfWidth = (b - a) / 2.0
    midpoint = (a + b) / 2.0
    
    -- Sum weighted function evaluations
    sumTerms = foldl (\acc node -> 
      let t = midpoint + halfWidth * node.x
      in acc + node.w * f t
    ) 0.0 nodes
  in
    halfWidth * sumTerms

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // curvature
-- ═════════════════════════════════════════════════════════════════════════════

-- | Signed curvature at parameter t for quadratic Bezier.
-- |
-- | Curvature κ = (x'y'' - y'x'') / (x'² + y'²)^(3/2)
-- | Positive = counter-clockwise, Negative = clockwise
-- |
-- | Returns 0 if tangent magnitude is near zero (degenerate case).
quadCurvatureAt :: Number -> QuadBezier -> Number
quadCurvatureAt t (QuadBezier b) =
  let
    t' = clamp01 t
    
    (Point2D p0) = b.p0
    (Point2D p1) = b.p1
    (Point2D p2) = b.p2
    
    -- First derivative (tangent)
    -- B'(t) = 2[(1-t)(P1-P0) + t(P2-P1)]
    mt = 1.0 - t'
    dx = 2.0 * (mt * (p1.x - p0.x) + t' * (p2.x - p1.x))
    dy = 2.0 * (mt * (p1.y - p0.y) + t' * (p2.y - p1.y))
    
    -- Second derivative (constant for quadratic)
    -- B''(t) = 2(P0 - 2P1 + P2)
    ddx = 2.0 * (p0.x - 2.0 * p1.x + p2.x)
    ddy = 2.0 * (p0.y - 2.0 * p1.y + p2.y)
    
    -- Curvature formula
    cross = dx * ddy - dy * ddx
    speedSq = dx * dx + dy * dy
    speed = sqrt speedSq
    speedCubed = speedSq * speed
  in
    if speedCubed < epsilon then 0.0
    else cross / speedCubed

-- | Signed curvature at parameter t for cubic Bezier.
-- |
-- | Returns 0 if tangent magnitude is near zero.
cubicCurvatureAt :: Number -> CubicBezier -> Number
cubicCurvatureAt t (CubicBezier b) =
  let
    t' = clamp01 t
    mt = 1.0 - t'
    
    (Point2D p0) = b.p0
    (Point2D p1) = b.p1
    (Point2D p2) = b.p2
    (Point2D p3) = b.p3
    
    -- Derivative control points
    c0x = p1.x - p0.x
    c0y = p1.y - p0.y
    c1x = p2.x - p1.x
    c1y = p2.y - p1.y
    c2x = p3.x - p2.x
    c2y = p3.y - p2.y
    
    -- First derivative
    -- B'(t) = 3[(1-t)²(P1-P0) + 2(1-t)t(P2-P1) + t²(P3-P2)]
    dx = 3.0 * (mt * mt * c0x + 2.0 * mt * t' * c1x + t' * t' * c2x)
    dy = 3.0 * (mt * mt * c0y + 2.0 * mt * t' * c1y + t' * t' * c2y)
    
    -- Second derivative
    -- B''(t) = 6[(1-t)(P0-2P1+P2) + t(P1-2P2+P3)]
    d0x = p0.x - 2.0 * p1.x + p2.x
    d0y = p0.y - 2.0 * p1.y + p2.y
    d1x = p1.x - 2.0 * p2.x + p3.x
    d1y = p1.y - 2.0 * p2.y + p3.y
    
    ddx = 6.0 * (mt * d0x + t' * d1x)
    ddy = 6.0 * (mt * d0y + t' * d1y)
    
    -- Curvature
    cross = dx * ddy - dy * ddx
    speedSq = dx * dx + dy * dy
    speed = sqrt speedSq
    speedCubed = speedSq * speed
  in
    if speedCubed < epsilon then 0.0
    else cross / speedCubed
