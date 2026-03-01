-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // geometry // bezier // evaluation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Bezier Evaluation — Point evaluation, tangents, and subdivision.
-- |
-- | ## Overview
-- |
-- | This module provides functions for evaluating Bezier curves at any
-- | parameter value t ∈ [0, 1], computing tangent vectors, and subdividing
-- | curves into smaller segments.
-- |
-- | All evaluation uses the De Casteljau algorithm for numerical stability.
-- |
-- | ## De Casteljau Algorithm
-- |
-- | Rather than directly computing the polynomial form, De Casteljau 
-- | recursively linearly interpolates between control points. This approach:
-- | - Is numerically stable even for extreme t values
-- | - Naturally provides subdivision as a byproduct
-- | - Is geometrically intuitive

module Hydrogen.Schema.Geometry.Bezier.Evaluation
  ( -- * Point Evaluation
    quadPointAt
  , cubicPointAt
  
  -- * Tangent Vectors
  , quadTangentAt
  , cubicTangentAt
  
  -- * Subdivision
  , quadSplitAt
  , cubicSplitAt
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (+)
  , (-)
  , (*)
  )

import Hydrogen.Schema.Geometry.Point (Point2D(Point2D), point2D)
import Hydrogen.Schema.Geometry.Vector (Vector2D, vec2)

import Hydrogen.Schema.Geometry.Bezier.Types
  ( QuadBezier(QuadBezier)
  , CubicBezier(CubicBezier)
  , quadBezier
  , cubicBezier
  , clamp01
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // point evaluation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Evaluate quadratic Bezier at parameter t ∈ [0, 1].
-- |
-- | Uses De Casteljau algorithm for numerical stability.
-- | B(t) = (1-t)²P0 + 2(1-t)tP1 + t²P2
quadPointAt :: Number -> QuadBezier -> Point2D
quadPointAt t (QuadBezier b) =
  let
    t' = clamp01 t
    mt = 1.0 - t'
    
    -- De Casteljau: linear interpolation at each level
    -- Level 1: interpolate between adjacent control points
    (Point2D p0) = b.p0
    (Point2D p1) = b.p1
    (Point2D p2) = b.p2
    
    q0x = mt * p0.x + t' * p1.x
    q0y = mt * p0.y + t' * p1.y
    q1x = mt * p1.x + t' * p2.x
    q1y = mt * p1.y + t' * p2.y
    
    -- Level 2: interpolate between level 1 points
    rx = mt * q0x + t' * q1x
    ry = mt * q0y + t' * q1y
  in
    point2D rx ry

-- | Evaluate cubic Bezier at parameter t ∈ [0, 1].
-- |
-- | Uses De Casteljau algorithm for numerical stability.
-- | B(t) = (1-t)³P0 + 3(1-t)²tP1 + 3(1-t)t²P2 + t³P3
cubicPointAt :: Number -> CubicBezier -> Point2D
cubicPointAt t (CubicBezier b) =
  let
    t' = clamp01 t
    mt = 1.0 - t'
    
    (Point2D p0) = b.p0
    (Point2D p1) = b.p1
    (Point2D p2) = b.p2
    (Point2D p3) = b.p3
    
    -- Level 1
    q0x = mt * p0.x + t' * p1.x
    q0y = mt * p0.y + t' * p1.y
    q1x = mt * p1.x + t' * p2.x
    q1y = mt * p1.y + t' * p2.y
    q2x = mt * p2.x + t' * p3.x
    q2y = mt * p2.y + t' * p3.y
    
    -- Level 2
    r0x = mt * q0x + t' * q1x
    r0y = mt * q0y + t' * q1y
    r1x = mt * q1x + t' * q2x
    r1y = mt * q1y + t' * q2y
    
    -- Level 3 (final point)
    sx = mt * r0x + t' * r1x
    sy = mt * r0y + t' * r1y
  in
    point2D sx sy

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // tangent vectors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tangent vector at parameter t for quadratic Bezier.
-- |
-- | The derivative of a quadratic Bezier is a linear function:
-- | B'(t) = 2(1-t)(P1-P0) + 2t(P2-P1)
quadTangentAt :: Number -> QuadBezier -> Vector2D
quadTangentAt t (QuadBezier b) =
  let
    t' = clamp01 t
    mt = 1.0 - t'
    
    (Point2D p0) = b.p0
    (Point2D p1) = b.p1
    (Point2D p2) = b.p2
    
    -- Derivative coefficients
    dx = 2.0 * (mt * (p1.x - p0.x) + t' * (p2.x - p1.x))
    dy = 2.0 * (mt * (p1.y - p0.y) + t' * (p2.y - p1.y))
  in
    vec2 dx dy

-- | Tangent vector at parameter t for cubic Bezier.
-- |
-- | The derivative of a cubic Bezier is a quadratic function:
-- | B'(t) = 3(1-t)²(P1-P0) + 6(1-t)t(P2-P1) + 3t²(P3-P2)
cubicTangentAt :: Number -> CubicBezier -> Vector2D
cubicTangentAt t (CubicBezier b) =
  let
    t' = clamp01 t
    mt = 1.0 - t'
    
    (Point2D p0) = b.p0
    (Point2D p1) = b.p1
    (Point2D p2) = b.p2
    (Point2D p3) = b.p3
    
    -- Derivative coefficients
    c0x = p1.x - p0.x
    c0y = p1.y - p0.y
    c1x = p2.x - p1.x
    c1y = p2.y - p1.y
    c2x = p3.x - p2.x
    c2y = p3.y - p2.y
    
    dx = 3.0 * (mt * mt * c0x + 2.0 * mt * t' * c1x + t' * t' * c2x)
    dy = 3.0 * (mt * mt * c0y + 2.0 * mt * t' * c1y + t' * t' * c2y)
  in
    vec2 dx dy

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // subdivision
-- ═════════════════════════════════════════════════════════════════════════════

-- | Split quadratic Bezier at parameter t into two curves.
-- |
-- | Uses De Casteljau algorithm — the intermediate points from evaluation
-- | become the control points of the two resulting curves.
quadSplitAt :: Number -> QuadBezier -> { left :: QuadBezier, right :: QuadBezier }
quadSplitAt t (QuadBezier b) =
  let
    t' = clamp01 t
    mt = 1.0 - t'
    
    (Point2D p0) = b.p0
    (Point2D p1) = b.p1
    (Point2D p2) = b.p2
    
    -- Level 1 points
    q0 = point2D (mt * p0.x + t' * p1.x) (mt * p0.y + t' * p1.y)
    q1 = point2D (mt * p1.x + t' * p2.x) (mt * p1.y + t' * p2.y)
    
    -- Level 2 point (the split point)
    (Point2D q0') = q0
    (Point2D q1') = q1
    r = point2D (mt * q0'.x + t' * q1'.x) (mt * q0'.y + t' * q1'.y)
  in
    { left: quadBezier b.p0 q0 r
    , right: quadBezier r q1 b.p2
    }

-- | Split cubic Bezier at parameter t into two curves.
-- |
-- | Uses De Casteljau algorithm.
cubicSplitAt :: Number -> CubicBezier -> { left :: CubicBezier, right :: CubicBezier }
cubicSplitAt t (CubicBezier b) =
  let
    t' = clamp01 t
    mt = 1.0 - t'
    
    (Point2D p0) = b.p0
    (Point2D p1) = b.p1
    (Point2D p2) = b.p2
    (Point2D p3) = b.p3
    
    -- Level 1 points
    q0 = point2D (mt * p0.x + t' * p1.x) (mt * p0.y + t' * p1.y)
    q1 = point2D (mt * p1.x + t' * p2.x) (mt * p1.y + t' * p2.y)
    q2 = point2D (mt * p2.x + t' * p3.x) (mt * p2.y + t' * p3.y)
    
    -- Level 2 points
    (Point2D q0') = q0
    (Point2D q1') = q1
    (Point2D q2') = q2
    r0 = point2D (mt * q0'.x + t' * q1'.x) (mt * q0'.y + t' * q1'.y)
    r1 = point2D (mt * q1'.x + t' * q2'.x) (mt * q1'.y + t' * q2'.y)
    
    -- Level 3 point (the split point)
    (Point2D r0') = r0
    (Point2D r1') = r1
    s = point2D (mt * r0'.x + t' * r1'.x) (mt * r0'.y + t' * r1'.y)
  in
    { left: cubicBezier b.p0 q0 r0 s
    , right: cubicBezier s r1 q2 b.p3
    }
