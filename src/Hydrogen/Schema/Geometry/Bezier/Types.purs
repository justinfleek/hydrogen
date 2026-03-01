-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // schema // geometry // bezier // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Bezier Types — Core type definitions for quadratic and cubic Bezier curves.
-- |
-- | ## Overview
-- |
-- | This module defines the foundational types for Bezier curves:
-- | - **QuadBezier**: 3 control points (P0, P1, P2)
-- | - **CubicBezier**: 4 control points (P0, P1, P2, P3)
-- |
-- | Also provides constructors, accessors, and internal helpers used across
-- | all Bezier operations.
-- |
-- | ## Mathematical Foundation
-- |
-- | Quadratic: B(t) = (1-t)²P0 + 2(1-t)tP1 + t²P2
-- | Cubic:     B(t) = (1-t)³P0 + 3(1-t)²tP1 + 3(1-t)t²P2 + t³P3
-- |
-- | Parameter t ∈ [0, 1] traces the curve from start to end.

module Hydrogen.Schema.Geometry.Bezier.Types
  ( -- * Quadratic Bezier
    QuadBezier(QuadBezier)
  , quadBezier
  
  -- * Cubic Bezier
  , CubicBezier(CubicBezier)
  , cubicBezier
  
  -- * Accessors
  , quadStart
  , quadControl
  , quadEnd
  , cubicStart
  , cubicControl1
  , cubicControl2
  , cubicEnd
  
  -- * Internal Helpers (re-exported for submodules)
  , clamp01
  , epsilon
  , quadPointAtX
  , quadPointAtY
  , cubicExtrema
  , foldExtrema
  , getX
  , getY
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

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
  , (&&)
  , negate
  )

import Data.Number (sqrt)
import Data.Array (foldl)

import Hydrogen.Schema.Geometry.Point (Point2D(Point2D), point2D)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // quadratic bezier
-- ═════════════════════════════════════════════════════════════════════════════

-- | Quadratic Bezier curve with 3 control points.
-- |
-- | P0 = start point (on curve)
-- | P1 = control point (off curve, defines tangent)
-- | P2 = end point (on curve)
newtype QuadBezier = QuadBezier
  { p0 :: Point2D
  , p1 :: Point2D
  , p2 :: Point2D
  }

derive instance eqQuadBezier :: Eq QuadBezier

instance showQuadBezier :: Show QuadBezier where
  show (QuadBezier b) = "(QuadBezier p0:" <> show b.p0 
    <> " p1:" <> show b.p1 
    <> " p2:" <> show b.p2 <> ")"

-- | Create a quadratic Bezier curve
quadBezier :: Point2D -> Point2D -> Point2D -> QuadBezier
quadBezier p0 p1 p2 = QuadBezier { p0, p1, p2 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // cubic bezier
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cubic Bezier curve with 4 control points.
-- |
-- | P0 = start point (on curve)
-- | P1 = first control point (defines start tangent)
-- | P2 = second control point (defines end tangent)
-- | P3 = end point (on curve)
-- |
-- | This is the standard form used in SVG paths and CSS animations.
newtype CubicBezier = CubicBezier
  { p0 :: Point2D
  , p1 :: Point2D
  , p2 :: Point2D
  , p3 :: Point2D
  }

derive instance eqCubicBezier :: Eq CubicBezier

instance showCubicBezier :: Show CubicBezier where
  show (CubicBezier b) = "(CubicBezier p0:" <> show b.p0 
    <> " p1:" <> show b.p1 
    <> " p2:" <> show b.p2 
    <> " p3:" <> show b.p3 <> ")"

-- | Create a cubic Bezier curve
cubicBezier :: Point2D -> Point2D -> Point2D -> Point2D -> CubicBezier
cubicBezier p0 p1 p2 p3 = CubicBezier { p0, p1, p2, p3 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get start point of quadratic Bezier
quadStart :: QuadBezier -> Point2D
quadStart (QuadBezier b) = b.p0

-- | Get control point of quadratic Bezier
quadControl :: QuadBezier -> Point2D
quadControl (QuadBezier b) = b.p1

-- | Get end point of quadratic Bezier
quadEnd :: QuadBezier -> Point2D
quadEnd (QuadBezier b) = b.p2

-- | Get start point of cubic Bezier
cubicStart :: CubicBezier -> Point2D
cubicStart (CubicBezier b) = b.p0

-- | Get first control point of cubic Bezier
cubicControl1 :: CubicBezier -> Point2D
cubicControl1 (CubicBezier b) = b.p1

-- | Get second control point of cubic Bezier
cubicControl2 :: CubicBezier -> Point2D
cubicControl2 (CubicBezier b) = b.p2

-- | Get end point of cubic Bezier
cubicEnd :: CubicBezier -> Point2D
cubicEnd (CubicBezier b) = b.p3

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // internal helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp value to [0, 1]
clamp01 :: Number -> Number
clamp01 n
  | n < 0.0 = 0.0
  | n > 1.0 = 1.0
  | true = n

-- | Small value for numerical comparisons
epsilon :: Number
epsilon = 0.0000001

-- | Evaluate quadratic at t for single axis
quadPointAtX :: Number -> Number -> Number -> Number -> Number
quadPointAtX t p0 p1 p2 =
  let mt = 1.0 - t
  in mt * mt * p0 + 2.0 * mt * t * p1 + t * t * p2

quadPointAtY :: Number -> Number -> Number -> Number -> Number
quadPointAtY = quadPointAtX

-- | Find t values where cubic derivative is zero (extrema).
-- |
-- | Solves: 3(1-t)²(P1-P0) + 6(1-t)t(P2-P1) + 3t²(P3-P2) = 0
-- | Simplifies to quadratic: at² + bt + c = 0
cubicExtrema :: Number -> Number -> Number -> Number -> Array Number
cubicExtrema p0 p1 p2 p3 =
  let
    -- Coefficients of derivative
    c0 = p1 - p0
    c1 = p2 - p1
    c2 = p3 - p2
    
    -- Quadratic coefficients: at² + bt + c = 0
    a = c0 - 2.0 * c1 + c2
    b = 2.0 * (c1 - c0)
    c = c0
    
    discriminant = b * b - 4.0 * a * c
  in
    if a == 0.0 then
      -- Linear case
      if b == 0.0 then []
      else 
        let t = negate c / b
        in if t > 0.0 && t < 1.0 then [t] else []
    else if discriminant < 0.0 then
      -- No real roots
      []
    else if discriminant == 0.0 then
      -- One root
      let t = negate b / (2.0 * a)
      in if t > 0.0 && t < 1.0 then [t] else []
    else
      -- Two roots
      let
        sqrtD = sqrt discriminant
        t1 = (negate b - sqrtD) / (2.0 * a)
        t2 = (negate b + sqrtD) / (2.0 * a)
        valid1 = t1 > 0.0 && t1 < 1.0
        valid2 = t2 > 0.0 && t2 < 1.0
      in
        if valid1 && valid2 then [t1, t2]
        else if valid1 then [t1]
        else if valid2 then [t2]
        else []

-- | Fold extrema into bounds
foldExtrema 
  :: (Number -> Number -> Number) 
  -> Number 
  -> Array Number 
  -> CubicBezier 
  -> (Point2D -> Number) 
  -> Number
foldExtrema f initial ts curve accessor =
  foldl (\acc t -> f acc (accessor (cubicPointAtInternal t curve))) initial ts

-- | Internal cubic point evaluation for foldExtrema
cubicPointAtInternal :: Number -> CubicBezier -> Point2D
cubicPointAtInternal t (CubicBezier b) =
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

-- | Get X coordinate from Point2D
getX :: Point2D -> Number
getX (Point2D p) = p.x

-- | Get Y coordinate from Point2D
getY :: Point2D -> Number
getY (Point2D p) = p.y
