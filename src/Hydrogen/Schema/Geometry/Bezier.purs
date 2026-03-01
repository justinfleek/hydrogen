-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // geometry // bezier
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Bezier — Quadratic and cubic Bezier curves.
-- |
-- | ## Design Philosophy
-- |
-- | Bezier curves are the mathematical foundation for smooth motion in digital
-- | systems. Every animation, easing function, and path is built on them.
-- |
-- | Two variants are provided:
-- | - **QuadBezier**: 3 control points (P0, P1, P2) — simpler, cheaper
-- | - **CubicBezier**: 4 control points (P0, P1, P2, P3) — more flexible, standard
-- |
-- | Both use the De Casteljau algorithm for evaluation and subdivision.
-- |
-- | ## Mathematical Foundation
-- |
-- | Quadratic: B(t) = (1-t)²P0 + 2(1-t)tP1 + t²P2
-- | Cubic:     B(t) = (1-t)³P0 + 3(1-t)²tP1 + 3(1-t)t²P2 + t³P3
-- |
-- | Parameter t ∈ [0, 1] traces the curve from start to end.
-- |
-- | ## Use Cases
-- |
-- | - Animation easing curves (CSS cubic-bezier)
-- | - Path segments in vector graphics
-- | - Motion trajectories for agents
-- | - Smooth interpolation between states
-- | - Font glyph outlines
-- |
-- | ## Module Structure
-- |
-- | This leader module re-exports from:
-- | - `Bezier.Types`: Core types and constructors
-- | - `Bezier.Evaluation`: Point evaluation, tangents, subdivision
-- | - `Bezier.Geometry`: Bounding box, arc length, curvature
-- | - `Bezier.HitTest`: Closest point and distance calculations
-- | - `Bezier.Easing`: Common animation easing curves
-- |
-- | ## Dependencies
-- |
-- | - Schema.Geometry.Point (Point2D for control points)
-- | - Schema.Geometry.Vector (tangent vectors)

module Hydrogen.Schema.Geometry.Bezier
  ( -- * Types and Constructors
    module Types
    
  -- * Evaluation
  , module Evaluation
  
  -- * Geometry
  , module Geometry
  
  -- * Hit Testing
  , module HitTest
  
  -- * Easing Curves
  , module Easing
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Geometry.Bezier.Types
  ( QuadBezier(QuadBezier)
  , quadBezier
  , CubicBezier(CubicBezier)
  , cubicBezier
  , quadStart
  , quadControl
  , quadEnd
  , cubicStart
  , cubicControl1
  , cubicControl2
  , cubicEnd
  ) as Types

import Hydrogen.Schema.Geometry.Bezier.Evaluation
  ( quadPointAt
  , cubicPointAt
  , quadTangentAt
  , cubicTangentAt
  , quadSplitAt
  , cubicSplitAt
  ) as Evaluation

import Hydrogen.Schema.Geometry.Bezier.Geometry
  ( quadBoundingBox
  , cubicBoundingBox
  , quadLength
  , cubicLength
  , quadCurvatureAt
  , cubicCurvatureAt
  ) as Geometry

import Hydrogen.Schema.Geometry.Bezier.HitTest
  ( quadClosestParameter
  , cubicClosestParameter
  , quadDistanceToPoint
  , cubicDistanceToPoint
  ) as HitTest

import Hydrogen.Schema.Geometry.Bezier.Easing
  ( easeLinear
  , easeInQuad
  , easeOutQuad
  , easeInOutQuad
  , easeInCubic
  , easeOutCubic
  , easeInOutCubic
  ) as Easing
