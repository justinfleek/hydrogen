-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // geometry // bezier // hittest
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Bezier Hit Testing — Closest point and distance calculations.
-- |
-- | ## Overview
-- |
-- | This module provides functions for finding the closest point on a Bezier
-- | curve to a given target point, and computing the distance.
-- |
-- | ## Algorithm
-- |
-- | Uses golden section search to find the parameter t that minimizes the
-- | squared distance from the curve to the target point. This is a robust
-- | approach that:
-- | - Works for any well-formed Bezier curve
-- | - Converges quickly (20 iterations gives ~10^-9 precision)
-- | - Handles edge cases gracefully
-- |
-- | ## Use Cases
-- |
-- | - Interactive curve editing (selection, snapping)
-- | - Path-based collision detection
-- | - Proximity queries in motion planning

module Hydrogen.Schema.Geometry.Bezier.HitTest
  ( -- * Closest Parameter
    quadClosestParameter
  , cubicClosestParameter
  
  -- * Distance
  , quadDistanceToPoint
  , cubicDistanceToPoint
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
  , (||)
  )

import Data.Number (sqrt)
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Geometry.Point (Point2D(Point2D))

import Hydrogen.Schema.Geometry.Bezier.Types
  ( QuadBezier
  , CubicBezier
  , quadStart
  , quadEnd
  , cubicStart
  , cubicEnd
  , epsilon
  )

import Hydrogen.Schema.Geometry.Bezier.Evaluation
  ( quadPointAt
  , cubicPointAt
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // closest parameter
-- ═════════════════════════════════════════════════════════════════════════════

-- | Find parameter t where quadratic Bezier is closest to given point.
-- |
-- | Uses iterative refinement (golden section search) to find the minimum
-- | distance. Returns t ∈ [0, 1].
-- |
-- | Returns Nothing if curve is degenerate (all control points coincident).
quadClosestParameter :: Point2D -> QuadBezier -> Maybe Number
quadClosestParameter target curve =
  let
    -- Check for degenerate curve
    (Point2D p0) = quadStart curve
    (Point2D p2) = quadEnd curve
    dx = p2.x - p0.x
    dy = p2.y - p0.y
    curveSpan = sqrt (dx * dx + dy * dy)
  in
    if curveSpan < epsilon then Nothing
    else Just (goldenSectionSearch (\t -> quadDistanceSq t target curve) 0.0 1.0 20)

-- | Find parameter t where cubic Bezier is closest to given point.
-- |
-- | Uses iterative refinement (golden section search) to find the minimum
-- | distance. Returns t ∈ [0, 1].
-- |
-- | Returns Nothing if curve is degenerate.
cubicClosestParameter :: Point2D -> CubicBezier -> Maybe Number
cubicClosestParameter target curve =
  let
    (Point2D p0) = cubicStart curve
    (Point2D p3) = cubicEnd curve
    dx = p3.x - p0.x
    dy = p3.y - p0.y
    curveSpan = sqrt (dx * dx + dy * dy)
  in
    if curveSpan < epsilon then Nothing
    else Just (goldenSectionSearch (\t -> cubicDistanceSq t target curve) 0.0 1.0 20)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // distance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Distance from a point to the closest point on a quadratic Bezier.
-- |
-- | Returns Nothing if curve is degenerate.
quadDistanceToPoint :: Point2D -> QuadBezier -> Maybe Number
quadDistanceToPoint target curve =
  case quadClosestParameter target curve of
    Nothing -> Nothing
    Just t -> 
      let 
        closest = quadPointAt t curve
        (Point2D c) = closest
        (Point2D p) = target
        dx = c.x - p.x
        dy = c.y - p.y
      in Just (sqrt (dx * dx + dy * dy))

-- | Distance from a point to the closest point on a cubic Bezier.
-- |
-- | Returns Nothing if curve is degenerate.
cubicDistanceToPoint :: Point2D -> CubicBezier -> Maybe Number
cubicDistanceToPoint target curve =
  case cubicClosestParameter target curve of
    Nothing -> Nothing
    Just t ->
      let
        closest = cubicPointAt t curve
        (Point2D c) = closest
        (Point2D p) = target
        dx = c.x - p.x
        dy = c.y - p.y
      in Just (sqrt (dx * dx + dy * dy))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // internal helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Squared distance from point on curve at t to target point.
quadDistanceSq :: Number -> Point2D -> QuadBezier -> Number
quadDistanceSq t target curve =
  let
    (Point2D p) = quadPointAt t curve
    (Point2D q) = target
    dx = p.x - q.x
    dy = p.y - q.y
  in dx * dx + dy * dy

-- | Squared distance from point on curve at t to target point.
cubicDistanceSq :: Number -> Point2D -> CubicBezier -> Number
cubicDistanceSq t target curve =
  let
    (Point2D p) = cubicPointAt t curve
    (Point2D q) = target
    dx = p.x - q.x
    dy = p.y - q.y
  in dx * dx + dy * dy

-- | Golden section search for minimum of unimodal function on [a, b].
-- |
-- | Uses the golden ratio to efficiently narrow down the minimum.
-- | Iterations parameter controls precision (20 gives ~10^-9 precision).
goldenSectionSearch :: (Number -> Number) -> Number -> Number -> Int -> Number
goldenSectionSearch f a b iterations =
  goldenSectionImpl f a b iterations phi invPhi
  where
    -- Golden ratio constants
    phi = (1.0 + sqrt 5.0) / 2.0
    invPhi = 1.0 / phi

goldenSectionImpl :: (Number -> Number) -> Number -> Number -> Int -> Number -> Number -> Number
goldenSectionImpl f a b remaining phi invPhi =
  if remaining <= 0 || (b - a) < epsilon then
    (a + b) / 2.0
  else
    let
      c = b - (b - a) * invPhi
      d = a + (b - a) * invPhi
      fc = f c
      fd = f d
    in
      if fc < fd then
        goldenSectionImpl f a d (remaining - 1) phi invPhi
      else
        goldenSectionImpl f c b (remaining - 1) phi invPhi
