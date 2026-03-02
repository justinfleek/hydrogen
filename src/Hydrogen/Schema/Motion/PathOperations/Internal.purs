-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                    // hydrogen // schema // motion // path-operations // internal
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Internal — Shared helper functions and constants for path operations.
-- |
-- | ## Design Philosophy
-- |
-- | This module provides the foundational utilities used across all path
-- | operation submodules:
-- |
-- | - **Constants**: epsilon for floating-point comparisons
-- | - **Array builders**: Construct arrays from generator functions
-- | - **Number utilities**: Clamping, floor, truncation
-- | - **Geometry helpers**: Point-to-line distance, angle computation
-- |
-- | ## Dependencies
-- |
-- | - Schema.Geometry.Point (Point2D)

module Hydrogen.Schema.Motion.PathOperations.Internal
  ( -- * Constants
    epsilon
  
  -- * Array Building
  , buildArray
  , buildIntArray
  , buildIntRange
  
  -- * Number Utilities
  , clamp01
  , floorInt
  , truncateToInt
  , mod
  
  -- * Geometry Helpers
  , pointToLineDistance
  , computeAngle
  , computeCurvatures
  , sumSegmentLengths
  , pointAtArcLength
  , findPointAtLength
  , computeNormalAt
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
  , (==)
  , (||)
  , otherwise
  , negate
  , max
  , min
  )

import Data.Array (length, index, snoc, last, foldl)
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Data.Number (sqrt, abs, atan2, pi, floor)

import Hydrogen.Schema.Geometry.Point (Point2D(Point2D), point2D)
import Hydrogen.Schema.Geometry.Vector (Vector2D, vec2, normalize2, perpendicular2)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Small epsilon for floating-point comparisons.
epsilon :: Number
epsilon = 1.0e-10

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // array building
-- ═════════════════════════════════════════════════════════════════════════════

-- | Build array from function.
buildArray :: forall a. Int -> (Int -> Maybe a) -> Array a
buildArray n f = buildArrayImpl 0 n f []

-- | Internal implementation of buildArray.
buildArrayImpl :: forall a. Int -> Int -> (Int -> Maybe a) -> Array a -> Array a
buildArrayImpl i n f acc =
  if i >= n then acc
  else case f i of
    Nothing -> buildArrayImpl (i + 1) n f acc
    Just x -> buildArrayImpl (i + 1) n f (snoc acc x)

-- | Build integer array [0, n-1].
buildIntArray :: Int -> Array Int
buildIntArray n = buildArray n Just

-- | Build integer range [start, end].
buildIntRange :: Int -> Int -> Array Int
buildIntRange start end = 
  buildArray (max 0 (end - start + 1)) (\i -> Just (start + i))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // number utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp to [0, 1].
clamp01 :: Number -> Number
clamp01 n
  | n < 0.0 = 0.0
  | n > 1.0 = 1.0
  | otherwise = n

-- | Floor to Int.
floorInt :: Number -> Int
floorInt n = 
  let floored = floor n
  in if floored >= 0.0 then truncateToInt floored else truncateToInt floored - 1

-- | Truncate Number to Int (simple approximation).
truncateToInt :: Number -> Int
truncateToInt n = truncateImpl n 0

-- | Internal implementation of truncateToInt.
truncateImpl :: Number -> Int -> Int
truncateImpl n acc =
  if n < 1.0 then acc
  else truncateImpl (n - 1.0) (acc + 1)

-- | Integer modulo.
mod :: Int -> Int -> Int
mod a b = a - (a / b) * b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // geometry helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Distance from point to line.
pointToLineDistance :: Number -> Number -> Number -> Number -> Number -> Number -> Number
pointToLineDistance px py x1 y1 x2 y2 =
  let
    dx = x2 - x1
    dy = y2 - y1
    lengthSq = dx * dx + dy * dy
  in
    if lengthSq < epsilon then
      -- Degenerate line (point)
      let dpx = px - x1
          dpy = py - y1
      in sqrt (dpx * dpx + dpy * dpy)
    else
      -- Perpendicular distance
      abs (dy * px - dx * py + x2 * y1 - y2 * x1) / sqrt lengthSq

-- | Compute angle at vertex (curvature approximation).
computeAngle :: Number -> Number -> Number -> Number -> Number -> Number -> Number
computeAngle px py cx cy nx ny =
  let
    -- Vectors from current to neighbors
    v1x = px - cx
    v1y = py - cy
    v2x = nx - cx
    v2y = ny - cy
    
    -- Angle between vectors
    angle1 = atan2 v1y v1x
    angle2 = atan2 v2y v2x
    diff = angle2 - angle1
  in
    -- Normalize to [-π, π]
    if diff > pi then diff - 2.0 * pi
    else if diff < negate pi then diff + 2.0 * pi
    else diff

-- | Compute curvature at each point.
computeCurvatures :: Array Point2D -> Array Number
computeCurvatures pts =
  let n = length pts
  in buildArray n (\i ->
       if i == 0 || i == n - 1 then Just 0.0
       else case { prev: index pts (i - 1), curr: index pts i, next: index pts (i + 1) } of
         { prev: Just (Point2D p), curr: Just (Point2D c), next: Just (Point2D nx) } ->
           Just (computeAngle p.x p.y c.x c.y nx.x nx.y)
         _ -> Just 0.0
     )

-- | Get lengths of each path segment.
pathSegmentLengths :: Array Point2D -> Array Number
pathSegmentLengths pts =
  let n = length pts
  in buildArray (max 0 (n - 1)) (\i ->
       case { p1: index pts i, p2: index pts (i + 1) } of
         { p1: Just (Point2D a), p2: Just (Point2D b) } ->
           let dx = b.x - a.x
               dy = b.y - a.y
           in Just (sqrt (dx * dx + dy * dy))
         _ -> Nothing
     )

-- | Sum of all segment lengths.
sumSegmentLengths :: Array Point2D -> Number
sumSegmentLengths pts =
  let segments = pathSegmentLengths pts
  in foldl (+) 0.0 segments

-- | Get point at specific arc length.
pointAtArcLength :: Number -> Array Point2D -> Point2D
pointAtArcLength targetLen pts =
  let
    segments = pathSegmentLengths pts
    n = length segments
  in
    findPointAtLength targetLen segments pts 0 0.0 n

-- | Helper to find point at arc length.
findPointAtLength :: Number -> Array Number -> Array Point2D -> Int -> Number -> Int -> Point2D
findPointAtLength target segments pts i accLen n =
  if i >= n then
    fromMaybe (point2D 0.0 0.0) (last pts)
  else
    case index segments i of
      Nothing -> fromMaybe (point2D 0.0 0.0) (last pts)
      Just segLen ->
        if accLen + segLen >= target then
          -- Interpolate within this segment
          let 
            localT = if segLen < epsilon then 0.0 else (target - accLen) / segLen
          in case { p1: index pts i, p2: index pts (i + 1) } of
            { p1: Just (Point2D a), p2: Just (Point2D b) } ->
              point2D (a.x + localT * (b.x - a.x)) (a.y + localT * (b.y - a.y))
            _ -> fromMaybe (point2D 0.0 0.0) (index pts i)
        else
          findPointAtLength target segments pts (i + 1) (accLen + segLen) n

-- | Compute normal at point index.
computeNormalAt :: Int -> Array Point2D -> Vector2D
computeNormalAt i pts =
  let
    n = length pts
    -- Get direction from neighboring points
    prevIdx = max 0 (i - 1)
    nextIdx = min (n - 1) (i + 1)
  in
    case { prev: index pts prevIdx, next: index pts nextIdx } of
      { prev: Just (Point2D p), next: Just (Point2D nx) } ->
        let 
          dx = nx.x - p.x
          dy = nx.y - p.y
          len = sqrt (dx * dx + dy * dy)
        in 
          if len < epsilon then vec2 0.0 1.0
          else perpendicular2 (normalize2 (vec2 dx dy))
      _ -> vec2 0.0 1.0
