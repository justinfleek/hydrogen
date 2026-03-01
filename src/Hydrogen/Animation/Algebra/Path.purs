-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // animation // algebra // path
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Path animations for following and morphing bezier paths.
-- |
-- | Supports SVG-style path segments: MoveTo, LineTo, QuadraticTo,
-- | CubicTo, ArcTo, ClosePath.

module Hydrogen.Animation.Algebra.Path
  ( Point2D
  , PathSegment(MoveTo, LineTo, QuadraticTo, CubicTo, ArcTo, ClosePath)
  , AnimationPath(AnimationPath)
  , followPath
  , morphPath
  , lerp2D
  , quadraticBezier
  , cubicBezier
  ) where

import Prelude
  ( class Eq
  , max
  , min
  , (+)
  , (-)
  , (*)
  , (==)
  )

import Data.Array (length, drop, head, index, zipWith)
import Data.Maybe (Maybe(Nothing, Just))
import Data.Newtype (class Newtype)
import Data.Int as Int

import Hydrogen.Animation.Time (Duration, Progress(Progress))
import Hydrogen.Animation.Algebra.Easing (Easing)
import Hydrogen.Animation.Algebra.Core (Animation(Animation))

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- Point2D
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | A point in 2D space.
type Point2D = { x :: Number, y :: Number }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- Path Segments
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Path segment types for bezier paths.
data PathSegment
  = MoveTo Point2D
  | LineTo Point2D
  | QuadraticTo Point2D Point2D           -- control, end
  | CubicTo Point2D Point2D Point2D       -- control1, control2, end
  | ArcTo Point2D Number Boolean Boolean  -- end, radius, largeArc, sweep
  | ClosePath

derive instance Eq PathSegment

-- | A complete animation path.
newtype AnimationPath = AnimationPath (Array PathSegment)

derive instance Newtype AnimationPath _
derive instance Eq AnimationPath

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- Path Following
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Animate an element following a path.
-- | Returns the position along the path at each progress point.
followPath :: AnimationPath -> Duration -> Easing -> Animation Point2D
followPath (AnimationPath segments) dur easing = Animation
  { dur
  , easing
  , sample: \(Progress p) -> samplePath segments p
  }

-- | Sample a point along the path at progress t in [0, 1].
samplePath :: Array PathSegment -> Number -> Point2D
samplePath segments t =
  case head segments of
    Nothing -> { x: 0.0, y: 0.0 }
    Just (MoveTo start) -> samplePathFrom start (drop 1 segments) t
    Just _ -> { x: 0.0, y: 0.0 } -- Path must start with MoveTo

samplePathFrom :: Point2D -> Array PathSegment -> Number -> Point2D
samplePathFrom start segments t =
  let total = length segments
  in if total == 0
       then start
       else 
         let segmentIndex = Int.floor (t * Int.toNumber total)
             boundedIndex = max 0 (min (total - 1) segmentIndex)
             localT = t * Int.toNumber total - Int.toNumber boundedIndex
         in case index segments boundedIndex of
              Nothing -> start
              Just seg -> sampleSegment start seg localT

-- | Sample a single path segment.
sampleSegment :: Point2D -> PathSegment -> Number -> Point2D
sampleSegment start segment t =
  case segment of
    MoveTo p -> p
    LineTo end -> lerp2D start end t
    QuadraticTo control end -> quadraticBezier start control end t
    CubicTo c1 c2 end -> cubicBezier start c1 c2 end t
    ArcTo end _ _ _ -> lerp2D start end t -- Simplified arc
    ClosePath -> start

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- Path Morphing
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Morph between two paths.
-- | Both paths must have the same structure (same number/types of segments).
morphPath :: AnimationPath -> AnimationPath -> Duration -> Easing -> Animation AnimationPath
morphPath (AnimationPath from) (AnimationPath to) dur easing = Animation
  { dur
  , easing
  , sample: \(Progress p) -> AnimationPath (zipWith (morphSegment p) from to)
  }

-- | Morph between two path segments.
morphSegment :: Number -> PathSegment -> PathSegment -> PathSegment
morphSegment t seg1 seg2 =
  case seg1, seg2 of
    MoveTo a, MoveTo b -> MoveTo (lerp2D a b t)
    LineTo a, LineTo b -> LineTo (lerp2D a b t)
    QuadraticTo c1 e1, QuadraticTo c2 e2 -> 
      QuadraticTo (lerp2D c1 c2 t) (lerp2D e1 e2 t)
    CubicTo c1a c1b e1, CubicTo c2a c2b e2 ->
      CubicTo (lerp2D c1a c2a t) (lerp2D c1b c2b t) (lerp2D e1 e2 t)
    ArcTo e1 r1 la1 sw1, ArcTo e2 r2 _ _ ->
      ArcTo (lerp2D e1 e2 t) (r1 + (r2 - r1) * t) la1 sw1
    ClosePath, ClosePath -> ClosePath
    _, _ -> seg1 -- Incompatible segments, keep first

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- Interpolation Utilities
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Linear interpolation in 2D.
lerp2D :: Point2D -> Point2D -> Number -> Point2D
lerp2D a b t =
  { x: a.x + (b.x - a.x) * t
  , y: a.y + (b.y - a.y) * t
  }

-- | Quadratic bezier interpolation.
quadraticBezier :: Point2D -> Point2D -> Point2D -> Number -> Point2D
quadraticBezier p0 p1 p2 t =
  let mt = 1.0 - t
      mt2 = mt * mt
      t2 = t * t
  in { x: mt2 * p0.x + 2.0 * mt * t * p1.x + t2 * p2.x
     , y: mt2 * p0.y + 2.0 * mt * t * p1.y + t2 * p2.y
     }

-- | Cubic bezier interpolation.
cubicBezier :: Point2D -> Point2D -> Point2D -> Point2D -> Number -> Point2D
cubicBezier p0 p1 p2 p3 t =
  let mt = 1.0 - t
      mt2 = mt * mt
      mt3 = mt2 * mt
      t2 = t * t
      t3 = t2 * t
  in { x: mt3 * p0.x + 3.0 * mt2 * t * p1.x + 3.0 * mt * t2 * p2.x + t3 * p3.x
     , y: mt3 * p0.y + 3.0 * mt2 * t * p1.y + 3.0 * mt * t2 * p2.y + t3 * p3.y
     }
