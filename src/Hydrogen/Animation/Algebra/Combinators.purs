-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // animation // algebra // combinators
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Animation combinators and stagger patterns.
-- |
-- | Combinators allow composition of animations:
-- | - Sequential: run one after another
-- | - Parallel: run simultaneously
-- | - Stagger: offset timing across a group

module Hydrogen.Animation.Algebra.Combinators
  ( -- Combinators
    sequential
  , parallel
  , stagger
  , delay
  , timeScale
  , reverse
  , pingPong
  , repeat
  
  -- Stagger patterns
  , StaggerPattern(LinearStagger, RandomStagger, CustomStagger)
  , StaggerDirection(LeftToRight, RightToLeft, CenterOut, EdgesIn)
  , applyStagger
  ) where

import Prelude
  ( class Eq
  , class Semigroup
  , class Monoid
  , mempty
  , max
  , mod
  , otherwise
  , (<>)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (==)
  )

import Data.Array (foldl)
import Data.Array as Array
import Data.Int as Int
import Data.Maybe (Maybe(Nothing, Just))
import Data.Ord (abs)

import Hydrogen.Animation.Time (Duration(Duration), Progress(Progress))
import Hydrogen.Animation.Algebra.Easing (Easing(Linear))
import Hydrogen.Animation.Algebra.Core (Animation(Animation), runAnimation)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- Core Combinators
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Sequential composition: run a1 then a2.
-- | Time is remapped: [0, 0.5) -> a1, [0.5, 1] -> a2 (proportionally).
sequential :: forall a. Semigroup a => Animation a -> Animation a -> Animation a
sequential (Animation a1) (Animation a2) = Animation
  { dur: a1.dur <> a2.dur
  , easing: Linear
  , sample: \(Progress p) ->
      let (Duration d1) = a1.dur
          (Duration d2) = a2.dur
          totalDur = Int.toNumber (d1 + d2)
          boundary = if totalDur == 0.0 then 0.5 else Int.toNumber d1 / totalDur
      in if p < boundary
           then a1.sample (Progress (if boundary == 0.0 then 0.0 else p / boundary))
           else let p2 = if boundary == 1.0 then 1.0 else (p - boundary) / (1.0 - boundary)
                in a1.sample (Progress 1.0) <> a2.sample (Progress p2)
  }

-- | Parallel composition: run a1 and a2 simultaneously.
-- | Total duration is max of both. Values are combined via Semigroup.
parallel :: forall a. Semigroup a => Animation a -> Animation a -> Animation a
parallel (Animation a1) (Animation a2) = Animation
  { dur: max a1.dur a2.dur
  , easing: Linear
  , sample: \p -> a1.sample p <> a2.sample p
  }

-- | Stagger an array of animations.
-- | Each animation starts after a delay relative to the previous one.
stagger :: forall a. Monoid a => Duration -> Array (Animation a) -> Animation a
stagger delayBetween animations =
  case Array.uncons animations of
    Nothing -> mempty
    Just { head, tail } -> 
      foldl (\acc anim -> sequential acc (sequential (delay delayBetween mempty) anim)) head tail

-- | Add a delay before an animation.
delay :: forall a. Duration -> a -> Animation a
delay dur value = Animation
  { dur
  , easing: Linear
  , sample: \_ -> value
  }

-- | Scale the time of an animation (speed up or slow down).
-- | factor > 1 = faster, factor < 1 = slower.
timeScale :: forall a. Number -> Animation a -> Animation a
timeScale factor (Animation anim) =
  let (Duration d) = anim.dur
      newDur = Duration (max 0 (Int.floor (Int.toNumber d / factor)))
  in Animation
    { dur: newDur
    , easing: anim.easing
    , sample: anim.sample
    }

-- | Reverse an animation (play backwards).
reverse :: forall a. Animation a -> Animation a
reverse (Animation anim) = Animation
  { dur: anim.dur
  , easing: anim.easing
  , sample: \(Progress p) -> anim.sample (Progress (1.0 - p))
  }

-- | Ping-pong: play forward then backward.
pingPong :: forall a. Semigroup a => Animation a -> Animation a
pingPong anim = sequential anim (reverse anim)

-- | Repeat an animation n times.
repeat :: forall a. Semigroup a => Int -> Animation a -> Animation a
repeat n anim
  | n < 1 = Animation { dur: Duration 0, easing: Linear, sample: \_ -> runAnimation anim (Progress 0.0) }
  | n == 1 = anim
  | otherwise = sequential anim (repeat (n - 1) anim)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- Stagger Patterns
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Direction for linear stagger patterns.
data StaggerDirection
  = LeftToRight
  | RightToLeft
  | CenterOut
  | EdgesIn

derive instance Eq StaggerDirection

-- | Stagger pattern determines delay for each element.
data StaggerPattern
  = LinearStagger StaggerDirection Duration
  | RandomStagger Int Duration   -- seed, max delay
  | CustomStagger (Int -> Int -> Duration)  -- index -> total -> delay

-- | Apply stagger pattern to get delay for element at index.
applyStagger :: StaggerPattern -> Int -> Int -> Duration
applyStagger pattern index total =
  case pattern of
    LinearStagger dir delayPer ->
      let (Duration d) = delayPer
          factor = case dir of
            LeftToRight -> index
            RightToLeft -> total - 1 - index
            CenterOut ->
              let center = Int.toNumber total / 2.0
              in Int.floor (abs (Int.toNumber index - center))
            EdgesIn ->
              let center = Int.toNumber total / 2.0
                  maxDist = center
              in Int.floor (maxDist - abs (Int.toNumber index - center))
      in Duration (d * factor)
    
    RandomStagger seed maxDelay ->
      let (Duration maxD) = maxDelay
          -- Simple deterministic pseudo-random based on seed and index
          hash = ((seed * 31) + index * 17) `mod` 10000
          factor = Int.toNumber hash / 10000.0
      in Duration (Int.floor (Int.toNumber maxD * factor))
    
    CustomStagger f -> f index total
