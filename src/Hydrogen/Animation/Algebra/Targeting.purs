-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // animation // algebra // targeting
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Animation targeting for typography animations.
-- |
-- | Target specific characters, words, lines, or ranges of text
-- | for animated effects.

module Hydrogen.Animation.Algebra.Targeting
  ( AnimationTarget(TargetCharacter, TargetWord, TargetLine, TargetRange, TargetAll)
  , TargetSelector(SelectAll, SelectOdd, SelectEven, SelectEvery, SelectRange, SelectIndices, SelectWhere)
  , targeted
  ) where

import Prelude
  ( class Eq
  , map
  , mod
  , (-)
  , (<)
  , (>=)
  , (==)
  , (&&)
  )

import Data.Array (filter, elem)

import Hydrogen.Animation.Algebra.Core (Animation)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- Animation Targets
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | What can be animated in typography.
data AnimationTarget
  = TargetCharacter Int              -- Single character by index
  | TargetWord Int                   -- Single word by index
  | TargetLine Int                   -- Single line by index
  | TargetRange Int Int              -- Character range [start, end)
  | TargetAll                        -- All characters

derive instance Eq AnimationTarget

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- Target Selectors
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Selector for which elements to animate.
data TargetSelector
  = SelectAll
  | SelectOdd
  | SelectEven
  | SelectEvery Int Int              -- every nth starting at offset
  | SelectRange Int Int              -- indices [start, end)
  | SelectIndices (Array Int)        -- specific indices
  | SelectWhere (Int -> Boolean)     -- custom predicate

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- Targeted Animation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Create a targeted animation that applies to specific characters/words.
targeted :: forall a. TargetSelector -> Animation a -> Array Int -> Array (Animation a)
targeted selector anim indices =
  let matches = case selector of
        SelectAll -> indices
        SelectOdd -> filter (\i -> i `mod` 2 == 1) indices
        SelectEven -> filter (\i -> i `mod` 2 == 0) indices
        SelectEvery n offset -> filter (\i -> (i - offset) `mod` n == 0) indices
        SelectRange start end -> filter (\i -> i >= start && i < end) indices
        SelectIndices specific -> filter (\i -> elem i specific) indices
        SelectWhere pred -> filter pred indices
  in map (\_ -> anim) matches
