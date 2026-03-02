-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // temporal // progress
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Progress Atom — Normalized animation progress value [0.0, 1.0].
-- |
-- | Progress represents the current state of an animation or process:
-- | - 0.0: Start
-- | - 1.0: End
-- |
-- | Values are clamped to [0.0, 1.0] to ensure valid interpolation.

module Hydrogen.Schema.Temporal.Progress
  ( Progress
  , progress
  , safeProgress
  , unsafeProgress
  , unwrapProgress
  , progressToNumber
  , start
  , end
  , progressBounds
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , not
  , otherwise
  , (&&)
  , (<>)
  , (<)
  , (>)
  , (>=)
  , (<=)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // progress
-- ═════════════════════════════════════════════════════════════════════════════

-- | Normalized progress value [0.0, 1.0]
newtype Progress = Progress Number

derive instance eqProgress :: Eq Progress
derive instance ordProgress :: Ord Progress

instance showProgress :: Show Progress where
  show (Progress p) = "(Progress " <> show p <> ")"

-- | Create Progress, clamping to [0.0, 1.0].
-- |
-- | NaN and Infinity are clamped to 0.0 (start of progress).
-- | For explicit rejection of invalid values, use `safeProgress`.
-- |
-- | ```purescript
-- | progress 0.5         -- Progress 0.5
-- | progress 1.5         -- Progress 1.0 (clamped)
-- | progress (-0.5)      -- Progress 0.0 (clamped)
-- | progress (0.0 / 0.0) -- Progress 0.0 (NaN clamped)
-- | progress (1.0 / 0.0) -- Progress 0.0 (Infinity clamped)
-- | ```
progress :: Number -> Progress
progress p
  | not (Bounded.isFiniteNumber p) = Progress 0.0  -- NaN/Infinity → start
  | p < 0.0 = Progress 0.0
  | p > 1.0 = Progress 1.0
  | otherwise = Progress p

-- | Create Progress with explicit validation, rejecting invalid values.
-- |
-- | Returns Nothing for NaN, Infinity, or values outside [0.0, 1.0].
-- | This is the **secure** constructor — use it at system boundaries.
-- |
-- | ```purescript
-- | safeProgress 0.5         -- Just (Progress 0.5)
-- | safeProgress 1.5         -- Nothing (exceeds 1.0)
-- | safeProgress (-0.5)      -- Nothing (negative)
-- | safeProgress (0.0 / 0.0) -- Nothing (NaN rejected)
-- | safeProgress (1.0 / 0.0) -- Nothing (Infinity rejected)
-- | ```
-- |
-- | ## Security Model
-- |
-- | NaN and Infinity are attack vectors. A malicious actor crafting
-- | `0.0 / 0.0` or `1.0 / 0.0` can bypass naive bounds checks.
-- | This function explicitly rejects these values at the boundary.
safeProgress :: Number -> Maybe Progress
safeProgress p
  | not (Bounded.isFiniteNumber p) = Nothing  -- NaN/Infinity rejected
  | p < 0.0 = Nothing                         -- Below minimum
  | p > 1.0 = Nothing                         -- Above maximum
  | otherwise = Just (Progress p)

-- | Create Progress without bounds checking
-- |
-- | Use only when you have already validated the value is in [0.0, 1.0].
unsafeProgress :: Number -> Progress
unsafeProgress = Progress

-- | Extract raw Number from Progress
unwrapProgress :: Progress -> Number
unwrapProgress (Progress p) = p

-- | Alias for unwrapProgress
progressToNumber :: Progress -> Number
progressToNumber = unwrapProgress

-- | Start of progress (0.0)
start :: Progress
start = Progress 0.0

-- | End of progress (1.0)
end :: Progress
end = Progress 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for Progress
progressBounds :: Bounded.NumberBounds
progressBounds = Bounded.numberBounds 0.0 1.0 Bounded.Clamps "progress"
  "Normalized progress value (0.0 to 1.0)"
