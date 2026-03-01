-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // game // score // scoring
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Score breakdown calculations and streak tracking.
-- |
-- | Provides functions for calculating composite scores from base values,
-- | multipliers, and bonuses. Also includes win streak bonus calculations.

module Hydrogen.Schema.Game.Score.Scoring
  ( -- * Score Breakdown
    calculateTotal
  , applyMultiplier
  , addBonus
  
  -- * Streak Tracking
  , streakBonus
  , streakMultiplier
  ) where

import Prelude
  ( otherwise
  , (+)
  , (*)
  , (<)
  )

import Hydrogen.Schema.Game.Score.Types (ScoreBreakdown)
import Hydrogen.Schema.Game.Score.Internal
  ( Bonus
  , intToNumber
  , roundToInt
  , sumBonuses
  , appendBonus
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // score // breakdown
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate total score from breakdown components.
-- |
-- | Formula: (base + sum(bonuses)) * multiplier
calculateTotal :: Int -> Number -> Array Bonus -> Int
calculateTotal base multiplier bonuses =
  let
    bonusSum = sumBonuses bonuses
    subtotal = intToNumber (base + bonusSum)
    finalScore = subtotal * multiplier
  in
    roundToInt finalScore

-- | Apply a multiplier to a score breakdown.
-- |
-- | The new multiplier is the product of the existing and new multipliers.
-- | Total is recalculated with the combined multiplier.
applyMultiplier :: ScoreBreakdown -> Number -> ScoreBreakdown
applyMultiplier breakdown mult =
  let
    newMultiplier = breakdown.multiplier * mult
    newTotal = calculateTotal breakdown.base newMultiplier breakdown.bonuses
  in
    breakdown { multiplier = newMultiplier, total = newTotal }

-- | Add a bonus to a score breakdown.
-- |
-- | Appends the bonus to the existing bonuses array and recalculates total.
addBonus :: ScoreBreakdown -> String -> Int -> ScoreBreakdown
addBonus breakdown name value =
  let
    newBonus = { name: name, value: value }
    newBonuses = appendBonus breakdown.bonuses newBonus
    newTotal = calculateTotal breakdown.base breakdown.multiplier newBonuses
  in
    breakdown { bonuses = newBonuses, total = newTotal }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // streak // tracking
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate bonus points for a win streak.
-- |
-- | Streak bonuses (consecutive wins):
-- | - 0-2: No bonus
-- | - 3-4: +10 points
-- | - 5-6: +25 points
-- | - 7-9: +50 points
-- | - 10+: +100 points
streakBonus :: Int -> Int
streakBonus streak
  | streak < 3  = 0
  | streak < 5  = 10
  | streak < 7  = 25
  | streak < 10 = 50
  | otherwise   = 100

-- | Calculate multiplier for a streak.
-- |
-- | Returns a multiplier >= 1.0 based on streak length:
-- | - 0-2: 1.0x
-- | - 3-4: 1.1x
-- | - 5-6: 1.25x
-- | - 7-9: 1.5x
-- | - 10+: 2.0x
streakMultiplier :: Int -> Number
streakMultiplier streak
  | streak < 3  = 1.0
  | streak < 5  = 1.1
  | streak < 7  = 1.25
  | streak < 10 = 1.5
  | otherwise   = 2.0
