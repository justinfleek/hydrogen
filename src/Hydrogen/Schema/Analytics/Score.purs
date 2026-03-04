-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // schema // analytics // score
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Bounded score primitives for analytics and leaderboards.
-- |
-- | ## Security Model
-- |
-- | When an agent operates inside a world model created by another (potentially
-- | malicious) agent, all incoming data is UNTRUSTED. A malicious world could:
-- |
-- | - Send `score: Infinity` to overflow rankings
-- | - Send `score: -999999999999999` to corrupt aggregations
-- | - Send `score: NaN` to poison calculations
-- |
-- | Bounded types are the firewall. Invalid values are REJECTED or CLAMPED
-- | at the boundary - no undefined behavior propagates into the agent's state.
-- |
-- | ## At Billion-Agent Scale
-- |
-- | At 10,000 tokens/second, an agent cannot manually validate every field.
-- | The type system enforces invariants automatically:
-- |
-- | - `Score 999999999999` → Clamped to `Score 999999999`
-- | - `Score (-1)` → Clamped to `Score 0`
-- | - Non-finite values → Rejected
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Bounded (clampInt, BoundsBehavior)

module Hydrogen.Schema.Analytics.Score
  ( -- * Score Atom
    Score
  , score
  , scoreUnsafe
  , clampScore
  , unwrapScore
  , scoreBounds
  
  -- * Score Constants
  , scoreZero
  , scoreMax
  
  -- * Score Operations
  , addScore
  , subtractScore
  , scaleScore
  
  -- * Score Predicates
  , isPositiveScore
  , isMaxScore
  
  -- * Rank Atom
  , Rank
  , rank
  , rankUnsafe
  , clampRank
  , unwrapRank
  , rankBounds
  
  -- * Rank Constants
  , rankFirst
  , rankLast
  
  -- * Rank Operations
  , improveRank
  , worsenRank
  
  -- * Rank Delta
  , RankDelta
  , rankDelta
  , rankDeltaUnsafe
  , clampRankDelta
  , unwrapRankDelta
  , rankDeltaBounds
  
  -- * RankDelta Constants
  , rankUnchanged
  , rankImproved
  , rankWorsened
  
  -- * RankDelta Predicates
  , isImprovement
  , isDecline
  , isUnchanged
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , negate
  , (+)
  , (-)
  , (*)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (==)
  , (&&)
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Bounded 
  ( BoundsBehavior(Clamps)
  , IntBounds
  , intBounds
  , clampInt
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // score atom
-- ═════════════════════════════════════════════════════════════════════════════

-- | Score - a bounded non-negative integer for game/analytics scores.
-- |
-- | Bounds: 0 to 999,999,999 (clamped)
-- |
-- | ## Security
-- |
-- | - Negative values clamp to 0
-- | - Values above max clamp to max
-- | - Safe against overflow attacks from malicious world models
newtype Score = Score Int

derive instance eqScore :: Eq Score
derive instance ordScore :: Ord Score

instance showScore :: Show Score where
  show (Score n) = "Score(" <> show n <> ")"

-- | Bounds documentation for Score.
scoreBounds :: IntBounds
scoreBounds = intBounds 0 999999999 Clamps "score" "Non-negative score value (0-999999999)"

-- | Smart constructor - validates and clamps input.
score :: Int -> Maybe Score
score n
  | n >= 0 && n <= 999999999 = Just (Score n)
  | otherwise = Nothing

-- | Clamping constructor - always succeeds by clamping to bounds.
clampScore :: Int -> Score
clampScore n = Score (clampInt 0 999999999 n)

-- | Unsafe constructor - use only when value is known valid.
scoreUnsafe :: Int -> Score
scoreUnsafe = Score

-- | Unwrap to raw Int.
unwrapScore :: Score -> Int
unwrapScore (Score n) = n

-- | Zero score.
scoreZero :: Score
scoreZero = Score 0

-- | Maximum score.
scoreMax :: Score
scoreMax = Score 999999999

-- | Add two scores (clamped).
addScore :: Score -> Score -> Score
addScore (Score a) (Score b) = clampScore (a + b)

-- | Subtract scores (clamped to 0).
subtractScore :: Score -> Score -> Score
subtractScore (Score a) (Score b) = clampScore (a - b)

-- | Scale score by factor (clamped).
scaleScore :: Int -> Score -> Score
scaleScore factor (Score n) = clampScore (factor * n)

-- | Is score positive (non-zero)?
isPositiveScore :: Score -> Boolean
isPositiveScore (Score n) = n > 0

-- | Is score at maximum?
isMaxScore :: Score -> Boolean
isMaxScore (Score n) = n == 999999999

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // rank atom
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rank - a bounded positive integer for leaderboard positions.
-- |
-- | Bounds: 1 to 1,000,000 (clamped)
-- |
-- | ## Semantics
-- |
-- | - Rank 1 is BEST (first place)
-- | - Rank 1000000 is WORST (last tracked position)
-- | - Lower number = better rank
newtype Rank = Rank Int

derive instance eqRank :: Eq Rank
derive instance ordRank :: Ord Rank

instance showRank :: Show Rank where
  show (Rank n) = "Rank(" <> show n <> ")"

-- | Bounds documentation for Rank.
rankBounds :: IntBounds
rankBounds = intBounds 1 1000000 Clamps "rank" "Leaderboard position (1-1000000, 1 is best)"

-- | Smart constructor - validates input.
rank :: Int -> Maybe Rank
rank n
  | n >= 1 && n <= 1000000 = Just (Rank n)
  | otherwise = Nothing

-- | Clamping constructor - always succeeds.
clampRank :: Int -> Rank
clampRank n = Rank (clampInt 1 1000000 n)

-- | Unsafe constructor.
rankUnsafe :: Int -> Rank
rankUnsafe = Rank

-- | Unwrap to raw Int.
unwrapRank :: Rank -> Int
unwrapRank (Rank n) = n

-- | First place (best rank).
rankFirst :: Rank
rankFirst = Rank 1

-- | Last tracked position.
rankLast :: Rank
rankLast = Rank 1000000

-- | Improve rank by n positions (lower number = better).
improveRank :: Int -> Rank -> Rank
improveRank positions (Rank n) = clampRank (n - positions)

-- | Worsen rank by n positions.
worsenRank :: Int -> Rank -> Rank
worsenRank positions (Rank n) = clampRank (n + positions)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // rank delta atom
-- ═════════════════════════════════════════════════════════════════════════════

-- | RankDelta - change in rank since last update.
-- |
-- | Bounds: -1,000,000 to +1,000,000 (clamped)
-- |
-- | ## Semantics
-- |
-- | - Negative = improved (moved UP the leaderboard)
-- | - Positive = declined (moved DOWN the leaderboard)
-- | - Zero = unchanged
newtype RankDelta = RankDelta Int

derive instance eqRankDelta :: Eq RankDelta
derive instance ordRankDelta :: Ord RankDelta

instance showRankDelta :: Show RankDelta where
  show (RankDelta n) = "RankDelta(" <> show n <> ")"

-- | Bounds documentation for RankDelta.
rankDeltaBounds :: IntBounds
rankDeltaBounds = intBounds (negate 1000000) 1000000 Clamps "rankDelta" "Change in rank (-1000000 to +1000000, negative = improvement)"

-- | Smart constructor.
rankDelta :: Int -> Maybe RankDelta
rankDelta n
  | n >= negate 1000000 && n <= 1000000 = Just (RankDelta n)
  | otherwise = Nothing

-- | Clamping constructor.
clampRankDelta :: Int -> RankDelta
clampRankDelta n = RankDelta (clampInt (negate 1000000) 1000000 n)

-- | Unsafe constructor.
rankDeltaUnsafe :: Int -> RankDelta
rankDeltaUnsafe = RankDelta

-- | Unwrap to raw Int.
unwrapRankDelta :: RankDelta -> Int
unwrapRankDelta (RankDelta n) = n

-- | No change in rank.
rankUnchanged :: RankDelta
rankUnchanged = RankDelta 0

-- | Improved by 1 position.
rankImproved :: RankDelta
rankImproved = RankDelta (negate 1)

-- | Worsened by 1 position.
rankWorsened :: RankDelta
rankWorsened = RankDelta 1

-- | Did rank improve (negative delta)?
isImprovement :: RankDelta -> Boolean
isImprovement (RankDelta n) = n < 0

-- | Did rank decline (positive delta)?
isDecline :: RankDelta -> Boolean
isDecline (RankDelta n) = n > 0

-- | Is rank unchanged?
isUnchanged :: RankDelta -> Boolean
isUnchanged (RankDelta n) = n == 0
