-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // schema // game // score // formatting
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Display formatting functions for scores and ratings.
-- |
-- | Provides human-readable string representations for ratings,
-- | rating changes, and win rates.

module Hydrogen.Schema.Game.Score.Formatting
  ( -- * Formatting
    formatRating
  , formatChange
  , formatWinRate
  ) where

import Prelude
  ( show
  , otherwise
  , (-)
  , (*)
  , (/)
  , (>)
  , (<)
  , (<>)
  )

import Hydrogen.Schema.Game.Score.Types
  ( EloRating
  , unwrapEloRating
  , LeaderboardEntry
  )

import Hydrogen.Schema.Game.Score.Leaderboard (winRate)

import Hydrogen.Schema.Game.Score.Internal (roundToInt, absInt)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // formatting
-- ═════════════════════════════════════════════════════════════════════════════

-- | Format Elo rating for display.
-- |
-- | Simply converts the rating to a string.
formatRating :: EloRating -> String
formatRating rating = show (unwrapEloRating rating)

-- | Format rating change with sign.
-- |
-- | Examples:
-- | - Positive: "+15"
-- | - Negative: "-10"
-- | - Zero: "0"
formatChange :: Int -> String
formatChange change
  | change > 0 = "+" <> show change
  | change < 0 = show change
  | otherwise  = "0"

-- | Format win rate as percentage string.
-- |
-- | Displays one decimal place.
-- |
-- | Example: "67.5%"
formatWinRate :: LeaderboardEntry -> String
formatWinRate entry =
  let
    rate = winRate entry
    rounded = roundToInt (rate * 10.0)
    whole = rounded / 10
    frac = absInt (rounded - (whole * 10))
  in
    show whole <> "." <> show frac <> "%"
