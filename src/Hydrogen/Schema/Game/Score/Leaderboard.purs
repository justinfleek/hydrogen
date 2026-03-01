-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // game // score // leaderboard
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Leaderboard entry operations.
-- |
-- | Provides functions for creating and querying leaderboard entries,
-- | including win rate calculations and game totals.

module Hydrogen.Schema.Game.Score.Leaderboard
  ( -- * Construction
    mkLeaderboardEntry
  
  -- * Queries
  , winRate
  , totalGames
  ) where

import Prelude
  ( otherwise
  , (+)
  , (/)
  , (*)
  , (<)
  , (==)
  )

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Game.Score.Types
  ( EloRating
  , LeaderboardEntry
  )

import Hydrogen.Schema.Game.Score.Internal (intToNumber)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a leaderboard entry with validation.
-- |
-- | Returns Nothing if:
-- | - rank is less than 1
-- | - wins, losses, or draws are negative
mkLeaderboardEntry :: Int -> String -> EloRating -> Int -> Int -> Int -> Maybe LeaderboardEntry
mkLeaderboardEntry rank playerId rating wins losses draws
  | rank < 1 = Nothing
  | wins < 0 = Nothing
  | losses < 0 = Nothing
  | draws < 0 = Nothing
  | otherwise = Just
      { rank: rank
      , playerId: playerId
      , rating: rating
      , wins: wins
      , losses: losses
      , draws: draws
      }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate win rate as a percentage.
-- |
-- | Returns 0.0 if no games have been played.
-- | Otherwise returns (wins / total) * 100.
winRate :: LeaderboardEntry -> Number
winRate entry =
  let
    total = entry.wins + entry.losses + entry.draws
  in
    if total == 0
      then 0.0
      else (intToNumber entry.wins / intToNumber total) * 100.0

-- | Get total games played.
totalGames :: LeaderboardEntry -> Int
totalGames entry = entry.wins + entry.losses + entry.draws
