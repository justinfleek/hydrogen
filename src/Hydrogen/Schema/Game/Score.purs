-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // schema // game // score
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Complete scoring and ranking systems for competitive games.
-- |
-- | Defines the atomic vocabulary for rating systems (Elo, Glicko), leaderboards,
-- | achievements, and score calculations. This module provides mathematically
-- | correct implementations suitable for deterministic game state at billion-
-- | agent scale.
-- |
-- | ## Rating Systems
-- |
-- | - **Elo**: Classic rating system (bounded 0-4000)
-- | - **Glicko**: Elo extension with rating deviation and volatility
-- |
-- | ## Design Philosophy
-- |
-- | Ratings are pure data with bounded domains. K-factors are bounded 10-40
-- | to prevent unstable rating swings. All calculations use standard formulas
-- | from statistical game theory.
-- |
-- | ## At Billion-Agent Scale
-- |
-- | When agents compute ratings:
-- | - Same inputs = same outputs (always)
-- | - Bounded domains prevent overflow/underflow
-- | - Deterministic expected score calculations
-- | - Complete achievement enumeration
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from submodules:
-- | - `Types`: Core data types (EloRating, GlickoRating, GameOutcome, etc.)
-- | - `Elo`: Elo rating calculations
-- | - `Glicko`: Glicko rating calculations
-- | - `Categories`: Rating categories, percentiles, tiers
-- | - `Leaderboard`: Leaderboard entry operations
-- | - `Scoring`: Score breakdown and streak tracking
-- | - `Formatting`: Display formatting functions

module Hydrogen.Schema.Game.Score
  ( module Types
  , module Elo
  , module Glicko
  , module Categories
  , module Leaderboard
  , module Scoring
  , module Formatting
  ) where

import Hydrogen.Schema.Game.Score.Types as Types
import Hydrogen.Schema.Game.Score.Elo as Elo
import Hydrogen.Schema.Game.Score.Glicko as Glicko
import Hydrogen.Schema.Game.Score.Categories as Categories
import Hydrogen.Schema.Game.Score.Leaderboard as Leaderboard
import Hydrogen.Schema.Game.Score.Scoring as Scoring
import Hydrogen.Schema.Game.Score.Formatting as Formatting
