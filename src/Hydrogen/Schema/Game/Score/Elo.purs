-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // game // score // elo
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Elo rating system calculations.
-- |
-- | Implements the standard Elo rating formulas for competitive games:
-- | - Expected score calculation
-- | - Rating updates after games
-- | - K-factor determination by rating level
-- |
-- | All calculations use bounded domains to ensure deterministic behavior.
-- | The formulas follow standard statistical game theory.

module Hydrogen.Schema.Game.Score.Elo
  ( -- * K-Factor by Rating
    kFactorByRating
  
  -- * Elo Calculations
  , expectedScore
  , newEloRating
  , eloChange
  , winProbability
  
  -- * Glicko Conversion
  , glickoToElo
  ) where

import Prelude
  ( otherwise
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  )

import Data.Number (pow) as Number

import Hydrogen.Schema.Game.Score.Types
  ( EloRating
  , eloRating
  , unwrapEloRating
  , KFactor(KFactor)
  , unwrapKFactor
  , GlickoRating
  , GameOutcome
  , outcomeValue
  , RatingChange
  )

import Hydrogen.Schema.Game.Score.Internal (intToNumber, roundToInt)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // k // factor // rules
-- ═════════════════════════════════════════════════════════════════════════════

-- | Determine K-factor based on rating level.
-- |
-- | FIDE-style rules:
-- | - Under 2100: K=40
-- | - 2100-2400: K=20
-- | - Above 2400: K=10
kFactorByRating :: EloRating -> KFactor
kFactorByRating rating =
  let
    r = unwrapEloRating rating
  in
    if r < 2100 then KFactor 40
    else if r < 2400 then KFactor 20
    else KFactor 10

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // elo // calculations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate expected score using Elo formula.
-- |
-- | E_A = 1 / (1 + 10^((R_B - R_A) / 400))
-- |
-- | Returns a probability between 0 and 1.
expectedScore :: EloRating -> EloRating -> Number
expectedScore playerA playerB =
  let
    rA = unwrapEloRating playerA
    rB = unwrapEloRating playerB
    diff = intToNumber (rB - rA)
    exponent = diff / 400.0
  in
    1.0 / (1.0 + Number.pow 10.0 exponent)

-- | Calculate new Elo rating after a game.
-- |
-- | R'_A = R_A + K * (S_A - E_A)
-- |
-- | Where:
-- | - R_A: Current rating
-- | - K: K-factor
-- | - S_A: Actual score (1 for win, 0.5 for draw, 0 for loss)
-- | - E_A: Expected score
newEloRating :: EloRating -> EloRating -> KFactor -> GameOutcome -> EloRating
newEloRating playerRating opponentRating kf outcome =
  let
    expected = expectedScore playerRating opponentRating
    actual = outcomeValue outcome
    k = intToNumber (unwrapKFactor kf)
    currentRating = intToNumber (unwrapEloRating playerRating)
    delta = k * (actual - expected)
    newRating = currentRating + delta
  in
    eloRating (roundToInt newRating)

-- | Calculate the rating change for a game.
eloChange :: EloRating -> EloRating -> KFactor -> GameOutcome -> RatingChange
eloChange playerRating opponentRating kf outcome =
  let
    newRating = newEloRating playerRating opponentRating kf outcome
    before = unwrapEloRating playerRating
    after = unwrapEloRating newRating
  in
    { before: playerRating
    , after: newRating
    , change: after - before
    }

-- | Calculate win probability (same as expected score).
winProbability :: EloRating -> EloRating -> Number
winProbability = expectedScore

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // glicko // conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Glicko rating to Elo (uses the rating component).
glickoToElo :: GlickoRating -> EloRating
glickoToElo g = eloRating (roundToInt g.rating)
