-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // game // score // glicko
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Glicko rating system calculations.
-- |
-- | Glicko extends Elo by tracking rating deviation (uncertainty).
-- | A player with high RD has an uncertain rating, while low RD indicates
-- | a well-established skill level.
-- |
-- | This implements Glicko-1 with simplified single-game updates.
-- | For full Glicko-2 with volatility updates, see the specification.

module Hydrogen.Schema.Game.Score.Glicko
  ( -- * Glicko Constants
    glickoQ
  , glickoG
  
  -- * Glicko Calculations
  , glickoExpectedScore
  , updateGlicko
  ) where

import Prelude
  ( negate
  , (-)
  , (*)
  , (/)
  , (+)
  , (>)
  )

import Data.Number (pow, log, sqrt, pi) as Number

import Hydrogen.Schema.Bounded (clampNumber)

import Hydrogen.Schema.Game.Score.Types
  ( RatingDeviation(RatingDeviation)
  , ratingDeviation
  , unwrapRatingDeviation
  , GlickoRating
  , GameOutcome
  , outcomeValue
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // glicko // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Glicko constant q = ln(10) / 400.
glickoQ :: Number
glickoQ = Number.log 10.0 / 400.0

-- | Glicko g function: g(RD) = 1 / sqrt(1 + 3 * q^2 * RD^2 / pi^2)
-- |
-- | This function attenuates the impact of opponents with high
-- | rating deviation (uncertain ratings).
glickoG :: RatingDeviation -> Number
glickoG rd =
  let
    rdVal = unwrapRatingDeviation rd
    q2 = glickoQ * glickoQ
    rd2 = rdVal * rdVal
    pi2 = Number.pi * Number.pi
    denominator = 1.0 + (3.0 * q2 * rd2 / pi2)
  in
    1.0 / Number.sqrt denominator

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // glicko // calculations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate Glicko expected score.
-- |
-- | E(s|r, r_j, RD_j) = 1 / (1 + 10^(-g(RD_j) * (r - r_j) / 400))
-- |
-- | This is similar to Elo expected score but attenuated by the
-- | opponent's rating deviation.
glickoExpectedScore :: GlickoRating -> GlickoRating -> Number
glickoExpectedScore player opponent =
  let
    g = glickoG opponent.deviation
    rDiff = player.rating - opponent.rating
    exponent = negate g * rDiff / 400.0
  in
    1.0 / (1.0 + Number.pow 10.0 exponent)

-- | Update a Glicko rating after a game.
-- |
-- | Simplified Glicko update (single game, not Glicko-2 full algorithm).
-- | Updates both rating and rating deviation based on game result.
-- |
-- | The rating deviation decreases as more games are played, indicating
-- | increased confidence in the rating.
updateGlicko :: GlickoRating -> GlickoRating -> GameOutcome -> GlickoRating
updateGlicko player opponent outcome =
  let
    g = glickoG opponent.deviation
    expected = glickoExpectedScore player opponent
    actual = outcomeValue outcome
    
    -- d^2 = 1 / (q^2 * g^2 * E * (1 - E))
    e = expected
    d2Inv = glickoQ * glickoQ * g * g * e * (1.0 - e)
    d2 = if d2Inv > 0.0 then 1.0 / d2Inv else 1000000.0
    
    -- New RD: 1 / sqrt(1/RD^2 + 1/d^2)
    rd = unwrapRatingDeviation player.deviation
    newRd2 = 1.0 / ((1.0 / (rd * rd)) + (1.0 / d2))
    newRd = Number.sqrt newRd2
    
    -- New rating: r' = r + q / (1/RD^2 + 1/d^2) * g * (s - E)
    ratingChange = (glickoQ / ((1.0 / (rd * rd)) + (1.0 / d2))) * g * (actual - expected)
    newRating = player.rating + ratingChange
  in
    { rating: clampNumber 0.0 4000.0 newRating
    , deviation: ratingDeviation newRd
    , volatility: player.volatility
    }
