-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // schema // game // score // categories
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Rating categories, percentiles, and tier classifications.
-- |
-- | Provides human-readable labels and statistical measures for Elo ratings.
-- | Categories follow standard chess terminology; percentiles are based on
-- | typical online rating distributions.

module Hydrogen.Schema.Game.Score.Categories
  ( -- * Rating Categories
    ratingCategory
  , ratingPercentile
  , ratingTier
  ) where

import Prelude
  ( otherwise
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  )

import Hydrogen.Schema.Bounded (clampNumber)

import Hydrogen.Schema.Game.Score.Types
  ( EloRating
  , unwrapEloRating
  )

import Hydrogen.Schema.Game.Score.Internal (intToNumber)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // rating // categories
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get human-readable rating category.
-- |
-- | Categories:
-- | - Beginner: 0-800
-- | - Novice: 800-1200
-- | - Intermediate: 1200-1600
-- | - Advanced: 1600-2000
-- | - Expert: 2000-2200
-- | - Master: 2200-2400
-- | - Grandmaster: 2400-2700
-- | - Super Grandmaster: 2700+
ratingCategory :: EloRating -> String
ratingCategory rating =
  let
    r = unwrapEloRating rating
  in
    if r < 800 then "Beginner"
    else if r < 1200 then "Novice"
    else if r < 1600 then "Intermediate"
    else if r < 2000 then "Advanced"
    else if r < 2200 then "Expert"
    else if r < 2400 then "Master"
    else if r < 2700 then "Grandmaster"
    else "Super Grandmaster"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // rating // percentile
-- ═════════════════════════════════════════════════════════════════════════════

-- | Estimate percentile rank based on Elo rating.
-- |
-- | Based on typical online chess rating distributions.
-- | Returns a value from 0 to 100.
-- |
-- | Distribution model:
-- | - 0-800: Bottom 10%
-- | - 800-1000: 10-25%
-- | - 1000-1200: 25-45%
-- | - 1200-1400: 45-65%
-- | - 1400-1600: 65-80%
-- | - 1600-1800: 80-90%
-- | - 1800-2000: 90-95%
-- | - 2000-2200: 95-98%
-- | - 2200-2400: 98-99.5%
-- | - 2400+: Top 0.5%
ratingPercentile :: EloRating -> Number
ratingPercentile rating =
  let
    r = unwrapEloRating rating
    rNum = intToNumber r
  in
    if r < 800 then clampNumber 0.0 100.0 (rNum / 800.0 * 10.0)
    else if r < 1000 then 10.0 + ((rNum - 800.0) / 200.0 * 15.0)
    else if r < 1200 then 25.0 + ((rNum - 1000.0) / 200.0 * 20.0)
    else if r < 1400 then 45.0 + ((rNum - 1200.0) / 200.0 * 20.0)
    else if r < 1600 then 65.0 + ((rNum - 1400.0) / 200.0 * 15.0)
    else if r < 1800 then 80.0 + ((rNum - 1600.0) / 200.0 * 10.0)
    else if r < 2000 then 90.0 + ((rNum - 1800.0) / 200.0 * 5.0)
    else if r < 2200 then 95.0 + ((rNum - 2000.0) / 200.0 * 3.0)
    else if r < 2400 then 98.0 + ((rNum - 2200.0) / 200.0 * 1.5)
    else clampNumber 99.0 100.0 (99.5 + ((rNum - 2400.0) / 600.0 * 0.5))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // rating // tier
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get numeric tier (1-8) for matchmaking purposes.
-- |
-- | Tiers provide a coarse-grained skill grouping useful for
-- | matchmaking queues and bracket organization.
-- |
-- | - Tier 1: 0-800
-- | - Tier 2: 800-1200
-- | - Tier 3: 1200-1600
-- | - Tier 4: 1600-2000
-- | - Tier 5: 2000-2200
-- | - Tier 6: 2200-2400
-- | - Tier 7: 2400-2700
-- | - Tier 8: 2700+
ratingTier :: EloRating -> Int
ratingTier rating =
  let
    r = unwrapEloRating rating
  in
    if r < 800 then 1
    else if r < 1200 then 2
    else if r < 1600 then 3
    else if r < 2000 then 4
    else if r < 2200 then 5
    else if r < 2400 then 6
    else if r < 2700 then 7
    else 8
