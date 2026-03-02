-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // game // score // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core data types for scoring and rating systems.
-- |
-- | This module defines the atomic vocabulary for competitive game scoring:
-- | - Elo ratings with bounded domains (0-4000)
-- | - K-factors for rating volatility (10-40)
-- | - Glicko ratings with uncertainty tracking
-- | - Game outcomes and rating changes
-- | - Achievement rarity system
-- |
-- | All types use bounded domains to ensure deterministic behavior at
-- | billion-agent scale.

module Hydrogen.Schema.Game.Score.Types
  ( -- * Elo Rating
    EloRating
  , eloRating
  , unwrapEloRating
  , eloRatingBounds
  , defaultEloRating
  , clampEloRating
  
  -- * K-Factor
  , KFactor(KFactor)
  , kFactor
  , unwrapKFactor
  , kFactorBounds
  , provisionalKFactor
  , masterKFactor
  
  -- * Rating Deviation (Glicko)
  , RatingDeviation(RatingDeviation)
  , ratingDeviation
  , unwrapRatingDeviation
  , ratingDeviationBounds
  , defaultRatingDeviation
  
  -- * Glicko Rating
  , GlickoRating
  , defaultGlickoRating
  
  -- * Game Outcome
  , GameOutcome(Win, Loss, Draw)
  , outcomeValue
  , invertOutcome
  
  -- * Rating Change
  , RatingChange
  , ratingChangeAmount
  , isPositiveChange
  
  -- * Achievement Rarity
  , AchievementRarity(Common, Uncommon, Rare, Epic, Legendary)
  , allRarities
  , rarityMultiplier
  , rarityThreshold
  
  -- * Achievement
  , Achievement
  
  -- * Score Breakdown
  , ScoreBreakdown
  , module Internal
  
  -- * Leaderboard
  , LeaderboardEntry
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , negate
  , (+)
  , (-)
  , (>)
  , (<>)
  )

import Hydrogen.Schema.Bounded
  ( IntBounds
  , NumberBounds
  , BoundsBehavior(Clamps)
  , intBounds
  , numberBounds
  , clampInt
  , clampNumber
  )

import Hydrogen.Schema.Game.Score.Internal (Bonus, intToNumber, absInt) as Internal

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // elo // rating
-- ═════════════════════════════════════════════════════════════════════════════

-- | Elo rating bounded 0-4000.
-- |
-- | Standard chess rating scale: 
-- | - Beginners: 0-1200
-- | - Intermediate: 1200-1600
-- | - Advanced: 1600-2000
-- | - Expert: 2000-2200
-- | - Master: 2200-2400
-- | - Grandmaster: 2400+
-- | - Super GM: 2700+
-- | - World Champion: 2800+
newtype EloRating = EloRating Int

derive instance eqEloRating :: Eq EloRating
derive instance ordEloRating :: Ord EloRating

instance showEloRating :: Show EloRating where
  show (EloRating r) = "EloRating " <> show r

-- | Smart constructor for Elo rating, clamped to 0-4000.
eloRating :: Int -> EloRating
eloRating n = EloRating (clampInt 0 4000 n)

-- | Extract raw Elo value.
unwrapEloRating :: EloRating -> Int
unwrapEloRating (EloRating r) = r

-- | Bounds documentation for Elo rating.
eloRatingBounds :: IntBounds
eloRatingBounds = intBounds 0 4000 Clamps "elo" "Elo rating (0-4000)"

-- | Default starting Elo rating (1200 for beginners, 1500 for standard).
defaultEloRating :: EloRating
defaultEloRating = EloRating 1200

-- | Clamp an integer to valid Elo range.
clampEloRating :: Int -> EloRating
clampEloRating = eloRating

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // k // factor
-- ═════════════════════════════════════════════════════════════════════════════

-- | K-factor for Elo calculations, bounded 10-40.
-- |
-- | Higher K = more volatile ratings (for new players).
-- | Lower K = more stable ratings (for established players).
-- |
-- | - Provisional (new players): 40
-- | - Standard: 20
-- | - Master (2400+): 10
newtype KFactor = KFactor Int

derive instance eqKFactor :: Eq KFactor
derive instance ordKFactor :: Ord KFactor

instance showKFactor :: Show KFactor where
  show (KFactor k) = "KFactor " <> show k

-- | Smart constructor for K-factor, clamped to 10-40.
kFactor :: Int -> KFactor
kFactor n = KFactor (clampInt 10 40 n)

-- | Extract raw K-factor value.
unwrapKFactor :: KFactor -> Int
unwrapKFactor (KFactor k) = k

-- | Bounds documentation for K-factor.
kFactorBounds :: IntBounds
kFactorBounds = intBounds 10 40 Clamps "k-factor" "K-factor for Elo (10-40)"

-- | K-factor for provisional (new) players.
provisionalKFactor :: KFactor
provisionalKFactor = KFactor 40

-- | K-factor for master-level players.
masterKFactor :: KFactor
masterKFactor = KFactor 10

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // rating // deviation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rating deviation for Glicko system.
-- |
-- | Measures uncertainty in a player's rating.
-- | - Low RD (30-50): Very certain rating
-- | - Medium RD (50-100): Moderately certain
-- | - High RD (100-350): Uncertain (inactive or new player)
-- |
-- | Bounded 30-350 (Glicko standard range).
newtype RatingDeviation = RatingDeviation Number

derive instance eqRatingDeviation :: Eq RatingDeviation
derive instance ordRatingDeviation :: Ord RatingDeviation

instance showRatingDeviation :: Show RatingDeviation where
  show (RatingDeviation rd) = "RatingDeviation " <> show rd

-- | Smart constructor for rating deviation, clamped to 30-350.
ratingDeviation :: Number -> RatingDeviation
ratingDeviation n = RatingDeviation (clampNumber 30.0 350.0 n)

-- | Extract raw rating deviation value.
unwrapRatingDeviation :: RatingDeviation -> Number
unwrapRatingDeviation (RatingDeviation rd) = rd

-- | Bounds documentation for rating deviation.
ratingDeviationBounds :: NumberBounds
ratingDeviationBounds = numberBounds 30.0 350.0 Clamps "rd" "Rating deviation (30-350)"

-- | Default rating deviation for new players (maximum uncertainty).
defaultRatingDeviation :: RatingDeviation
defaultRatingDeviation = RatingDeviation 350.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // glicko // rating
-- ═════════════════════════════════════════════════════════════════════════════

-- | Glicko rating with uncertainty tracking.
-- |
-- | Extension of Elo that tracks:
-- | - `rating`: Current skill estimate (like Elo, typically 1500 base)
-- | - `deviation`: Uncertainty in rating (decreases with more games)
-- | - `volatility`: Expected fluctuation in rating (Glicko-2)
type GlickoRating =
  { rating :: Number
  , deviation :: RatingDeviation
  , volatility :: Number
  }

-- | Default Glicko rating for new players.
defaultGlickoRating :: GlickoRating
defaultGlickoRating =
  { rating: 1500.0
  , deviation: defaultRatingDeviation
  , volatility: 0.06
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // game // outcome
-- ═════════════════════════════════════════════════════════════════════════════

-- | Result of a game for rating calculation.
data GameOutcome
  = Win   -- ^ Player won (score = 1.0)
  | Loss  -- ^ Player lost (score = 0.0)
  | Draw  -- ^ Game was drawn (score = 0.5)

derive instance eqGameOutcome :: Eq GameOutcome
derive instance ordGameOutcome :: Ord GameOutcome

instance showGameOutcome :: Show GameOutcome where
  show Win = "Win"
  show Loss = "Loss"
  show Draw = "Draw"

-- | Numeric value of outcome for Elo calculation.
outcomeValue :: GameOutcome -> Number
outcomeValue Win = 1.0
outcomeValue Loss = 0.0
outcomeValue Draw = 0.5

-- | Get the opposite outcome (from opponent's perspective).
invertOutcome :: GameOutcome -> GameOutcome
invertOutcome Win = Loss
invertOutcome Loss = Win
invertOutcome Draw = Draw

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // rating // change
-- ═════════════════════════════════════════════════════════════════════════════

-- | Record of a rating change after a game.
type RatingChange =
  { before :: EloRating
  , after :: EloRating
  , change :: Int
  }

-- | Get the magnitude of rating change.
ratingChangeAmount :: RatingChange -> Int
ratingChangeAmount rc = Internal.absInt rc.change

-- | Check if the rating change was positive.
isPositiveChange :: RatingChange -> Boolean
isPositiveChange rc = rc.change > 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // achievement // rarity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rarity levels for achievements.
data AchievementRarity
  = Common      -- ^ ~50% of players earn this
  | Uncommon    -- ^ ~25% of players earn this
  | Rare        -- ^ ~10% of players earn this
  | Epic        -- ^ ~1% of players earn this
  | Legendary   -- ^ <0.1% of players earn this

derive instance eqAchievementRarity :: Eq AchievementRarity
derive instance ordAchievementRarity :: Ord AchievementRarity

instance showAchievementRarity :: Show AchievementRarity where
  show Common = "Common"
  show Uncommon = "Uncommon"
  show Rare = "Rare"
  show Epic = "Epic"
  show Legendary = "Legendary"

-- | All achievement rarities in order.
allRarities :: Array AchievementRarity
allRarities = [Common, Uncommon, Rare, Epic, Legendary]

-- | Point multiplier based on rarity.
rarityMultiplier :: AchievementRarity -> Number
rarityMultiplier Common = 1.0
rarityMultiplier Uncommon = 2.0
rarityMultiplier Rare = 5.0
rarityMultiplier Epic = 10.0
rarityMultiplier Legendary = 25.0

-- | Approximate percentage of players who earn this rarity.
rarityThreshold :: AchievementRarity -> Number
rarityThreshold Common = 50.0
rarityThreshold Uncommon = 25.0
rarityThreshold Rare = 10.0
rarityThreshold Epic = 1.0
rarityThreshold Legendary = 0.1

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // achievement
-- ═════════════════════════════════════════════════════════════════════════════

-- | Achievement definition.
type Achievement =
  { id :: String
  , name :: String
  , description :: String
  , points :: Int
  , rarity :: AchievementRarity
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // score // breakdown
-- ═════════════════════════════════════════════════════════════════════════════

-- | Breakdown of a score calculation.
type ScoreBreakdown =
  { base :: Int
  , multiplier :: Number
  , bonuses :: Array Internal.Bonus
  , total :: Int
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // leaderboard
-- ═════════════════════════════════════════════════════════════════════════════

-- | Entry on a leaderboard.
type LeaderboardEntry =
  { rank :: Int
  , playerId :: String
  , rating :: EloRating
  , wins :: Int
  , losses :: Int
  , draws :: Int
  }
