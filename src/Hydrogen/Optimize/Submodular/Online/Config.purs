-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // optimize // submodular // online // config
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Online Algorithm Configuration and Utility Feedback.
-- |
-- | This module provides configuration types for online submodular maximization
-- | and utility feedback structures for adversarial reveals.
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Math.Core (clamping)

module Hydrogen.Optimize.Submodular.Online.Config
  ( -- * Algorithm Configuration
    OnlineConfig(OnlineConfig)
  , mkOnlineConfig
  , defaultOnlineConfig
  
  -- * Utility Feedback
  , UtilityFeedback(UtilityFeedback)
  , mkUtilityFeedback
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Data.Map (Map)
import Data.Map as Map

import Hydrogen.Math.Core as Math

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // online configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for online submodular maximization.
newtype OnlineConfig = OnlineConfig
  { -- | Learning rate schedule: η_t = baseRate / √t
    baseLearningRate :: Number
    
    -- | Exploration parameter for gradient estimation
  , explorationRate :: Number
  
    -- | Number of samples for gradient estimation per round
  , samplesPerRound :: Int
  
    -- | Rounding frequency: round every K rounds
  , roundingFrequency :: Int
  
    -- | Random seed for reproducibility
  , seed :: Number
  
    -- | Whether to use adaptive step sizes
  , adaptiveSteps :: Boolean
  }

derive instance eqOnlineConfig :: Eq OnlineConfig

instance showOnlineConfig :: Show OnlineConfig where
  show (OnlineConfig c) = 
    "OnlineConfig{η=" <> show c.baseLearningRate <> "}"

-- | Create online configuration with sensible defaults.
mkOnlineConfig :: Number -> OnlineConfig
mkOnlineConfig baseLearningRate = OnlineConfig
  { baseLearningRate: Math.clamp 0.001 10.0 baseLearningRate
  , explorationRate: 0.01
  , samplesPerRound: 10
  , roundingFrequency: 60
  , seed: 42.0
  , adaptiveSteps: true
  }

-- | Default configuration optimized for 60fps rendering.
defaultOnlineConfig :: OnlineConfig
defaultOnlineConfig = OnlineConfig
  { baseLearningRate: 1.0
  , explorationRate: 0.01
  , samplesPerRound: 5
  , roundingFrequency: 60
  , seed: 42.0
  , adaptiveSteps: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // utility feedback
-- ═════════════════════════════════════════════════════════════════════════════

-- | Utility feedback from the environment (adversary's reveal).
-- |
-- | In the viewport allocation context:
-- | - utilityValue: quality achieved given the selection
-- | - executionTime: GPU time consumed
-- | - qualityMetrics: per-region quality measurements
newtype UtilityFeedback :: Type -> Type
newtype UtilityFeedback v = UtilityFeedback
  { utilityValue :: Number              -- ^ f_t(S_t)
  , executionTime :: Number             -- ^ GPU time in ms
  , qualityMetrics :: Map Int Number    -- ^ Per-element quality
  , round :: Int                        -- ^ Round number
  }

derive instance eqUtilityFeedback :: Eq (UtilityFeedback v)

instance showUtilityFeedback :: Show (UtilityFeedback v) where
  show (UtilityFeedback f) = 
    "Utility{v=" <> show f.utilityValue <> ",t=" <> show f.round <> "}"

-- | Create utility feedback.
mkUtilityFeedback :: forall v. Number -> Number -> Int -> UtilityFeedback v
mkUtilityFeedback utilityValue executionTime round = UtilityFeedback
  { utilityValue
  , executionTime
  , qualityMetrics: Map.empty
  , round
  }
