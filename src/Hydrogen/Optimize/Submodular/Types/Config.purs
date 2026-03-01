-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // submodular // config
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Algorithm Configuration Types for Submodular Maximization.
-- |
-- | Configuration parameters for:
-- | - Continuous-to-discrete rounding (sampling rate)
-- | - Gradient-based updates (step size)
-- | - Pipage rounding strategies
-- |
-- | ## Theoretical Constraints
-- |
-- | - Step size η typically O(1/√T) or O(1/√t) for regret bounds
-- | - Sampling rate ρ ∈ [0, 1] is a probability
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)

module Hydrogen.Optimize.Submodular.Types.Config
  ( SamplingRate(SamplingRate)
  , StepSize(StepSize)
  , PiPage
      ( DeterministicPipage
      , RandomizedPipage
      , ContiguousPipage
      , SwapPipage
      )
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // algorithm configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sampling rate for continuous-to-discrete rounding.
-- |
-- | In continuous relaxation algorithms, we maintain x ∈ [0,1]^n
-- | and round to discrete solutions with rate ρ.
-- |
-- | Bounded to [0, 1] (probability).
newtype SamplingRate = SamplingRate Number

derive instance eqSamplingRate :: Eq SamplingRate
derive instance ordSamplingRate :: Ord SamplingRate

instance showSamplingRate :: Show SamplingRate where
  show (SamplingRate r) = "ρ=" <> show r

-- | Step size for gradient-based updates.
-- |
-- | η controls the learning rate. For regret bounds to hold,
-- | typically η = O(1/√T) or η = O(1/√t) (adaptive).
-- |
-- | Bounded to (0, 1] for stability.
newtype StepSize = StepSize Number

derive instance eqStepSize :: Eq StepSize
derive instance ordStepSize :: Ord StepSize

instance showStepSize :: Show StepSize where
  show (StepSize η) = "η=" <> show η

-- | Pipage rounding parameter.
-- |
-- | Controls how continuous solutions are rounded to discrete
-- | while preserving the value (in expectation for randomized rounding,
-- | or exactly for pipage rounding).
-- |
-- | The PiPage type encapsulates the rounding strategy and its parameters.
data PiPage
  = DeterministicPipage      -- ^ Deterministic pipage rounding
  | RandomizedPipage Number  -- ^ Randomized with given rate
  | ContiguousPipage         -- ^ Contiguous rounding (for matroids)
  | SwapPipage               -- ^ Swap-based rounding

derive instance eqPiPage :: Eq PiPage

instance showPiPage :: Show PiPage where
  show DeterministicPipage = "Pipage[det]"
  show (RandomizedPipage r) = "Pipage[rand=" <> show r <> "]"
  show ContiguousPipage = "Pipage[contig]"
  show SwapPipage = "Pipage[swap]"
