-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // optimize // submodular // online // state
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Online State Management for Submodular Maximization.
-- |
-- | This module provides the complete state representation for online
-- | submodular maximization, including fractional solutions, gradient
-- | estimates, and algorithm configuration.
-- |
-- | ## Lean Correspondence
-- |
-- | | PureScript                  | Lean                        | Theorem/Definition      |
-- | |-----------------------------|-----------------------------|-------------------------|
-- | | `OnlineState.solution`      | Fractional point in P(M)    | RAOCO.lean:258          |
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Optimize.Submodular.Types (core types)
-- | - Hydrogen.Optimize.Submodular.Continuous (fractional solutions)
-- | - Hydrogen.Optimize.Submodular.Online.Config (configuration)
-- | - Hydrogen.Optimize.Submodular.Online.Regret (regret tracking)
-- | - Hydrogen.Optimize.Submodular.Online.Blackwell (approachability)

module Hydrogen.Optimize.Submodular.Online.State
  ( -- * Online State
    OnlineState(OnlineState)
  , mkOnlineState
  , resetOnlineState
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Show
  , negate
  , show
  , (-)
  , (<>)
  )

import Data.Map (Map)
import Data.Map as Map
import Data.Set as Set

import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Tensor.Dimension (Dim(Dim), unwrapDim)
import Hydrogen.Optimize.Submodular.Types
  ( ElementSet
  , GroundSet(GroundSet)
  , class Matroid
  , MatroidRank(MatroidRank)
  , maxRank
  )
import Hydrogen.Optimize.Submodular.Continuous
  ( FractionalSolution
  , zeroes
  )
import Hydrogen.Optimize.Submodular.Online.Config (OnlineConfig)
import Hydrogen.Optimize.Submodular.Online.Regret
  ( RegretState
  , mkRegretState
  )
import Hydrogen.Optimize.Submodular.Online.Blackwell
  ( BlackwellState
  , mkBlackwellState
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // online state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete state for online submodular maximization.
newtype OnlineState v = OnlineState
  { -- | Current fractional solution x ∈ P(M)
    solution :: FractionalSolution v
    
    -- | Cumulative gradient estimates
  , cumulativeGradient :: Map Int Number
  
    -- | Blackwell approachability state
  , blackwell :: BlackwellState
  
    -- | Regret tracking
  , regret :: RegretState
  
    -- | Current round
  , round :: Int
  
    -- | Last integral solution (for stability)
  , lastSelection :: ElementSet v
  
    -- | Configuration
  , config :: OnlineConfig
  
    -- | Ground set size (for bounds)
  , groundSetSize :: Int
  
    -- | Matroid rank (for bounds)
  , matroidRank :: Int
  }

instance showOnlineState :: Show (OnlineState v) where
  show (OnlineState s) = 
    "OnlineState{T=" <> show s.round <> ",regret=" <> show s.regret <> "}"

-- | Create initial online state.
mkOnlineState 
  :: forall m v
   . Matroid m v
  => m 
  -> GroundSet v 
  -> OnlineConfig 
  -> OnlineState v
mkOnlineState matroid groundSet@(GroundSet { size }) config =
  let
    (MatroidRank (Dim k)) = maxRank matroid
    n = unwrapDim size
    -- Approximation ratio for monotone + matroid
    alpha = 1.0 - Math.exp (negate 1.0)  -- 1 - 1/e ≈ 0.632
  in
    OnlineState
      { solution: zeroes groundSet
      , cumulativeGradient: Map.empty
      , blackwell: mkBlackwellState 2  -- 2D: (regret, variance)
      , regret: mkRegretState alpha
      , round: 0
      , lastSelection: Set.empty
      , config
      , groundSetSize: n
      , matroidRank: k
      }

-- | Reset online state (keep config, reset learning).
resetOnlineState :: forall v. GroundSet v -> OnlineState v -> OnlineState v
resetOnlineState groundSet (OnlineState s) =
  let
    alpha = 1.0 - Math.exp (negate 1.0)
  in
    OnlineState
      { solution: zeroes groundSet
      , cumulativeGradient: Map.empty
      , blackwell: mkBlackwellState 2
      , regret: mkRegretState alpha
      , round: 0
      , lastSelection: Set.empty
      , config: s.config
      , groundSetSize: s.groundSetSize
      , matroidRank: s.matroidRank
      }
