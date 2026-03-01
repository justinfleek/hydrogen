-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // optimize // submodular // online
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Online Submodular Maximization via First-Order Regret Bounds.
-- |
-- | ## Theoretical Foundation
-- |
-- | This module implements the Harvey/Liaw/Soma (NeurIPS 2020) algorithm for
-- | online submodular maximization with first-order regret bounds.
-- |
-- | **Key Result**: O(√(kT ln(n/k))) expected α-regret for monotone + matroid
-- |
-- | The algorithm maintains a fractional solution x ∈ P(M) (matroid polytope)
-- | and updates it via online gradient descent with Blackwell approachability.
-- |
-- | ## Online Model
-- |
-- | At each round t:
-- | 1. Algorithm selects set Sₜ ∈ I (independent in matroid M)
-- | 2. Adversary reveals submodular function fₜ
-- | 3. Algorithm receives utility fₜ(Sₜ)
-- | 4. Algorithm updates internal state
-- |
-- | The adversary IS reality: fₜ is revealed by actual GPU execution.
-- |
-- | ## Blackwell Approachability
-- |
-- | The algorithm uses Blackwell's approachability theorem to convert
-- | vector-valued payoffs into scalar regret bounds. This enables:
-- |
-- | - First-order regret: bounds depend on actual gains, not worst-case
-- | - Adaptive learning rates: faster convergence when problem is "easy"
-- | - Anytime guarantees: valid regret bound at any stopping time
-- |
-- | ## References
-- |
-- | - Harvey, Liaw, Soma. "Improved Algorithms for Online Submodular
-- |   Maximization via First-order Regret Bounds" NeurIPS 2020
-- | - Blackwell, D. "An Analog of the Minimax Theorem for Vector Payoffs"
-- |   Pacific J. Math. 6(1), 1-8 (1956)
-- | - Si Salem et al. "Online Submodular Maximization via Online Convex
-- |   Optimization" arXiv:2309.04339v4 (January 2024)
-- |
-- | ## Lean4 Proof Correspondence
-- |
-- | This module implements algorithms proven correct in:
-- |
-- | - `proofs/Hydrogen/Optimize/Submodular/RAOCO.lean`
-- |   - `raoco_reduction`: α-regret_T(P_X) ≤ α · regret_T(P_Y)
-- |   - `wtp_matroid_raoco`: (1-1/e)-regret = O(√T) for WTP over matroids
-- |   - `thresholdPotential`: Weighted threshold potential definition
-- |
-- | - `proofs/Hydrogen/Optimize/Submodular/ContinuousGreedy.lean`
-- |   - `continuous_greedy_guarantee`: F(x_T) ≥ (1-(1-1/T)^T)·OPT
-- |   - `full_pipeline_guarantee`: Rounding preserves approximation
-- |
-- | - `proofs/Hydrogen/Optimize/Submodular/Matroid.lean`
-- |   - `Matroid`: Independence system axioms (I1, I2, I3)
-- |   - `inPolytope`: Matroid polytope membership
-- |   - `matroidRank`: Rank of full ground set
-- |
-- | - `proofs/Hydrogen/Optimize/Submodular/Core.lean`
-- |   - `FractionalSolution`: coords ∈ [0,1]^V with proof obligations
-- |   - `IsSubmodular`: Diminishing returns property
-- |   - `multilinearExt`: Extension to continuous domain
-- |
-- | ## Type Correspondence
-- |
-- | | PureScript                  | Lean                        | Theorem/Definition      |
-- | |-----------------------------|-----------------------------|-------------------------|
-- | | `FractionalSolution v`      | `FractionalSolution V`      | Core.lean:232           |
-- | | `MatroidPolytope m v`       | `inPolytope M x`            | Matroid.lean:155        |
-- | | `solutionGroundSetSize`     | `Fintype.card V`            | Matroid.lean:259        |
-- | | `polytopeGroundSet`         | Ground set `V`              | Matroid.lean:158        |
-- | | `OnlineState.solution`      | Fractional point in P(M)    | RAOCO.lean:258          |
-- | | `RegretState.alpha`         | `α = (1-1/Δ)^Δ`             | RAOCO.lean:122          |
-- |
-- | ## Module Structure
-- |
-- | This leader module re-exports from:
-- | - `Online.Config`: Configuration and utility feedback
-- | - `Online.Regret`: Regret tracking and first-order bounds
-- | - `Online.Blackwell`: Blackwell approachability
-- | - `Online.State`: Online algorithm state
-- | - `Online.Algorithm`: Core algorithm and utilities
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Optimize.Submodular.Types (core types)
-- | - Hydrogen.Optimize.Submodular.Continuous (fractional solutions)
-- | - Hydrogen.Math.Core (exp, log, sqrt)

module Hydrogen.Optimize.Submodular.Online
  ( -- * Re-exports from submodules
    module Config
  , module Regret  
  , module Blackwell
  , module State
  , module Algorithm
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

-- Re-export from Config
import Hydrogen.Optimize.Submodular.Online.Config
  ( OnlineConfig(OnlineConfig)
  , mkOnlineConfig
  , defaultOnlineConfig
  , UtilityFeedback(UtilityFeedback)
  , mkUtilityFeedback
  ) as Config

-- Re-export from Regret
import Hydrogen.Optimize.Submodular.Online.Regret
  ( RegretState(RegretState)
  , mkRegretState
  , updateRegret
  , currentRegret
  , regretBound
  , isWithinBound
  , firstOrderBound
  , adaptiveStepSize
  ) as Regret

-- Re-export from Blackwell
import Hydrogen.Optimize.Submodular.Online.Blackwell
  ( BlackwellState(BlackwellState)
  , mkBlackwellState
  , blackwellUpdate
  , blackwellResponse
  ) as Blackwell

-- Re-export from State
import Hydrogen.Optimize.Submodular.Online.State
  ( OnlineState(OnlineState)
  , mkOnlineState
  , resetOnlineState
  ) as State

-- Re-export from Algorithm
import Hydrogen.Optimize.Submodular.Online.Algorithm
  ( onlineStep
  , onlineRound
  , runOnline
  , isWarmupPhase
  , groundSetDimension
  , solutionFromCoords
  , getSolutionCoord
  , solutionGroundSetSize
  , polytopeGroundSet
  ) as Algorithm
