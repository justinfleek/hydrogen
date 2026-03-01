-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // optimize // submodular // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core Type System for Online Submodular Maximization.
-- |
-- | ## Theoretical Foundation
-- |
-- | This module implements the type-theoretic foundation for Harvey/Liaw/Soma's
-- | online submodular maximization algorithm (NeurIPS 2020). The key result:
-- |
-- | **O(√(kT ln(n/k))) first-order regret for monotone + matroid constraint**
-- |
-- | Where:
-- | - k = rank of matroid (max independent set size)
-- | - T = time horizon (number of rounds)
-- | - n = ground set size
-- |
-- | ## Design Philosophy
-- |
-- | Submodularity is the discrete analog of concavity. A function f : 2^V → ℝ
-- | is submodular iff for all A ⊆ B and e ∉ B:
-- |
-- |   f(A ∪ {e}) - f(A) ≥ f(B ∪ {e}) - f(B)
-- |
-- | This is the **diminishing returns** property: adding an element to a smaller
-- | set gives at least as much gain as adding it to a larger set.
-- |
-- | We encode this property directly in the type system using phantom types
-- | that track monotonicity, curvature bounds, and approximation ratios.
-- |
-- | ## Billion-Agent Context
-- |
-- | At billion-agent swarm scale, submodular optimization enables:
-- | - **Widget allocation**: Select k UI components maximizing engagement
-- | - **Attention routing**: Choose which elements get rendered first
-- | - **Resource scheduling**: Allocate compute across rendering tasks
-- | - **Feature selection**: Pick which brand atoms to include in design
-- |
-- | Each agent must reach the same decision given the same state. The type
-- | system guarantees this by making approximation ratios explicit.
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports types from submodules:
-- | - Types.GroundSet - Ground set elements
-- | - Types.Classification - Monotonicity and curvature
-- | - Types.Function - Submodular function and oracle types
-- | - Types.Matroid - Matroid constraints and instances
-- | - Types.Approximation - Approximation ratio phantom types
-- | - Types.Online - Online learning state and graded monad
-- | - Types.Blackwell - Blackwell approachability types
-- | - Types.Config - Algorithm configuration
-- |
-- | ## References
-- |
-- | - Harvey, Liaw, Soma. "Improved Online Submodular Maximization"
-- |   NeurIPS 2020, arXiv:2007.09231
-- | - Blackwell, D. "An analog of the minimax theorem for vector payoffs"
-- |   Pacific J. Math. 6(1), 1-8 (1956)

module Hydrogen.Optimize.Submodular.Types
  ( -- * Ground Set Elements (from Types.GroundSet)
    module Hydrogen.Optimize.Submodular.Types.GroundSet
    
    -- * Submodular Function Classification (from Types.Classification)
  , module Hydrogen.Optimize.Submodular.Types.Classification
  
    -- * Core Submodular Function Type (from Types.Function)
  , module Hydrogen.Optimize.Submodular.Types.Function
  
    -- * Matroid Constraints (from Types.Matroid)
  , module Hydrogen.Optimize.Submodular.Types.Matroid
  
    -- * Approximation Ratios (from Types.Approximation)
  , module Hydrogen.Optimize.Submodular.Types.Approximation
  
    -- * Online Learning State (from Types.Online)
  , module Hydrogen.Optimize.Submodular.Types.Online
  
    -- * Blackwell Approachability (from Types.Blackwell)
  , module Hydrogen.Optimize.Submodular.Types.Blackwell
  
    -- * Algorithm Configuration (from Types.Config)
  , module Hydrogen.Optimize.Submodular.Types.Config
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Optimize.Submodular.Types.GroundSet
  ( Element(Element)
  , ElementSet
  , GroundSet(GroundSet)
  )

import Hydrogen.Optimize.Submodular.Types.Classification
  ( Monotonicity(Monotone, NonMonotone)
  , Curvature(CurvatureUnknown, CurvatureBounded, CurvatureExact)
  , CurvatureWitness(CurvatureWitness)
  )

import Hydrogen.Optimize.Submodular.Types.Function
  ( SubmodularFn
  , SubmodularOracle(SubmodularOracle)
  , MarginalGain(MarginalGain)
  , SetValue(SetValue)
  )

import Hydrogen.Optimize.Submodular.Types.Matroid
  ( class Matroid
  , rank
  , maxRank
  , isIndependent
  , canExtend
  , extensionElements
  , MatroidRank(MatroidRank)
  , IndependentSet
  , CardinalityMatroid(CardinalityMatroid)
  , PartitionMatroid(PartitionMatroid)
  , PartitionBlock(PartitionBlock)
  , UniformMatroid(UniformMatroid)
  , GraphicMatroid(GraphicMatroid)
  )

import Hydrogen.Optimize.Submodular.Types.Approximation
  ( ApproxRatio(ExactRatio, MonotoneMatroidRatio, NonMonotoneMatroidRatio, HalfRatio, CustomRatio)
  , AlphaRegret(AlphaRegret)
  , MonotoneOPT
  , NonMonotoneOPT
  )

import Hydrogen.Optimize.Submodular.Types.Online
  ( TimeHorizon(TimeHorizon)
  , Round(Round)
  , CumulativeGradient(CumulativeGradient)
  , DualVariable(DualVariable)
  , RegretBound(RegretBound)
  , OnlineGrade(OnlineGrade)
  , OnlineLearn
  )

import Hydrogen.Optimize.Submodular.Types.Blackwell
  ( TargetSet(TargetSet)
  , ResponseSet(ResponseSet)
  , PayoffVector(PayoffVector)
  )

import Hydrogen.Optimize.Submodular.Types.Config
  ( SamplingRate(SamplingRate)
  , StepSize(StepSize)
  , PiPage(DeterministicPipage, RandomizedPipage, ContiguousPipage, SwapPipage)
  )
