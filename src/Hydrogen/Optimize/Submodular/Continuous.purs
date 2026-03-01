-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // optimize // submodular // continuous
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Continuous Relaxation for Submodular Optimization.
-- |
-- | ## Theoretical Foundation
-- |
-- | The multilinear extension F : [0,1]^n → ℝ of f : 2^V → ℝ is:
-- |
-- |   F(x) = 𝔼_{S ~ x}[f(S)] = Σ_{S ⊆ V} f(S) ∏_{e ∈ S} x_e ∏_{e ∉ S} (1 - x_e)
-- |
-- | Where S ~ x means each element e is included independently with probability x_e.
-- |
-- | Key properties:
-- | - F(1_S) = f(S) for indicator vectors
-- | - F is multilinear (linear in each coordinate)
-- | - ∂F/∂x_e = 𝔼_{S ~ x_{-e}}[f(S ∪ {e}) - f(S)] (expected marginal gain)
-- | - F is concave along any direction if f is submodular
-- |
-- | ## Gradient Estimation
-- |
-- | Computing F(x) exactly requires exponentially many evaluations.
-- | We use two-point gradient estimation:
-- |
-- |   ∇F(x) ≈ (F(x + δ) - F(x - δ)) / (2δ) · d
-- |
-- | Where d is the perturbation direction.
-- |
-- | For coordinates: ∂F/∂x_e ≈ (f(S ∪ {e}) - f(S)) sampled over S ~ x.
-- |
-- | ## Frank-Wolfe Algorithm
-- |
-- | Continuous greedy maximizes F over the matroid polytope:
-- |
-- |   x_{t+1} = x_t + (1/T) · v_t
-- |
-- | Where v_t = argmax_{v ∈ P} ⟨∇F(x_t), v⟩ is a linear maximization oracle.
-- |
-- | For matroid polytopes, this reduces to greedy selection.
-- |
-- | ## Billion-Agent Context
-- |
-- | Continuous relaxation enables:
-- | - Fractional solutions for load balancing across agents
-- | - Smooth optimization landscapes for gradient methods
-- | - Provable approximation guarantees with rounding
-- |
-- | Agents can solve relaxed problems independently, then coordinate rounding.
-- |
-- | ## References
-- |
-- | - Vondrák, J. "Optimal approximation for the submodular welfare problem
-- |   in the value oracle model" STOC 2008
-- | - Calinescu et al. "Maximizing a Monotone Submodular Function Subject
-- |   to a Matroid Constraint" SICOMP 2011
-- |
-- | ## Module Structure
-- |
-- | This leader module re-exports from submodules:
-- | - Continuous.Utilities: Number/Int conversion helpers
-- | - Continuous.FractionalSolution: Fractional points in [0,1]^n
-- | - Continuous.Multilinear: Multilinear extension evaluation
-- | - Continuous.MatroidPolytope: Polytope membership and optimization
-- | - Continuous.Greedy: Standard continuous greedy algorithm
-- | - Continuous.FAA: FAA-enhanced continuous greedy (√T speedup)
-- | - Continuous.Gradient: Gradient estimation methods
-- | - Continuous.Rounding: Converting fractional to discrete solutions

module Hydrogen.Optimize.Submodular.Continuous
  ( -- * Fractional Solution
    module FractionalSolution
  
  -- * Multilinear Extension
  , module Multilinear
  
  -- * Matroid Polytope
  , module MatroidPolytope
  
  -- * Continuous Greedy
  , module Greedy
  
  -- * FAA-Enhanced Continuous Greedy
  , module FAA
  
  -- * Gradient Estimation
  , module Gradient
  
  -- * Solution Rounding
  , module Rounding
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Optimize.Submodular.Continuous.FractionalSolution
  ( FractionalSolution(FractionalSolution)
  , mkFractionalSolution
  , mkFractionalSolutionBounded
  , solutionValue
  , solutionValueBounded
  , solutionCoord
  , solutionCoordBounded
  , solutionCoords
  , solutionSupport
  , zeroes
  , ones
  , uniform
  , addScaled
  ) as FractionalSolution

import Hydrogen.Optimize.Submodular.Continuous.Multilinear
  ( MultilinearExt(MultilinearExt)
  , mkMultilinearExt
  , evalMultilinear
  , evalMultilinearSampled
  , partialDerivative
  , gradientSampled
  , sampleOnce
  ) as Multilinear

import Hydrogen.Optimize.Submodular.Continuous.MatroidPolytope
  ( MatroidPolytope(MatroidPolytope)
  , mkMatroidPolytope
  , isInPolytope
  , linearMaximize
  ) as MatroidPolytope

import Hydrogen.Optimize.Submodular.Continuous.Greedy
  ( ContinuousGreedyConfig(ContinuousGreedyConfig)
  , mkContinuousGreedyConfig
  , continuousGreedy
  , continuousGreedyStep
  ) as Greedy

import Hydrogen.Optimize.Submodular.Continuous.FAA
  ( FAAConfig(FAAConfig)
  , mkFAAConfig
  , continuousGreedyFAA
  , continuousGreedyStepFAA
  , faaStepSize
  , faaIterations
  ) as FAA

import Hydrogen.Optimize.Submodular.Continuous.Gradient
  ( GradientEstimate(GradientEstimate)
  , twoPointEstimate
  , coordinateGradient
  , stochasticGradient
  ) as Gradient

import Hydrogen.Optimize.Submodular.Continuous.Rounding
  ( sampleSolution
  , thresholdRound
  , dependentRound
  ) as Rounding
