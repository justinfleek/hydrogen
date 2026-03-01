-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                  // hydrogen // optimize // submodular // continuous // greedy
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Continuous Greedy Algorithm for Submodular Maximization.
-- |
-- | ## Algorithm
-- |
-- | Continuous greedy maximizes F(x) over the matroid polytope:
-- |
-- |   x_{t+1} = x_t + (1/T) · v_t
-- |
-- | Where v_t = argmax_{v ∈ P(M)} ⟨∇F(x_t), v⟩ is a linear maximization oracle.
-- |
-- | For matroid polytopes, this reduces to greedy selection.
-- |
-- | ## Approximation Guarantee
-- |
-- | Returns fractional solution achieving (1 - 1/e) approximation for
-- | maximizing a monotone submodular function subject to matroid constraint.
-- |
-- | ## References
-- |
-- | - Calinescu et al. "Maximizing a Monotone Submodular Function Subject
-- |   to a Matroid Constraint" SICOMP 2011
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Optimize.Submodular.Continuous.FractionalSolution
-- | - Hydrogen.Optimize.Submodular.Continuous.Multilinear
-- | - Hydrogen.Optimize.Submodular.Continuous.MatroidPolytope

module Hydrogen.Optimize.Submodular.Continuous.Greedy
  ( ContinuousGreedyConfig(ContinuousGreedyConfig)
  , mkContinuousGreedyConfig
  , continuousGreedy
  , continuousGreedyStep
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , (+)
  , (*)
  , (/)
  , (>=)
  )

import Hydrogen.Optimize.Submodular.Types
  ( Element
  , SubmodularOracle(SubmodularOracle)
  , class Matroid
  )
import Hydrogen.Optimize.Submodular.Continuous.FractionalSolution
  ( FractionalSolution
  , zeroes
  , addScaled
  )
import Hydrogen.Optimize.Submodular.Continuous.Multilinear
  ( MultilinearExt
  , mkMultilinearExt
  , gradientSampled
  )
import Hydrogen.Optimize.Submodular.Continuous.MatroidPolytope
  ( MatroidPolytope
  , mkMatroidPolytope
  , linearMaximize
  )
import Hydrogen.Optimize.Submodular.Continuous.Utilities (intToNum)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for continuous greedy algorithm.
newtype ContinuousGreedyConfig = ContinuousGreedyConfig
  { numIterations :: Int       -- ^ T: number of iterations
  , samplesPerGradient :: Int  -- ^ Samples for gradient estimation
  , seed :: Number             -- ^ Random seed for reproducibility
  }

derive instance eqContinuousGreedyConfig :: Eq ContinuousGreedyConfig

-- | Create continuous greedy config with sensible defaults.
mkContinuousGreedyConfig :: Int -> ContinuousGreedyConfig
mkContinuousGreedyConfig numIterations = ContinuousGreedyConfig
  { numIterations
  , samplesPerGradient: 10
  , seed: 42.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // continuous greedy
-- ═════════════════════════════════════════════════════════════════════════════

-- | Continuous greedy algorithm for submodular maximization.
-- |
-- | Maximizes F(x) over matroid polytope P(M).
-- |
-- | x_0 = 0
-- | For t = 0, ..., T-1:
-- |   v_t = argmax_{v ∈ P(M)} ⟨∇F(x_t), v⟩
-- |   x_{t+1} = x_t + (1/T) · v_t
-- |
-- | Returns fractional solution achieving (1 - 1/e) approximation.
continuousGreedy 
  :: forall m v
   . Ord (Element v)
  => Matroid m v 
  => m 
  -> SubmodularOracle v 
  -> ContinuousGreedyConfig 
  -> FractionalSolution v
continuousGreedy matroid oracle config =
  let ext = mkMultilinearExt oracle
      (SubmodularOracle { groundSet }) = oracle
      polytope = mkMatroidPolytope matroid groundSet
      initial = zeroes groundSet
  in continuousGreedyLoop ext polytope config initial 0

-- | Continuous greedy iteration loop.
continuousGreedyLoop 
  :: forall m v
   . Ord (Element v)
  => Matroid m v 
  => MultilinearExt v 
  -> MatroidPolytope m v 
  -> ContinuousGreedyConfig 
  -> FractionalSolution v 
  -> Int 
  -> FractionalSolution v
continuousGreedyLoop ext polytope config@(ContinuousGreedyConfig { numIterations }) current t =
  if t >= numIterations
    then current
    else
      let next = continuousGreedyStep ext polytope config current t
      in continuousGreedyLoop ext polytope config next (t + 1)

-- | Single step of continuous greedy.
continuousGreedyStep 
  :: forall m v
   . Ord (Element v)
  => Matroid m v 
  => MultilinearExt v 
  -> MatroidPolytope m v 
  -> ContinuousGreedyConfig 
  -> FractionalSolution v 
  -> Int 
  -> FractionalSolution v
continuousGreedyStep ext polytope (ContinuousGreedyConfig { numIterations, samplesPerGradient, seed }) current t =
  let -- Estimate gradient
      gradient = gradientSampled ext current samplesPerGradient (seed + intToNum t * 10000.0)
      -- Linear maximize
      direction = linearMaximize polytope gradient
      -- Step size
      stepSize = 1.0 / intToNum numIterations
      -- Update
  in addScaled current stepSize direction


