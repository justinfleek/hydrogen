-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // optimize // submodular // rounding
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pipage Rounding for Submodular Maximization.
-- |
-- | ## Theoretical Foundation
-- |
-- | Pipage rounding converts fractional solutions to integral solutions while:
-- | 1. Maintaining feasibility (output is always matroid-independent)
-- | 2. Preserving marginals: E[1_e ∈ S] = x_e for all elements e
-- | 3. Never decreasing expected value: E[f(S)] ≥ F(x)
-- |
-- | The key insight: for submodular functions, the multilinear extension F
-- | is concave along "pipage" directions (transfer probability between elements).
-- |
-- | ## Pipage Direction
-- |
-- | A pipage step between elements i and j with transfer ε:
-- |   x'_i = x_i + ε
-- |   x'_j = x_j - ε
-- |
-- | The multilinear extension F is piecewise linear along this direction.
-- | We move to a "breakpoint" where either x'_i ∈ {0,1} or x'_j ∈ {0,1}.
-- |
-- | ## Swap Rounding
-- |
-- | Randomized variant: at each step, randomly choose direction.
-- | Preserves marginals in expectation and produces independent set.
-- |
-- | ## Contention Resolution
-- |
-- | For online/parallel settings: resolve conflicting element selections
-- | probabilistically while maintaining approximation guarantees.
-- |
-- | ## References
-- |
-- | - Ageev, Sviridenko. "Pipage Rounding: A New Method of Constructing
-- |   Algorithms with Proven Performance Guarantee" J. Comb. Opt. 2004
-- | - Chekuri, Vondrák, Zenklusen. "Dependent Randomized Rounding via
-- |   Exchange Properties of Matroids" FOCS 2010
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from submodules:
-- |
-- | - Hydrogen.Optimize.Submodular.Rounding.Util (utilities)
-- | - Hydrogen.Optimize.Submodular.Rounding.Pairing (element pairing)
-- | - Hydrogen.Optimize.Submodular.Rounding.Metrics (quality metrics)
-- | - Hydrogen.Optimize.Submodular.Rounding.Pipage (pipage algorithm)
-- | - Hydrogen.Optimize.Submodular.Rounding.Swap (swap algorithm)
-- | - Hydrogen.Optimize.Submodular.Rounding.Contention (contention resolution)
-- | - Hydrogen.Optimize.Submodular.Rounding.MinEnergy (FAA P3 min-energy)

module Hydrogen.Optimize.Submodular.Rounding
  ( -- * Pipage Rounding
    module Hydrogen.Optimize.Submodular.Rounding.Pipage
  
  -- * Swap Rounding
  , module Hydrogen.Optimize.Submodular.Rounding.Swap
  
  -- * Contention Resolution
  , module Hydrogen.Optimize.Submodular.Rounding.Contention
  
  -- * Rounding Metrics
  , module Hydrogen.Optimize.Submodular.Rounding.Metrics
  
  -- * Element Pairing
  , module Hydrogen.Optimize.Submodular.Rounding.Pairing
  
  -- * Min-Energy Sampling (FAA P3)
  , module Hydrogen.Optimize.Submodular.Rounding.MinEnergy
  
  -- * Utility
  , module Hydrogen.Optimize.Submodular.Rounding.Util
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Optimize.Submodular.Rounding.Util
  ( isIntegralValue
  , isFractional
  , fractionalElements
  , integralElements
  , updateSolutionCoord
  , shuffleArray
  , hashIndex
  , intToNum
  , identity
  , pseudoRandom
  )

import Hydrogen.Optimize.Submodular.Rounding.Pairing
  ( PipagePair(PipagePair)
  , findPipagePair
  , pairTransferBounds
  , scorePair
  , allPairs
  )

import Hydrogen.Optimize.Submodular.Rounding.Metrics
  ( RoundingMetrics(RoundingMetrics)
  , mkRoundingMetrics
  , updateMetrics
  , roundingQuality
  )

import Hydrogen.Optimize.Submodular.Rounding.Pipage
  ( PipageState(PipageState)
  , mkPipageState
  , pipageStep
  , pipageRound
  , fullPipageRound
  , findPipagePairFromSolution
  )

import Hydrogen.Optimize.Submodular.Rounding.Swap
  ( SwapState(SwapState)
  , mkSwapState
  , swapStep
  , swapRound
  , jointRound
  )

import Hydrogen.Optimize.Submodular.Rounding.Contention
  ( ContentionScheme(ContentionScheme)
  , mkContentionScheme
  , resolveContention
  , correlatedContentionResolution
  )

import Hydrogen.Optimize.Submodular.Rounding.MinEnergy
  ( MinEnergyConfig(MinEnergyConfig)
  , mkMinEnergyConfig
  , roundingEnergy
  , minEnergyRound
  , minEnergyCandidates
  , randomThresholdRound
  )
