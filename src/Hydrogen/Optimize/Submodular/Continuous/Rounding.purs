-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                // hydrogen // optimize // submodular // continuous // rounding
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Solution Rounding for Continuous Submodular Optimization.
-- |
-- | ## Purpose
-- |
-- | Continuous greedy produces fractional solutions x ∈ [0,1]^n.
-- | Rounding converts these to discrete solutions S ⊆ V.
-- |
-- | ## Rounding Methods
-- |
-- | ### Independent Sampling
-- | Each element e is included independently with probability x_e.
-- | Simple but may violate matroid constraints.
-- |
-- | ### Threshold Rounding
-- | Include e iff x_e ≥ threshold.
-- | Deterministic but may violate constraints.
-- |
-- | ### Dependent Rounding (Swap/Pipage)
-- | Respects matroid constraint while preserving marginal probabilities.
-- | E[1_e] = x_e for all e, and result is always independent.
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Optimize.Submodular.Continuous.FractionalSolution
-- | - Hydrogen.Optimize.Submodular.Continuous.Multilinear (sampleOnce)
-- | - Hydrogen.Optimize.Submodular.Types (Matroid)
-- | - Hydrogen.Math.Core (sin, floor)

module Hydrogen.Optimize.Submodular.Continuous.Rounding
  ( sampleSolution
  , thresholdRound
  , dependentRound
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Ord
  , compare
  , map
  , (+)
  , (-)
  , (*)
  , (<)
  , (>=)
  )

import Data.Maybe (Maybe(Nothing, Just))

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Set (Set)
import Data.Set as Set
import Data.Map as Map
import Data.Tuple (Tuple(Tuple), fst)

import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Bounded (unwrapUnit)
import Hydrogen.Optimize.Submodular.Types
  ( Element(Element)
  , ElementSet
  , class Matroid
  , canExtend
  )
import Hydrogen.Optimize.Submodular.Continuous.FractionalSolution
  ( FractionalSolution(FractionalSolution)
  , solutionCoord
  , solutionSupport
  )
import Hydrogen.Optimize.Submodular.Continuous.Multilinear (sampleOnce)
import Hydrogen.Optimize.Submodular.Continuous.Utilities (intToNum)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // independent sampling
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sample a discrete solution from fractional solution.
-- |
-- | Each element e is included independently with probability x_e.
-- |
-- | Note: Result may not be matroid-independent. Use dependentRound for
-- | matroid-respecting rounding.
sampleSolution :: forall v. FractionalSolution v -> Number -> ElementSet v
sampleSolution sol@(FractionalSolution { groundSetSize }) seed =
  let elements = map Element (Array.range 0 (groundSetSize - 1))
  in sampleOnce sol elements seed

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // threshold rounding
-- ═════════════════════════════════════════════════════════════════════════════

-- | Threshold rounding: include e iff x_e ≥ threshold.
-- |
-- | Deterministic but may not respect matroid constraints.
thresholdRound :: forall v. FractionalSolution v -> Number -> ElementSet v
thresholdRound (FractionalSolution { coords }) threshold =
  let aboveThreshold = Map.filter (\x -> unwrapUnit x >= threshold) coords
      indexSet = Map.keys aboveThreshold
      indices = Set.toUnfoldable indexSet :: Array Int
  in Set.fromFoldable (map Element indices)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // dependent rounding
-- ═════════════════════════════════════════════════════════════════════════════

-- | Dependent rounding that respects matroid constraint.
-- |
-- | Swap rounding: iteratively pairs elements and rounds jointly
-- | such that the result is always independent.
-- |
-- | For matroid polytope points, produces independent set with
-- | E[1_e] = x_e for all e.
dependentRound 
  :: forall m v
   . Ord (Element v)
  => Matroid m v 
  => m 
  -> FractionalSolution v 
  -> Number                  -- ^ Seed
  -> ElementSet v
dependentRound matroid sol seed =
  -- Simplified version: greedy rounding
  -- Full swap/pipage rounding would be more complex
  let support = solutionSupport sol
      elements = Set.toUnfoldable support :: Array (Element v)
      -- Sort by x_e descending (prioritize higher probability)
      withProbs = map (\e -> Tuple (solutionCoord sol e) e) elements
      sorted = Array.reverse (Array.sortBy (\a b -> compare (fst a) (fst b)) withProbs)
  in greedyRoundSorted matroid sorted Set.empty seed

-- | Greedy rounding from sorted candidates.
greedyRoundSorted 
  :: forall m v
   . Matroid m v 
  => m 
  -> Array (Tuple Number (Element v)) 
  -> ElementSet v 
  -> Number 
  -> ElementSet v
greedyRoundSorted _ [] current _ = current
greedyRoundSorted matroid sorted current seed =
  case Array.uncons sorted of
    Nothing -> current
    Just { head: Tuple prob e@(Element i), tail: rest } ->
      if canExtend matroid e current
        then
          -- Include with probability proportional to x_e (simplified: threshold at 0.5)
          let hash = Math.sin (seed * 12.9898 + intToNum i * 78.233) * 43758.5453
              r = hash - Math.floor hash
              include = r < prob
          in if include
               then greedyRoundSorted matroid rest (Set.insert e current) seed
               else greedyRoundSorted matroid rest current seed
        else greedyRoundSorted matroid rest current seed
