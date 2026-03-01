-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--          // hydrogen // optimize // submodular // continuous // matroid polytope
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Matroid Polytope for Continuous Optimization.
-- |
-- | ## Theoretical Foundation
-- |
-- | The matroid polytope P(M) for a matroid M is:
-- |
-- |   P(M) = conv{1_I : I independent in M}
-- |        = {x ∈ [0,1]^n : x(S) ≤ r(S) for all S ⊆ V}
-- |
-- | Where r(S) is the rank function of the matroid.
-- |
-- | ## Key Property
-- |
-- | Linear optimization over P(M) reduces to greedy selection on the matroid.
-- | This is the foundation of the continuous greedy algorithm.
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Optimize.Submodular.Continuous.FractionalSolution
-- | - Hydrogen.Optimize.Submodular.Types (Matroid, GroundSet)

module Hydrogen.Optimize.Submodular.Continuous.MatroidPolytope
  ( MatroidPolytope(MatroidPolytope)
  , mkMatroidPolytope
  , isInPolytope
  , linearMaximize
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Ord
  , compare
  , map
  , (+)
  , (<=)
  )

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Maybe (Maybe(Nothing, Just))
import Data.Set as Set
import Data.Map (Map)
import Data.Map as Map
import Data.Tuple (Tuple(Tuple), fst)

import Hydrogen.Schema.Bounded (unitOne)
import Hydrogen.Schema.Tensor.Dimension (Dim(Dim), unwrapDim)
import Hydrogen.Optimize.Submodular.Types
  ( Element(Element)
  , ElementSet
  , GroundSet(GroundSet)
  , class Matroid
  , maxRank
  , MatroidRank(MatroidRank)
  , canExtend
  )
import Hydrogen.Optimize.Submodular.Continuous.FractionalSolution
  ( FractionalSolution(FractionalSolution)
  , solutionCoords
  )
import Hydrogen.Optimize.Submodular.Continuous.Utilities (intToNum)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // matroid polytope
-- ═════════════════════════════════════════════════════════════════════════════

-- | The matroid polytope P(M) for a matroid M.
-- |
-- | P(M) = conv{1_I : I independent in M}
-- |      = {x ∈ [0,1]^n : x(S) ≤ r(S) for all S ⊆ V}
-- |
-- | Key property: linear optimization over P(M) reduces to greedy.
newtype MatroidPolytope m v = MatroidPolytope
  { matroid :: m
  , groundSet :: GroundSet v
  }

-- | Create matroid polytope.
mkMatroidPolytope :: forall m v. Matroid m v => m -> GroundSet v -> MatroidPolytope m v
mkMatroidPolytope matroid groundSet = MatroidPolytope { matroid, groundSet }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // polytope queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a fractional solution is in the matroid polytope.
-- |
-- | x ∈ P(M) iff x(S) ≤ r(S) for all S ⊆ V.
-- |
-- | We check a necessary condition: sum of coordinates ≤ rank.
isInPolytope :: forall m v. Matroid m v => MatroidPolytope m v -> FractionalSolution v -> Boolean
isInPolytope (MatroidPolytope { matroid }) sol =
  let totalMass = foldl (+) 0.0 (solutionCoords sol)
      (MatroidRank (Dim r)) = maxRank matroid
  in totalMass <= intToNum r + 0.0001  -- Small tolerance for numerical error

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // linear optimization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Linear maximization over matroid polytope.
-- |
-- | Given weights w, find argmax_{x ∈ P(M)} ⟨w, x⟩.
-- |
-- | Solution: greedy algorithm on discrete matroid, return indicator vector.
linearMaximize 
  :: forall m v
   . Ord (Element v)
  => Matroid m v 
  => MatroidPolytope m v 
  -> Map Int Number          -- ^ Weights
  -> FractionalSolution v
linearMaximize (MatroidPolytope { matroid, groundSet }) weights =
  let (GroundSet { elements }) = groundSet
      -- Sort elements by weight descending
      withWeights = map (\e@(Element i) -> 
        Tuple (case Map.lookup i weights of
          Nothing -> 0.0
          Just w -> w) e) elements
      sorted = Array.reverse (Array.sortBy (\a b -> compare (fst a) (fst b)) withWeights)
      -- Greedy selection
      selected = greedySelectWeighted matroid sorted Set.empty
      -- Build indicator vector
      coords = foldl (\acc (Element i) -> Map.insert i unitOne acc) Map.empty 
                 (Set.toUnfoldable selected :: Array (Element v))
  in FractionalSolution { groundSetSize: unwrapDim (let (GroundSet { size }) = groundSet in size), coords }

-- | Greedy selection with weights.
greedySelectWeighted 
  :: forall m v
   . Matroid m v 
  => m 
  -> Array (Tuple Number (Element v)) 
  -> ElementSet v 
  -> ElementSet v
greedySelectWeighted _ [] current = current
greedySelectWeighted matroid sorted current =
  case Array.uncons sorted of
    Nothing -> current
    Just { head: Tuple _ e, tail: rest } ->
      if canExtend matroid e current
        then greedySelectWeighted matroid rest (Set.insert e current)
        else greedySelectWeighted matroid rest current
