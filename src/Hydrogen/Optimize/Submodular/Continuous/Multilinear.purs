-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--              // hydrogen // optimize // submodular // continuous // multilinear
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Multilinear Extension for Submodular Functions.
-- |
-- | ## Theoretical Foundation
-- |
-- | The multilinear extension F : [0,1]^n → ℝ of f : 2^V → ℝ is:
-- |
-- |   F(x) = 𝔼_{S ~ x}[f(S)] = Σ_{S ⊆ V} f(S) ∏_{e ∈ S} x_e ∏_{e ∉ S} (1 - x_e)
-- |
-- | Where S ~ x means each element e is included independently with probability x_e.
-- |
-- | ## Key Properties
-- |
-- | - F(1_S) = f(S) for indicator vectors
-- | - F is multilinear (linear in each coordinate)
-- | - ∂F/∂x_e = 𝔼_{S ~ x_{-e}}[f(S ∪ {e}) - f(S)] (expected marginal gain)
-- | - F is concave along any direction if f is submodular
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Optimize.Submodular.Continuous.FractionalSolution
-- | - Hydrogen.Optimize.Submodular.Types (SubmodularOracle)
-- | - Hydrogen.Math.Core (sin, floor)

module Hydrogen.Optimize.Submodular.Continuous.Multilinear
  ( MultilinearExt(MultilinearExt)
  , mkMultilinearExt
  , evalMultilinear
  , evalMultilinearSampled
  , partialDerivative
  , gradientSampled
  , sampleOnce
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Ord
  , map
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (/=)
  , (<>)
  )

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Maybe (Maybe(Nothing, Just))
import Data.Set (Set)
import Data.Set as Set
import Data.Map (Map)
import Data.Map as Map
import Data.Tuple (Tuple(Tuple), snd)

import Hydrogen.Math.Core as Math
import Hydrogen.Optimize.Submodular.Types
  ( Element(Element)
  , ElementSet
  , GroundSet(GroundSet)
  , SubmodularOracle(SubmodularOracle)
  , SetValue(SetValue)
  , MarginalGain(MarginalGain)
  )
import Hydrogen.Optimize.Submodular.Continuous.FractionalSolution
  ( FractionalSolution
  , solutionCoord
  )
import Hydrogen.Optimize.Submodular.Continuous.Utilities (intToNum)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // multilinear extension
-- ═════════════════════════════════════════════════════════════════════════════

-- | The multilinear extension of a submodular function.
-- |
-- | F(x) = 𝔼_{S ~ x}[f(S)]
-- |
-- | Wraps a discrete oracle to provide continuous evaluation.
newtype MultilinearExt v = MultilinearExt
  { oracle :: SubmodularOracle v
  , groundSet :: GroundSet v
  }

-- | Create multilinear extension from oracle.
mkMultilinearExt :: forall v. SubmodularOracle v -> MultilinearExt v
mkMultilinearExt oracle@(SubmodularOracle { groundSet }) =
  MultilinearExt { oracle, groundSet }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // exact evaluation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Evaluate multilinear extension exactly (exponential time).
-- |
-- | F(x) = Σ_{S ⊆ V} f(S) ∏_{e ∈ S} x_e ∏_{e ∉ S} (1 - x_e)
-- |
-- | WARNING: Only for small ground sets (|V| ≤ 15).
evalMultilinear :: forall v. MultilinearExt v -> FractionalSolution v -> Number
evalMultilinear (MultilinearExt { oracle, groundSet }) sol =
  let (SubmodularOracle { eval }) = oracle
      (GroundSet { elements }) = groundSet
      allSubsets = powerset elements
      termValue :: ElementSet v -> Number
      termValue s =
        let (SetValue fS) = eval s
            prob = subsetProbability sol s elements
        in fS * prob
  in foldl (\acc s -> acc + termValue s) 0.0 allSubsets

-- | Probability of exactly set S being sampled.
subsetProbability :: forall v. FractionalSolution v -> ElementSet v -> Array (Element v) -> Number
subsetProbability sol s allElements =
  foldl (\acc e ->
    let p = solutionCoord sol e
    in acc * (if Set.member e s then p else 1.0 - p)
  ) 1.0 allElements

-- | Powerset of an array.
powerset :: forall a. Ord a => Array a -> Array (Set a)
powerset arr = case Array.uncons arr of
  Nothing -> [Set.empty]
  Just { head, tail } ->
    let rest = powerset tail
    in rest <> map (Set.insert head) rest

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // sampled evaluation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Evaluate multilinear extension via sampling (polynomial time).
-- |
-- | Takes numSamples random samples S ~ x and averages f(S).
-- |
-- | Variance: O(1/numSamples)
evalMultilinearSampled 
  :: forall v
   . MultilinearExt v 
  -> FractionalSolution v 
  -> Int                     -- ^ Number of samples
  -> Number                  -- ^ Seed for determinism
  -> Number
evalMultilinearSampled ext@(MultilinearExt { oracle }) sol numSamples seed =
  let samples = generateSamples ext sol numSamples seed
      (SubmodularOracle { eval }) = oracle
      values = map (\s -> let (SetValue v) = eval s in v) samples
  in foldl (+) 0.0 values / intToNum numSamples

-- | Generate samples from the fractional distribution.
generateSamples 
  :: forall v
   . MultilinearExt v 
  -> FractionalSolution v 
  -> Int 
  -> Number 
  -> Array (ElementSet v)
generateSamples (MultilinearExt { groundSet }) sol numSamples seed =
  let (GroundSet { elements }) = groundSet
  in Array.mapWithIndex (\i _ -> sampleOnce sol elements (seed + intToNum i)) 
       (Array.range 0 (numSamples - 1))

-- | Sample one set according to the fractional solution.
sampleOnce :: forall v. FractionalSolution v -> Array (Element v) -> Number -> ElementSet v
sampleOnce sol elements seed =
  let indexed = Array.mapWithIndex Tuple elements
      included = Array.filter (includeElement sol seed) indexed
  in Set.fromFoldable (map snd included)

-- | Deterministic "random" inclusion based on seed.
-- |
-- | Uses simple hash: include if hash(seed, i) / maxHash < x_i
includeElement :: forall v. FractionalSolution v -> Number -> Tuple Int (Element v) -> Boolean
includeElement sol seed (Tuple idx e) =
  let p = solutionCoord sol e
      -- Simple deterministic pseudo-random
      hash = Math.sin (seed * 12.9898 + intToNum idx * 78.233) * 43758.5453
      r = hash - Math.floor hash  -- Fractional part in [0, 1)
  in r < p

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // gradient computation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Partial derivative ∂F/∂x_e = 𝔼_{S ~ x_{-e}}[f(S ∪ {e}) - f(S)]
-- |
-- | Sampled estimation with given number of samples.
partialDerivative 
  :: forall v
   . MultilinearExt v 
  -> FractionalSolution v 
  -> Element v 
  -> Int                     -- ^ Number of samples
  -> Number                  -- ^ Seed
  -> Number
partialDerivative (MultilinearExt { oracle, groundSet }) sol e@(Element eIdx) numSamples seed =
  let (SubmodularOracle { marginal }) = oracle
      (GroundSet { elements }) = groundSet
      -- Sample sets not including e
      elementsWithoutE = Array.filter (\(Element i) -> i /= eIdx) elements
      samples = Array.mapWithIndex 
        (\i _ -> sampleOnce sol elementsWithoutE (seed + intToNum i))
        (Array.range 0 (numSamples - 1))
      -- Compute marginal gains
      gains = map (\s -> let (MarginalGain g) = marginal e s in g) samples
  in foldl (+) 0.0 gains / intToNum numSamples

-- | Full gradient via sampling.
gradientSampled 
  :: forall v
   . MultilinearExt v 
  -> FractionalSolution v 
  -> Int                     -- ^ Samples per coordinate
  -> Number                  -- ^ Seed
  -> Map Int Number          -- ^ Gradient: element index → partial derivative
gradientSampled ext@(MultilinearExt { groundSet }) sol samplesPerCoord seed =
  let (GroundSet { elements }) = groundSet
  in foldl (\acc e@(Element i) -> 
       let deriv = partialDerivative ext sol e samplesPerCoord (seed + intToNum i * 1000.0)
       in Map.insert i deriv acc
     ) Map.empty elements
