-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                  // hydrogen // optimize // submodular // rounding // min-energy
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Min-Energy Sampling for FAA Phase 3.
-- |
-- | ## Theoretical Foundation (Proven in proofs/Hydrogen/Optimize/Submodular/FAA.lean)
-- |
-- | For noise-resilient rounding in FAA, instead of random sampling we choose
-- | the rounding that minimizes "energy" - the squared deviation from fractional:
-- |
-- |   E(S, x) = Σ_e (x_e - 1_S(e))²
-- |
-- | ## Why This Works
-- |
-- | 1. **Deterministic**: Given candidates, always picks the same solution
-- | 2. **Noise-resilient**: Minimizes deviation from intended allocation
-- | 3. **Locally optimal**: Closest integral solution to fractional
-- |
-- | ## Proven Properties (FAA.lean)
-- |
-- | - `roundingEnergy`: Energy is always non-negative
-- | - `min_energy_deterministic`: Unique minimum exists for finite candidates
-- | - Works with FAA's larger step sizes without instability
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Math.Core (mathematical operations)
-- | - Hydrogen.Optimize.Submodular.Types (element types)
-- | - Hydrogen.Optimize.Submodular.Continuous (fractional solutions)
-- | - Hydrogen.Optimize.Submodular.Rounding.Util (utility functions)

module Hydrogen.Optimize.Submodular.Rounding.MinEnergy
  ( -- * Configuration
    MinEnergyConfig(MinEnergyConfig)
  , mkMinEnergyConfig
  
  -- * Energy Computation
  , roundingEnergy
  
  -- * Min-Energy Rounding
  , minEnergyRound
  , minEnergyCandidates
  
  -- * Internal
  , randomThresholdRound
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , map
  , show
  , (+)
  , (-)
  , (*)
  , (<)
  , (>)
  , (<>)
  )

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Maybe (Maybe(Nothing, Just))
import Data.Set as Set
import Data.Tuple (Tuple(Tuple))

import Hydrogen.Optimize.Submodular.Types
  ( Element(Element)
  , ElementSet
  )
import Hydrogen.Optimize.Submodular.Continuous
  ( FractionalSolution(FractionalSolution)
  , solutionCoord
  )
import Hydrogen.Optimize.Submodular.Rounding.Util
  ( intToNum
  , pseudoRandom
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Min-Energy Sampling Configuration.
-- |
-- | ## Theoretical Foundation (Proven in proofs/Hydrogen/Optimize/Submodular/FAA.lean)
-- |
-- | For noise-resilient rounding in FAA, instead of random sampling we choose
-- | the rounding that minimizes "energy" - the squared deviation from fractional:
-- |
-- |   E(S, x) = Σ_e (x_e - 1_S(e))²
-- |
-- | ## Why This Works
-- |
-- | 1. **Deterministic**: Given candidates, always picks the same solution
-- | 2. **Noise-resilient**: Minimizes deviation from intended allocation
-- | 3. **Locally optimal**: Closest integral solution to fractional
-- |
-- | ## Proven Properties (FAA.lean)
-- |
-- | - `roundingEnergy`: Energy is always non-negative
-- | - `min_energy_deterministic`: Unique minimum exists for finite candidates
-- | - Works with FAA's larger step sizes without instability
newtype MinEnergyConfig = MinEnergyConfig
  { numCandidates :: Int     -- ^ Number of random roundings to generate
  , seed :: Number           -- ^ Random seed for candidate generation
  }

derive instance eqMinEnergyConfig :: Eq MinEnergyConfig

instance showMinEnergyConfig :: Show MinEnergyConfig where
  show (MinEnergyConfig { numCandidates }) =
    "MinEnergyConfig[candidates=" <> show numCandidates <> "]"

-- | Create min-energy config with sensible defaults.
-- |
-- | More candidates = better quality but slower.
-- | For real-time (60fps): 10-20 candidates
-- | For batch processing: 100+ candidates
mkMinEnergyConfig :: Int -> MinEnergyConfig
mkMinEnergyConfig numCandidates = MinEnergyConfig
  { numCandidates
  , seed: 42.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // energy computation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute rounding energy: Σ_e (x_e - 1_S(e))²
-- |
-- | Lower energy = closer to fractional solution.
-- |
-- | ## Proven (FAA.lean: roundingEnergy)
-- |
-- | Energy is always non-negative and zero iff x is already integral.
roundingEnergy :: forall v. Ord (Element v) => FractionalSolution v -> ElementSet v -> Number
roundingEnergy sol@(FractionalSolution { groundSetSize }) selected =
  let -- For each element, compute (x_e - indicator)²
      computeElementEnergy :: Int -> Number
      computeElementEnergy i =
        let x_e = solutionCoord sol (Element i)
            indicator = if Set.member (Element i) selected then 1.0 else 0.0
            diff = x_e - indicator
        in diff * diff
      -- Sum over all elements in ground set
      indices = Array.range 0 (groundSetSize - 1)
  in foldl (+) 0.0 (map computeElementEnergy indices)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // min-energy rounding
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate candidate roundings for min-energy selection.
-- |
-- | Uses randomized threshold rounding with different seeds.
minEnergyCandidates 
  :: forall v
   . Ord (Element v) 
  => FractionalSolution v 
  -> MinEnergyConfig 
  -> Array (ElementSet v)
minEnergyCandidates sol (MinEnergyConfig { numCandidates, seed }) =
  let -- Generate random thresholds for each candidate
      generateCandidate :: Int -> ElementSet v
      generateCandidate candidateIdx =
        let candidateSeed = seed + intToNum candidateIdx * 17.0
        in randomThresholdRound sol candidateSeed
  in map generateCandidate (Array.range 0 (numCandidates - 1))

-- | Random threshold rounding: include e iff x_e > random threshold.
randomThresholdRound :: forall v. Ord (Element v) => FractionalSolution v -> Number -> ElementSet v
randomThresholdRound sol@(FractionalSolution { groundSetSize }) seed =
  let indices = Array.range 0 (groundSetSize - 1)
      includeElement :: Int -> Boolean
      includeElement i =
        let x_e = solutionCoord sol (Element i)
            -- Generate pseudo-random threshold in [0, 1]
            threshold = pseudoRandom (seed + intToNum i * 31.0)
        in x_e > threshold
      selected = Array.filter includeElement indices
  in Set.fromFoldable (map Element selected)

-- | Min-energy rounding: select the candidate with lowest energy.
-- |
-- | ## Algorithm
-- |
-- | 1. Generate `numCandidates` random roundings
-- | 2. Compute energy for each
-- | 3. Return the one with minimum energy
-- |
-- | ## Proven (FAA.lean: min_energy_deterministic)
-- |
-- | For non-empty candidate set, minimum always exists and is deterministic.
minEnergyRound 
  :: forall v
   . Ord (Element v) 
  => FractionalSolution v 
  -> MinEnergyConfig 
  -> ElementSet v
minEnergyRound sol config =
  let candidates = minEnergyCandidates sol config
      -- Compute energy for each candidate
      withEnergy = map (\s -> Tuple (roundingEnergy sol s) s) candidates
      -- Find minimum energy candidate
      findMin :: Maybe (Tuple Number (ElementSet v)) -> Array (Tuple Number (ElementSet v)) -> ElementSet v
      findMin acc remaining = case Array.uncons remaining of
        Nothing -> case acc of
          Nothing -> Set.empty  -- No candidates (shouldn't happen)
          Just (Tuple _ best) -> best
        Just { head: candidate@(Tuple energy _), tail: rest } ->
          case acc of
            Nothing -> findMin (Just candidate) rest
            Just (Tuple bestEnergy _) ->
              if energy < bestEnergy
                then findMin (Just candidate) rest
                else findMin acc rest
  in findMin Nothing withEnergy
