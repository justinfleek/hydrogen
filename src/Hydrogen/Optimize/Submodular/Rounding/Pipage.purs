-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                     // hydrogen // optimize // submodular // rounding // pipage
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pipage Rounding Algorithm.
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
-- | ## References
-- |
-- | - Ageev, Sviridenko. "Pipage Rounding: A New Method of Constructing
-- |   Algorithms with Proven Performance Guarantee" J. Comb. Opt. 2004
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Optimize.Submodular.Types (element types)
-- | - Hydrogen.Optimize.Submodular.Continuous (fractional solutions)
-- | - Hydrogen.Optimize.Submodular.Rounding.Util (utility functions)
-- | - Hydrogen.Optimize.Submodular.Rounding.Pairing (element pairing)

module Hydrogen.Optimize.Submodular.Rounding.Pipage
  ( -- * Pipage State
    PipageState(PipageState)
  , mkPipageState
  
  -- * Pipage Algorithm
  , pipageStep
  , pipageRound
  , fullPipageRound
  
  -- * Internal
  , findPipagePairFromSolution
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Ord
  , class Show
  , show
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (>=)
  , (&&)
  , (<>)
  , ($)
  )

import Data.Array as Array
import Data.Maybe (Maybe(Nothing, Just))
import Data.Set as Set
import Data.Tuple (Tuple(Tuple))

import Hydrogen.Math.Core as Math
import Hydrogen.Optimize.Submodular.Types
  ( Element
  , ElementSet
  )
import Hydrogen.Optimize.Submodular.Continuous
  ( FractionalSolution(FractionalSolution)
  , solutionCoord
  )
import Hydrogen.Optimize.Submodular.Rounding.Util
  ( fractionalElements
  , isIntegralValue
  , updateSolutionCoord
  , identity
  , intToNum
  )
import Hydrogen.Optimize.Submodular.Rounding.Pairing
  ( PipagePair(PipagePair)
  , pairTransferBounds
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // pipage state
-- ═════════════════════════════════════════════════════════════════════════════

-- | State for pipage rounding algorithm.
newtype PipageState v = PipageState
  { solution :: FractionalSolution v    -- ^ Current (partially integral) solution
  , integral :: ElementSet v            -- ^ Elements fixed at 1
  , excluded :: ElementSet v            -- ^ Elements fixed at 0
  , steps :: Int                        -- ^ Steps taken
  , seed :: Number                      -- ^ Random seed for tie-breaking
  }

instance showPipageState :: Show (PipageState v) where
  show (PipageState s) = 
    "PipageState{steps=" <> show s.steps <> 
    ", integral=" <> show (Set.size s.integral) <>
    ", excluded=" <> show (Set.size s.excluded) <> "}"

-- | Create initial pipage state.
mkPipageState :: forall v. FractionalSolution v -> Number -> PipageState v
mkPipageState solution seed = PipageState
  { solution
  , integral: Set.empty
  , excluded: Set.empty
  , steps: 0
  , seed
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // pipage algorithm
-- ═════════════════════════════════════════════════════════════════════════════

-- | Perform one pipage step.
-- |
-- | 1. Find a pair of fractional elements
-- | 2. Randomly choose direction (up or down)
-- | 3. Transfer probability until one element becomes integral
-- | 4. Update state
-- |
-- | Returns Nothing if solution is already integral.
pipageStep 
  :: forall v
   . Ord (Element v) 
  => PipageState v 
  -> Maybe (PipageState v)
pipageStep (PipageState s) =
  case findPipagePairFromSolution s.solution of
    Nothing -> Nothing  -- Already integral
    Just pair@(PipagePair p) ->
      let (Tuple maxUp maxDown) = pairTransferBounds pair
          -- Random direction choice
          hash = Math.sin (s.seed * 12.9898 + intToNum s.steps * 78.233) * 43758.5453
          r = hash - Math.floor hash
          -- Weight choice by transfer amounts
          upWeight = maxUp / (maxUp + maxDown + 0.0001)
          goUp = r < upWeight
          -- Compute new probabilities
          (Tuple newProb1 newProb2) = if goUp
            then Tuple (p.prob1 + maxUp) (p.prob2 - maxUp)
            else Tuple (p.prob1 - maxDown) (p.prob2 + maxDown)
          -- Update solution
          newSolution = updateSolutionCoord 
            (updateSolutionCoord s.solution p.element1 newProb1) 
            p.element2 newProb2
          -- Track which elements became integral
          newIntegral = 
            (if isIntegralValue newProb1 && newProb1 > 0.5 
               then Set.insert p.element1 else identity) $
            (if isIntegralValue newProb2 && newProb2 > 0.5 
               then Set.insert p.element2 else identity) $
            s.integral
          newExcluded =
            (if isIntegralValue newProb1 && newProb1 < 0.5 
               then Set.insert p.element1 else identity) $
            (if isIntegralValue newProb2 && newProb2 < 0.5 
               then Set.insert p.element2 else identity) $
            s.excluded
      in Just $ PipageState
           { solution: newSolution
           , integral: newIntegral
           , excluded: newExcluded
           , steps: s.steps + 1
           , seed: s.seed
           }

-- | Find pipage pair with probabilities filled in.
findPipagePairFromSolution :: forall v. Ord (Element v) => FractionalSolution v -> Maybe (PipagePair v)
findPipagePairFromSolution sol =
  let fractional = fractionalElements sol
      elements = Set.toUnfoldable fractional :: Array (Element v)
  in case Array.uncons elements of
       Nothing -> Nothing
       Just { head: e1, tail } ->
         case Array.head tail of
           Nothing -> Nothing
           Just e2 ->
             let prob1 = solutionCoord sol e1
                 prob2 = solutionCoord sol e2
             in Just $ PipagePair { element1: e1, element2: e2, prob1, prob2 }

-- | Run pipage until a stopping condition.
-- |
-- | maxSteps: maximum iterations (safety bound)
pipageRound 
  :: forall v
   . Ord (Element v) 
  => Int                         -- ^ Max steps
  -> PipageState v 
  -> PipageState v
pipageRound maxSteps state =
  pipageLoop maxSteps 0 state

pipageLoop :: forall v. Ord (Element v) => Int -> Int -> PipageState v -> PipageState v
pipageLoop maxSteps current state =
  if current >= maxSteps
    then state
    else case pipageStep state of
           Nothing -> state  -- Converged
           Just newState -> pipageLoop maxSteps (current + 1) newState

-- | Full pipage rounding: run until solution is integral.
-- |
-- | Returns the integral solution as an ElementSet.
fullPipageRound 
  :: forall v
   . Ord (Element v) 
  => FractionalSolution v 
  -> Number                      -- ^ Seed
  -> ElementSet v
fullPipageRound sol seed =
  let initialState = mkPipageState sol seed
      -- Max steps = 2 * ground set size (each step fixes at least one element)
      (FractionalSolution { groundSetSize }) = sol
      maxSteps = 2 * groundSetSize
      finalState = pipageRound maxSteps initialState
      (PipageState s) = finalState
  in s.integral
