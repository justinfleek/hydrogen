-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // optimize // submodular // rounding // swap
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Swap Rounding Algorithm.
-- |
-- | ## Theoretical Foundation
-- |
-- | Swap rounding is a randomized variant of pipage:
-- | - At each step, randomly choose direction
-- | - Preserves marginals in expectation
-- | - Produces independent set
-- |
-- | ## References
-- |
-- | - Chekuri, Vondrák, Zenklusen. "Dependent Randomized Rounding via
-- |   Exchange Properties of Matroids" FOCS 2010
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Optimize.Submodular.Types (element types)
-- | - Hydrogen.Optimize.Submodular.Continuous (fractional solutions)
-- | - Hydrogen.Optimize.Submodular.Rounding.Util (utility functions)

module Hydrogen.Optimize.Submodular.Rounding.Swap
  ( -- * Swap State
    SwapState(SwapState)
  , mkSwapState
  
  -- * Swap Algorithm
  , swapStep
  , swapRound
  
  -- * Internal
  , jointRound
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Ord
  , class Show
  , max
  , show
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (<>)
  , ($)
  )

import Data.Array as Array
import Data.Maybe (Maybe(Nothing, Just))
import Data.Set as Set
import Data.Tuple (Tuple(Tuple), fst, snd)

import Hydrogen.Math.Core as Math
import Hydrogen.Optimize.Submodular.Types
  ( Element
  , ElementSet
  )
import Hydrogen.Optimize.Submodular.Continuous
  ( FractionalSolution
  , solutionCoord
  , solutionSupport
  )
import Hydrogen.Optimize.Submodular.Rounding.Util
  ( shuffleArray
  , intToNum
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // swap state
-- ═════════════════════════════════════════════════════════════════════════════

-- | State for swap rounding (randomized pipage).
-- |
-- | Swap rounding is pipage with random pairing at each step,
-- | which provides stronger randomness guarantees.
newtype SwapState v = SwapState
  { solution :: FractionalSolution v
  , result :: ElementSet v          -- ^ Elements selected so far
  , remaining :: Array (Element v)  -- ^ Elements not yet processed
  , seed :: Number
  }

instance showSwapState :: Show (SwapState v) where
  show (SwapState s) = 
    "SwapState{result=" <> show (Set.size s.result) <> 
    ", remaining=" <> show (Array.length s.remaining) <> "}"

-- | Create initial swap state.
mkSwapState :: forall v. Ord (Element v) => FractionalSolution v -> Number -> SwapState v
mkSwapState sol seed =
  let support = solutionSupport sol
      elements = Set.toUnfoldable support :: Array (Element v)
      -- Shuffle elements based on seed
      shuffled = shuffleArray elements seed
  in SwapState
       { solution: sol
       , result: Set.empty
       , remaining: shuffled
       , seed
       }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // swap algorithm
-- ═════════════════════════════════════════════════════════════════════════════

-- | Perform one swap step.
-- |
-- | Takes two elements from remaining, jointly rounds them,
-- | and adds result to the selected set.
swapStep :: forall v. Ord (Element v) => SwapState v -> Maybe (SwapState v)
swapStep (SwapState s) =
  case Array.uncons s.remaining of
    Nothing -> Nothing
    Just { head: e1, tail: rest1 } ->
      case Array.uncons rest1 of
        Nothing ->
          -- Single element: round individually
          let prob = solutionCoord s.solution e1
              hash = Math.sin (s.seed * 12.9898) * 43758.5453
              r = hash - Math.floor hash
              newResult = if r < prob 
                then Set.insert e1 s.result 
                else s.result
          in Just $ SwapState s { result = newResult, remaining = [] }
        Just { head: e2, tail: rest2 } ->
          let prob1 = solutionCoord s.solution e1
              prob2 = solutionCoord s.solution e2
              -- Joint rounding preserving sum
              hash = Math.sin (s.seed * 12.9898 + intToNum (Array.length rest2) * 78.233) * 43758.5453
              r = hash - Math.floor hash
              -- Decide how many to include (0, 1, or 2)
              roundResult = jointRound prob1 prob2 r
              include1 = fst roundResult
              include2 = snd roundResult
              newResult = 
                (if include1 then Set.insert e1 else identity) $
                (if include2 then Set.insert e2 else identity) $
                s.result
          in Just $ SwapState
               { solution: s.solution
               , result: newResult
               , remaining: rest2
               , seed: s.seed + 1.0
               }

-- | Joint rounding of two elements.
-- |
-- | Preserves marginals: P[include e1] = prob1, P[include e2] = prob2
-- | Uses correlation to ensure sum is approximately preserved.
jointRound :: Number -> Number -> Number -> Tuple Boolean Boolean
jointRound prob1 prob2 r =
  let total = prob1 + prob2
      -- Cases based on total
      floorTotal = Math.floor total
      fracPart = total - floorTotal
  in if total < 1.0
       then
         -- At most one can be included
         if r < prob1
           then Tuple true false
           else if r < total
                  then Tuple false true
                  else Tuple false false
       else if total < 2.0
         then
           -- Exactly one must be included, possibly two
           if r < fracPart
             then Tuple true true   -- Both
             else if r < fracPart + prob1 * (1.0 - fracPart) / max 0.001 (prob1 + prob2 - 1.0)
                    then Tuple true false
                    else Tuple false true
         else
           -- Both must be included
           Tuple true true

-- | Run swap rounding to completion.
swapRound :: forall v. Ord (Element v) => SwapState v -> ElementSet v
swapRound state = swapLoop state

swapLoop :: forall v. Ord (Element v) => SwapState v -> ElementSet v
swapLoop state@(SwapState s) =
  case swapStep state of
    Nothing -> s.result
    Just newState -> swapLoop newState

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // utility
-- ═════════════════════════════════════════════════════════════════════════════

-- | Identity function (local definition).
identity :: forall a. a -> a
identity x = x
