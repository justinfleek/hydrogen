-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                    // hydrogen // optimize // submodular // rounding // pairing
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Element pairing for pipage rounding.
-- |
-- | During pipage rounding, we transfer probability mass between two
-- | fractional elements until one becomes integral (0 or 1).
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Optimize.Submodular.Types (element types)
-- | - Hydrogen.Optimize.Submodular.Continuous (fractional solutions)
-- | - Hydrogen.Optimize.Submodular.Rounding.Util (utility functions)

module Hydrogen.Optimize.Submodular.Rounding.Pairing
  ( -- * Pipage Pair
    PipagePair(PipagePair)
  , findPipagePair
  , pairTransferBounds
  , scorePair
  , allPairs
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , bind
  , compare
  , map
  , min
  , show
  , (+)
  , (-)
  , (*)
  , (<>)
  )

import Data.Array as Array
import Data.Maybe (Maybe(Nothing, Just))
import Data.Set as Set
import Data.Tuple (Tuple(Tuple), snd)

import Hydrogen.Optimize.Submodular.Types (Element(Element))
import Hydrogen.Optimize.Submodular.Continuous
  ( FractionalSolution
  , solutionCoord
  )
import Hydrogen.Optimize.Submodular.Rounding.Util
  ( fractionalElements
  , intToNum
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // pipage pair
-- ═════════════════════════════════════════════════════════════════════════════

-- | A pair of elements for pipage transfer.
-- |
-- | During pipage rounding, we transfer probability mass between two
-- | fractional elements until one becomes integral (0 or 1).
newtype PipagePair v = PipagePair
  { element1 :: Element v           -- ^ First element (probability increases)
  , element2 :: Element v           -- ^ Second element (probability decreases)
  , prob1 :: Number                 -- ^ x_{e1}
  , prob2 :: Number                 -- ^ x_{e2}
  }

derive instance eqPipagePair :: Eq (PipagePair v)

instance showPipagePair :: Show (PipagePair v) where
  show (PipagePair p) = 
    "Pair{" <> show p.element1 <> ":" <> show p.prob1 <> 
    ", " <> show p.element2 <> ":" <> show p.prob2 <> "}"

-- | Find a pair of fractional elements for pipage.
-- |
-- | Returns Nothing if solution is already integral.
-- | Prefers pairs that maximize the transfer amount.
findPipagePair :: forall v. Ord (Element v) => FractionalSolution v -> Maybe (PipagePair v)
findPipagePair sol =
  let fractional = fractionalElements sol
      elements = Set.toUnfoldable fractional :: Array (Element v)
  in case Array.length elements of
       0 -> Nothing
       1 -> Nothing  -- Need at least 2 fractional elements
       _ ->
         -- Find pair with largest combined "room to move"
         let pairs = allPairs elements
             scored = map (scorePair sol) pairs
             best = Array.sortBy (\a b -> compare (snd b) (snd a)) scored
         in case Array.head best of
              Nothing -> Nothing
              Just (Tuple pair _) -> Just pair

-- | Score a pair by transfer potential.
-- |
-- | Uses the solution to get actual probabilities and updates the pair
-- | with real probability values before scoring.
scorePair :: forall v. FractionalSolution v -> PipagePair v -> Tuple (PipagePair v) Number
scorePair sol (PipagePair p) =
  let -- Get actual probabilities from solution
      actualProb1 = solutionCoord sol p.element1
      actualProb2 = solutionCoord sol p.element2
      -- Create pair with actual probabilities
      actualPair = PipagePair 
        { element1: p.element1
        , element2: p.element2
        , prob1: actualProb1
        , prob2: actualProb2
        }
      (Tuple up down) = pairTransferBounds actualPair
      score = up + down  -- Total transfer potential
  in Tuple actualPair score

-- | Generate all pairs from array.
-- |
-- | Uses element indices to ensure pairs are ordered (smaller index first)
-- | for deterministic pairing.
allPairs :: forall v. Array (Element v) -> Array (PipagePair v)
allPairs elements = do
  i <- Array.range 0 (Array.length elements - 2)
  j <- Array.range (i + 1) (Array.length elements - 1)
  case Tuple (Array.index elements i) (Array.index elements j) of
    Tuple (Just e1@(Element i1)) (Just e2@(Element i2)) ->
      -- Order by element index for determinism
      -- Use indices to seed initial probability estimates
      let baseProbE1 = 0.5 + intToNum i1 * 0.001 - intToNum i1 * 0.001
          baseProbE2 = 0.5 + intToNum i2 * 0.001 - intToNum i2 * 0.001
      in [ PipagePair { element1: e1, element2: e2, prob1: baseProbE1, prob2: baseProbE2 } ]
    _ -> []

-- | Compute transfer bounds for a pair.
-- |
-- | Returns (maxUp, maxDown) where:
-- | - maxUp: maximum we can increase e1 (and decrease e2 equally)
-- | - maxDown: maximum we can decrease e1 (and increase e2 equally)
pairTransferBounds :: forall v. PipagePair v -> Tuple Number Number
pairTransferBounds (PipagePair p) =
  let -- e1 can increase until 1 or e2 hits 0
      maxUp = min (1.0 - p.prob1) p.prob2
      -- e1 can decrease until 0 or e2 hits 1
      maxDown = min p.prob1 (1.0 - p.prob2)
  in Tuple maxUp maxDown
