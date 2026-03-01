-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // optimize // submodular // rounding // util
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Internal utility functions for rounding algorithms.
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Math.Core (mathematical operations)
-- | - Hydrogen.Schema.Bounded (unit interval)
-- | - Hydrogen.Optimize.Submodular.Types (element types)
-- | - Hydrogen.Optimize.Submodular.Continuous (fractional solutions)

module Hydrogen.Optimize.Submodular.Rounding.Util
  ( -- * Value Classification
    isIntegralValue
  , isFractional
  , fractionalElements
  , integralElements
  
  -- * Solution Manipulation
  , updateSolutionCoord
  
  -- * Array Utilities
  , shuffleArray
  , hashIndex
  
  -- * Numeric Utilities
  , intToNum
  , identity
  , pseudoRandom
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
  , (>)
  , (>=)
  , (&&)
  , (||)
  )

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Map as Map
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple (Tuple(Tuple), fst, snd)

import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Bounded (clampUnit, unwrapUnit)
import Hydrogen.Optimize.Submodular.Types (Element(Element))
import Hydrogen.Optimize.Submodular.Continuous
  ( FractionalSolution(FractionalSolution)
  , solutionCoord
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // value classification
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a value is "integral" (close to 0 or 1).
isIntegralValue :: Number -> Boolean
isIntegralValue x = x < 0.0001 || x > 0.9999

-- | Check if an element has fractional value.
isFractional :: forall v. FractionalSolution v -> Element v -> Boolean
isFractional sol e =
  let x = solutionCoord sol e
  in x > 0.0001 && x < 0.9999

-- | Get all fractional elements from a solution.
-- |
-- | Note: Elements not in coords are implicitly 0 (integral), so we only
-- | need to check elements in the map. The groundSetSize is used to
-- | validate that all fractional elements are within bounds.
fractionalElements :: forall v. Ord (Element v) => FractionalSolution v -> Set (Element v)
fractionalElements sol@(FractionalSolution { groundSetSize, coords }) =
  let allIndices = Map.keys coords
      indices = Set.toUnfoldable allIndices :: Array Int
      -- Only consider indices within ground set bounds
      validIndices = Array.filter (\i -> i >= 0 && i < groundSetSize) indices
      fractional = Array.filter (\i -> isFractional sol (Element i)) validIndices
  in Set.fromFoldable (map Element fractional)

-- | Get all integral elements (value = 1) from a solution.
integralElements :: forall v. Ord (Element v) => FractionalSolution v -> Set (Element v)
integralElements (FractionalSolution { coords }) =
  let integral = Map.filter (\x -> unwrapUnit x > 0.9999) coords
      indices = Set.toUnfoldable (Map.keys integral) :: Array Int
  in Set.fromFoldable (map Element indices)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // solution manipulation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Update a coordinate in a fractional solution.
updateSolutionCoord 
  :: forall v
   . FractionalSolution v 
  -> Element v 
  -> Number 
  -> FractionalSolution v
updateSolutionCoord (FractionalSolution { groundSetSize, coords }) (Element i) value =
  FractionalSolution 
    { groundSetSize
    , coords: Map.insert i (clampUnit value) coords
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // array utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Shuffle array using seed.
shuffleArray :: forall a. Array a -> Number -> Array a
shuffleArray arr seed =
  let indexed = Array.mapWithIndex (\i x -> Tuple (hashIndex i seed) x) arr
      sorted = Array.sortBy (\a b -> compare (fst a) (fst b)) indexed
  in map snd sorted

-- | Hash an index with seed for shuffling.
hashIndex :: Int -> Number -> Number
hashIndex i seed = 
  let hash = Math.sin (seed * 12.9898 + intToNum i * 78.233) * 43758.5453
  in hash - Math.floor hash

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // numeric utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Identity function.
identity :: forall a. a -> a
identity x = x

-- | Convert Int to Number.
intToNum :: Int -> Number
intToNum i = foldl (\acc _ -> acc + 1.0) 0.0 (Array.range 1 i)

-- | Simple pseudo-random number generator in [0, 1].
-- |
-- | Uses sine-based hash for reproducibility without FFI.
pseudoRandom :: Number -> Number
pseudoRandom seed =
  let hash = Math.sin (seed * 12.9898 + 78.233) * 43758.5453
  in hash - Math.floor hash
