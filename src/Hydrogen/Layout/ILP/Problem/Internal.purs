-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // layout // ilp // problem // internal
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Internal — Helper functions for ILP problem operations.
-- |
-- | These utilities are used across the Problem submodules for array
-- | manipulation, indexing, and numeric operations. They are internal
-- | implementation details, not part of the public API.
-- |
-- | Status: INTERNAL

module Hydrogen.Layout.ILP.Problem.Internal
  ( -- * Array Utilities
    getAt
  , zipWithIndex
  , zipArrays
  , mapArray
  
    -- * Numeric Utilities
  , toFloor
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( otherwise
  , ($)
  , (+)
  , (-)
  , (<)
  , (>=)
  )

import Data.Array (snoc, index) as Data.Array
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Data.Foldable (foldl)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // array utilities
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get element at index (returns 0.0 for out of bounds).
getAt :: Int -> Array Number -> Number
getAt i arr = case Data.Array.index arr i of
  Just x -> x
  Nothing -> 0.0

-- | Zip array with indices.
zipWithIndex :: forall a. Array a -> Array (Tuple Int a)
zipWithIndex arr = zipWithIndexGo arr 0 []

zipWithIndexGo :: forall a. Array a -> Int -> Array (Tuple Int a) -> Array (Tuple Int a)
zipWithIndexGo arr i acc = case Data.Array.index arr i of
  Nothing -> acc
  Just x -> zipWithIndexGo arr (i + 1) (Data.Array.snoc acc (Tuple i x))

-- | Zip two arrays together (truncates to shorter length).
zipArrays :: forall a b. Array a -> Array b -> Array (Tuple a b)
zipArrays arr1 arr2 = zipArraysGo arr1 arr2 0 []
  where
    zipArraysGo :: Array a -> Array b -> Int -> Array (Tuple a b) -> Array (Tuple a b)
    zipArraysGo a1 a2 i acc = case Tuple (Data.Array.index a1 i) (Data.Array.index a2 i) of
      Tuple (Just x) (Just y) -> zipArraysGo a1 a2 (i + 1) (Data.Array.snoc acc (Tuple x y))
      _ -> acc

-- | Map over array.
mapArray :: forall a b. (a -> b) -> Array a -> Array b
mapArray f arr = foldl (\acc x -> Data.Array.snoc acc (f x)) [] arr

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // numeric utilities
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Floor a number to nearest integer below.
toFloor :: Number -> Number
toFloor x = toFloorGo x 0.0
  where
    toFloorGo :: Number -> Number -> Number
    toFloorGo n acc
      | n < 0.0 = toFloorNeg n 0.0
      | n < 1.0 = acc
      | otherwise = toFloorGo (n - 1.0) (acc + 1.0)
    
    toFloorNeg :: Number -> Number -> Number
    toFloorNeg n acc
      | n >= 0.0 = acc - 1.0
      | otherwise = toFloorNeg (n + 1.0) (acc - 1.0)
