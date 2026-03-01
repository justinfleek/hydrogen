-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                  // hydrogen // optimize // submodular // continuous // utilities
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Utility functions for continuous submodular optimization.
-- |
-- | ## Pure Number Conversions
-- |
-- | These functions provide FFI-free conversions between Int and Number.
-- | While not optimal for performance, they guarantee pure functional
-- | behavior essential for billion-agent determinism.
-- |
-- | ## Dependencies
-- |
-- | - Data.Array (range, foldl)

module Hydrogen.Optimize.Submodular.Continuous.Utilities
  ( intToNum
  , numToInt
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (+)
  , (-)
  , (<)
  )

import Data.Array as Array
import Data.Foldable (foldl)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // number helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Int to Number.
-- |
-- | Pure implementation using array folding.
intToNum :: Int -> Number
intToNum i = foldl (\acc _ -> acc + 1.0) 0.0 (Array.range 1 i)

-- | Convert Number to Int (floor toward zero).
-- |
-- | Pure implementation without FFI.
numToInt :: Number -> Int
numToInt n = 
  if n < 0.0 
    then negateInt (numToIntPos (negateNum n) 0)
    else numToIntPos n 0
  where
    numToIntPos :: Number -> Int -> Int
    numToIntPos x acc = 
      if x < 1.0 
        then acc 
        else numToIntPos (x - 1.0) (acc + 1)
    negateInt :: Int -> Int
    negateInt x = 0 - x
    negateNum :: Number -> Number
    negateNum x = 0.0 - x
