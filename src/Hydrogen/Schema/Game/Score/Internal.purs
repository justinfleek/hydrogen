-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // game // score // internal
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Internal helper functions and FFI for the Score module.
-- |
-- | These functions provide low-level numeric conversions and array operations
-- | that require FFI at the serialization boundary. This module is internal
-- | and should not be imported directly by external code.

module Hydrogen.Schema.Game.Score.Internal
  ( -- * Numeric Conversions
    intToNumber
  , roundToInt
  , absInt
  
  -- * Array Operations
  , sumBonuses
  , appendBonus
  
  -- * Bonus Type (needed for array ops)
  , Bonus
  ) where

import Prelude
  ( negate
  , (+)
  , (<)
  )
import Prim (Int, Number, Array, String)

import Data.Int (toNumber, floor) as Int
import Data.Array (foldl, snoc) as Array

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // bonus // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | A bonus component of a score.
type Bonus =
  { name :: String
  , value :: Int
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // numeric // conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Int to Number.
intToNumber :: Int -> Number
intToNumber = Int.toNumber

-- | Round Number to Int.
-- | Adds 0.5 then floors to achieve rounding behavior.
roundToInt :: Number -> Int
roundToInt n = Int.floor (n + 0.5)

-- | Absolute value of Int.
absInt :: Int -> Int
absInt n = if n < 0 then negate n else n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // array // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sum all bonus values using foldl.
sumBonuses :: Array Bonus -> Int
sumBonuses bonuses = Array.foldl (\acc b -> acc + b.value) 0 bonuses

-- | Append a bonus to array using snoc.
appendBonus :: Array Bonus -> Bonus -> Array Bonus
appendBonus arr bonus = Array.snoc arr bonus
