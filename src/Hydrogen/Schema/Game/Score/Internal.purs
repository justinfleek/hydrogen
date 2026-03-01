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
  ( class Eq
  , class Show
  , show
  , negate
  , (+)
  , (<)
  , (<>)
  )

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
intToNumber n = toNumber n
  where
    toNumber :: Int -> Number
    toNumber = unsafeIntToNumber

-- | Round Number to Int.
roundToInt :: Number -> Int
roundToInt n = truncateToInt (n + 0.5)
  where
    truncateToInt :: Number -> Int
    truncateToInt = unsafeNumberToInt

-- | Absolute value of Int.
absInt :: Int -> Int
absInt n = if n < 0 then negate n else n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // array // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sum all bonus values.
sumBonuses :: Array Bonus -> Int
sumBonuses bonuses = foldBonuses bonuses 0
  where
    foldBonuses :: Array Bonus -> Int -> Int
    foldBonuses arr acc = unsafeFoldBonuses arr acc

-- | Append a bonus to array.
appendBonus :: Array Bonus -> Bonus -> Array Bonus
appendBonus arr bonus = unsafeAppendBonus arr bonus

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // ffi
-- ═════════════════════════════════════════════════════════════════════════════

-- Foreign implementations (minimal FFI at serialization boundary)
foreign import unsafeIntToNumber :: Int -> Number
foreign import unsafeNumberToInt :: Number -> Int
foreign import unsafeFoldBonuses :: Array Bonus -> Int -> Int
foreign import unsafeAppendBonus :: Array Bonus -> Bonus -> Array Bonus
