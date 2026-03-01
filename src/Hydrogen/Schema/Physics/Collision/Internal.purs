-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                      // hydrogen // schema // physics // collision // internal
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Internal — Helper functions for collision primitives.
-- |
-- | ## Purpose
-- |
-- | Provides bounded mathematical helpers used throughout the collision module.
-- | These are internal implementation details, not part of the public API.
-- |
-- | ## Dependencies
-- |
-- | - Prelude (basic operations)
-- | - Data.Number (sqrt)

module Hydrogen.Schema.Physics.Collision.Internal
  ( -- * Numeric Helpers
    minNum
  , maxNum
  , absNum
  , clampNum
  , clampPositive
  , clampUnit
  , clampDepth
  
  -- * Integer Helpers
  , modInt
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( otherwise
  , negate
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // numeric helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Minimum of two numbers
minNum :: Number -> Number -> Number
minNum a b = if a < b then a else b

-- | Maximum of two numbers
maxNum :: Number -> Number -> Number
maxNum a b = if a > b then a else b

-- | Absolute value
absNum :: Number -> Number
absNum n = if n < 0.0 then negate n else n

-- | Clamp to range
clampNum :: Number -> Number -> Number -> Number
clampNum lo hi x
  | x < lo = lo
  | x > hi = hi
  | otherwise = x

-- | Clamp positive (0 to maxVal)
clampPositive :: Number -> Number -> Number
clampPositive maxVal n
  | n < 0.0 = 0.0
  | n > maxVal = maxVal
  | otherwise = n

-- | Clamp to unit range (0 to maxVal)
clampUnit :: Number -> Number -> Number
clampUnit maxVal n
  | n < 0.0 = 0.0
  | n > maxVal = maxVal
  | otherwise = n

-- | Clamp penetration depth to reasonable bounds
clampDepth :: Number -> Number
clampDepth d
  | d < 0.0 = 0.0
  | d > 10000.0 = 10000.0
  | otherwise = d

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // integer helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Integer modulo (for layer check)
modInt :: Int -> Int -> Int
modInt a b = a - (a / b) * b
