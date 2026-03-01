-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // schema // physics // force // internal
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Internal helper functions for force calculations.
-- |
-- | These are shared utilities used across force submodules.
-- | Not intended for direct external use.

module Hydrogen.Schema.Physics.Force.Internal
  ( clampForceComponent
  , clampPositive
  , clampUnit
  , absNumber
  , power
  , arrayLength
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( negate
  , otherwise
  , (*)
  , (<)
  , (<=)
  , (>)
  )

import Data.Array as Array

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp force component to reasonable bounds
clampForceComponent :: Number -> Number
clampForceComponent n
  | n > 10000.0 = 10000.0
  | n < -10000.0 = -10000.0
  | otherwise = n

-- | Clamp positive value
clampPositive :: Number -> Number -> Number
clampPositive maxVal n
  | n < 0.0 = 0.0
  | n > maxVal = maxVal
  | otherwise = n

-- | Clamp to unit-ish range
clampUnit :: Number -> Number -> Number
clampUnit maxVal n
  | n < 0.0 = 0.0
  | n > maxVal = maxVal
  | otherwise = n

-- | Absolute value
absNumber :: Number -> Number
absNumber n = if n < 0.0 then negate n else n

-- | Power function (simple iterative for integer-ish exponents)
power :: Number -> Number -> Number
power base exp
  | exp <= 0.0 = 1.0
  | exp <= 1.0 = base
  | exp <= 2.0 = base * base
  | exp <= 3.0 = base * base * base
  | otherwise = base * base * base * base

-- | Array length (pure implementation)
arrayLength :: forall a. Array a -> Int
arrayLength = Array.length
