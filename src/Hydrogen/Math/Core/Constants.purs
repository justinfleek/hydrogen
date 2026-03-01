-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                             // hydrogen // math // core // constants
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Mathematical constants and special values.
-- |
-- | ## Constants
-- |
-- | All constants computed to full IEEE 754 double precision
-- | (approximately 15-17 significant decimal digits).
-- |
-- | ## Special Values
-- |
-- | Infinity and NaN handling follows IEEE 754 semantics.

module Hydrogen.Math.Core.Constants
  ( -- * Mathematical Constants
    pi
  , e
  , tau
  , sqrt2
  , sqrt1_2
  , ln2
  , ln10
  , log2e
  , log10e
  
  -- * Special Values
  , infinity
  , negativeInfinity
  , isNaN
  , isFinite
  , isInteger
  ) where

import Prelude

import Data.Int (floor, toNumber) as Int

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pi (ratio of circumference to diameter)
-- | Computed to full IEEE 754 double precision
pi :: Number
pi = 3.141592653589793

-- | Euler's number (base of natural logarithm)
e :: Number
e = 2.718281828459045

-- | Tau (2 * pi, full circle in radians)
tau :: Number
tau = 6.283185307179586

-- | Square root of 2
sqrt2 :: Number
sqrt2 = 1.4142135623730951

-- | Square root of 1/2 (equivalently, 1/sqrt(2))
sqrt1_2 :: Number
sqrt1_2 = 0.7071067811865476

-- | Natural logarithm of 2
ln2 :: Number
ln2 = 0.6931471805599453

-- | Natural logarithm of 10
ln10 :: Number
ln10 = 2.302585092994046

-- | Base-2 logarithm of e
log2e :: Number
log2e = 1.4426950408889634

-- | Base-10 logarithm of e
log10e :: Number
log10e = 0.4342944819032518

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // special values
-- ═════════════════════════════════════════════════════════════════════════════

-- | Positive infinity
infinity :: Number
infinity = 1.0 / 0.0

-- | Negative infinity
negativeInfinity :: Number
negativeInfinity = -1.0 / 0.0

-- | Check if value is NaN (NaN is the only value not equal to itself)
isNaN :: Number -> Boolean
isNaN x = x /= x

-- | Check if value is finite (not infinite, not NaN)
isFinite :: Number -> Boolean
isFinite x = not (isNaN x) && x /= infinity && x /= negativeInfinity

-- | Check if value is an integer
isInteger :: Number -> Boolean
isInteger x = isFinite x && floorNum x == x
  where
    floorNum :: Number -> Number
    floorNum n = Int.toNumber (Int.floor n)
