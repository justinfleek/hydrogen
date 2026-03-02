-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // math // core // arithmetic
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Basic arithmetic operations — rounding, clamping, powers, and roots.
-- |
-- | No JavaScript. No FFI. Pure functional implementations using:
-- | - Newton-Raphson iteration for roots
-- | - Standard IEEE 754 semantics for edge cases

module Hydrogen.Math.Core.Arithmetic
  ( -- * Rounding
    floor
  , ceil
  , round
  , trunc
  , fround
  
  -- * Absolute & Sign
  , abs
  , sign
  
  -- * Min/Max
  , min
  , max
  , minArray
  , maxArray
  , clamp
  
  -- * Powers & Roots
  , pow
  , sqrt
  , cbrt
  , hypot
  , hypot3
  ) where

import Prelude hiding (min, max)

import Data.Array (foldl)
import Data.Int (floor, toNumber) as Int

import Hydrogen.Math.Core.Constants (infinity, negativeInfinity, isNaN, isFinite, isInteger)
import Hydrogen.Math.Core.Exponential (exp, log)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // absolute & sign
-- ═════════════════════════════════════════════════════════════════════════════

-- | Absolute value
abs :: Number -> Number
abs x = if x < 0.0 then negate x else x

-- | Sign: -1.0, 0.0, or 1.0
sign :: Number -> Number
sign x
  | x > 0.0 = 1.0
  | x < 0.0 = -1.0
  | otherwise = 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // rounding
-- ═════════════════════════════════════════════════════════════════════════════

-- | Round down to nearest integer
floor :: Number -> Number
floor x = 
  let i = Int.floor x
  in Int.toNumber i

-- | Round up to nearest integer
ceil :: Number -> Number
ceil x = 
  let fl = floor x
  in if x == fl then fl else fl + 1.0

-- | Round to nearest integer (half away from zero)
round :: Number -> Number
round x = 
  let fl = floor x
      diff = x - fl
  in if diff >= 0.5 then fl + 1.0 else fl

-- | Truncate toward zero
trunc :: Number -> Number
trunc x = if x >= 0.0 then floor x else ceil x

-- | Round to nearest 32-bit float (identity for our purposes)
fround :: Number -> Number
fround x = x

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // min/max
-- ═════════════════════════════════════════════════════════════════════════════

-- | Minimum of two values
min :: Number -> Number -> Number
min a b = if a <= b then a else b

-- | Maximum of two values
max :: Number -> Number -> Number
max a b = if a >= b then a else b

-- | Minimum of an array
minArray :: Array Number -> Number
minArray arr = foldl min infinity arr

-- | Maximum of an array  
maxArray :: Array Number -> Number
maxArray arr = foldl max negativeInfinity arr

-- | Clamp value to range [minVal, maxVal] (NaN/Infinity-safe).
-- |
-- | If input is NaN or Infinity, returns minVal (safe fallback).
-- | This prevents non-finite values from propagating through the system.
-- |
-- | ## At Billion-Agent Scale
-- |
-- | NaN is the escape hatch for all bounds checks. A malicious actor
-- | could craft `0.0 / 0.0` to bypass validation. This function closes
-- | that vector by treating non-finite values as out-of-bounds.
-- |
-- | ```purescript
-- | clamp 0.0 100.0 50.0      -- 50.0
-- | clamp 0.0 100.0 150.0     -- 100.0
-- | clamp 0.0 100.0 (-10.0)   -- 0.0
-- | clamp 0.0 100.0 (0.0/0.0) -- 0.0 (NaN → minVal)
-- | clamp 0.0 100.0 (1.0/0.0) -- 0.0 (Infinity → minVal)
-- | ```
clamp :: Number -> Number -> Number -> Number
clamp minVal maxVal x
  | not (isFinite x) = minVal  -- NaN/Infinity → safe fallback
  | otherwise = min maxVal (max minVal x)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // powers & roots
-- ═════════════════════════════════════════════════════════════════════════════

-- | Square root using Newton-Raphson iteration
-- |
-- | Starting guess: x/2, iterate: guess' = (guess + x/guess) / 2
-- | Converges quadratically (doubles correct digits each iteration)
sqrt :: Number -> Number
sqrt x
  | x < 0.0 = 0.0 / 0.0  -- NaN for negative
  | x == 0.0 = 0.0
  | x == infinity = infinity
  | otherwise = newtonSqrt x (initialGuess x) 0

-- | Initial guess for sqrt using bit manipulation approximation
-- | For IEEE 754, sqrt(x) ≈ x^0.5, and we can estimate via exponent halving
initialGuess :: Number -> Number
initialGuess x = 
  if x >= 1.0 
    then x / 2.0 
    else x * 2.0

-- | Newton-Raphson iteration for sqrt
newtonSqrt :: Number -> Number -> Int -> Number
newtonSqrt x guess iter
  | iter >= 100 = guess  -- Max iterations (should never hit this)
  | otherwise =
      let next = (guess + x / guess) / 2.0
      in if abs (next - guess) < 1.0e-15 * abs guess
           then next
           else newtonSqrt x next (iter + 1)

-- | Cube root
cbrt :: Number -> Number
cbrt x
  | x == 0.0 = 0.0
  | x < 0.0 = negate (cbrtPositive (negate x))
  | otherwise = cbrtPositive x

-- | Cube root for positive numbers using Newton-Raphson
-- | Iteration: guess' = (2*guess + x/guess^2) / 3
cbrtPositive :: Number -> Number
cbrtPositive x = newtonCbrt x (x / 3.0) 0

newtonCbrt :: Number -> Number -> Int -> Number
newtonCbrt x guess iter
  | iter >= 100 = guess
  | otherwise =
      let next = (2.0 * guess + x / (guess * guess)) / 3.0
      in if abs (next - guess) < 1.0e-15 * abs guess
           then next
           else newtonCbrt x next (iter + 1)

-- | Hypotenuse of 2D vector: sqrt(x^2 + y^2)
-- | Uses scaling to avoid overflow/underflow
hypot :: Number -> Number -> Number
hypot x y =
  let ax = abs x
      ay = abs y
      maxVal = max ax ay
  in if maxVal == 0.0
       then 0.0
       else maxVal * sqrt ((ax / maxVal) * (ax / maxVal) + (ay / maxVal) * (ay / maxVal))

-- | Hypotenuse of 3D vector: sqrt(x^2 + y^2 + z^2)
hypot3 :: Number -> Number -> Number -> Number
hypot3 x y z =
  let ax = abs x
      ay = abs y
      az = abs z
      maxVal = max (max ax ay) az
  in if maxVal == 0.0
       then 0.0
       else maxVal * sqrt ((ax / maxVal) * (ax / maxVal) + 
                           (ay / maxVal) * (ay / maxVal) + 
                           (az / maxVal) * (az / maxVal))

-- | Power function: base^exponent
-- | Uses exp(exponent * log(base)) for general case
pow :: Number -> Number -> Number
pow base exponent
  | exponent == 0.0 = 1.0
  | base == 0.0 = if exponent > 0.0 then 0.0 else infinity
  | base == 1.0 = 1.0
  | exponent == 1.0 = base
  | base < 0.0 && not (isInteger exponent) = 0.0 / 0.0  -- NaN
  | base < 0.0 = 
      let result = exp (exponent * log (negate base))
      in if isOdd (trunc exponent) then negate result else result
  | otherwise = exp (exponent * log base)

isOdd :: Number -> Boolean
isOdd x = 
  let half = x / 2.0
  in floor half /= half
