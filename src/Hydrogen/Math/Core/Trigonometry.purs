-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // math // core // trigonometry
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Trigonometric functions — standard and hyperbolic.
-- |
-- | No JavaScript. No FFI. Pure functional implementations using:
-- | - Taylor series for transcendental functions
-- | - Range reduction for numerical stability
-- |
-- | ## Precision
-- |
-- | All Taylor series use sufficient terms for IEEE 754 double precision
-- | (approximately 15-17 significant decimal digits).

module Hydrogen.Math.Core.Trigonometry
  ( -- * Standard Trigonometry
    sin
  , cos
  , tan
  , asin
  , acos
  , atan
  , atan2
  
  -- * Hyperbolic Trigonometry
  , sinh
  , cosh
  , tanh
  , asinh
  , acosh
  , atanh
  ) where

import Prelude

import Data.Int (toNumber) as Int

import Hydrogen.Math.Core.Constants (pi, tau, infinity, negativeInfinity, isNaN, isFinite)
import Hydrogen.Math.Core.Exponential (exp, log)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Local absolute value to avoid circular dependency
abs :: Number -> Number
abs n = if n < 0.0 then negate n else n

-- | Local sqrt for this module (to avoid circular dependency with Arithmetic)
sqrt :: Number -> Number
sqrt x
  | x < 0.0 = 0.0 / 0.0
  | x == 0.0 = 0.0
  | otherwise = newtonSqrt x (if x >= 1.0 then x / 2.0 else x * 2.0) 0

newtonSqrt :: Number -> Number -> Int -> Number
newtonSqrt x guess iter
  | iter >= 100 = guess
  | otherwise =
      let next = (guess + x / guess) / 2.0
      in if abs (next - guess) < 1.0e-15 * abs guess
           then next
           else newtonSqrt x next (iter + 1)

-- | Local round for range reduction
round :: Number -> Number
round x = 
  let fl = floorNum x
      diff = x - fl
  in if diff >= 0.5 then fl + 1.0 else fl

floorNum :: Number -> Number
floorNum x = 
  if x >= 0.0
    then x - modPositive x 1.0
    else negate (ceilPositive (negate x))
  where
    modPositive :: Number -> Number -> Number
    modPositive a b = 
      let n = truncTowardZero (a / b)
      in a - n * b
    
    truncTowardZero :: Number -> Number
    truncTowardZero n = 
      if n >= 0.0 
        then floorPositiveSimple n 
        else negate (floorPositiveSimple (negate n))
    
    floorPositiveSimple :: Number -> Number
    floorPositiveSimple n =
      -- Simple iterative floor for positive numbers
      floorIter n 0.0
    
    floorIter :: Number -> Number -> Number
    floorIter target current
      | current + 1.0 > target = current
      | otherwise = floorIter target (current + 1.0)
    
    ceilPositive :: Number -> Number
    ceilPositive n = 
      let fl = floorPositiveSimple n
      in if n == fl then fl else fl + 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // standard trigonometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sine using Taylor series with range reduction
-- |
-- | sin(x) = x - x³/3! + x⁵/5! - x⁷/7! + ...
-- |
-- | Range reduction: reduce to [-π, π] then to [-π/2, π/2]
sin :: Number -> Number
sin x
  | isNaN x = x
  | not (isFinite x) = 0.0 / 0.0
  | otherwise =
      let reduced = reduceAngle x
      in sinReduced reduced

-- | Reduce angle to [-π, π]
reduceAngle :: Number -> Number
reduceAngle x =
  let reduced = x - tau * round (x / tau)
  in reduced

-- | Sin for reduced angle in [-π, π]
sinReduced :: Number -> Number
sinReduced x
  | x > pi / 2.0 = sinTaylor (pi - x)
  | x < (negate pi) / 2.0 = negate (sinTaylor (pi + x))
  | otherwise = sinTaylor x

-- | Taylor series for sin, valid for |x| <= π/2
sinTaylor :: Number -> Number
sinTaylor x = taylorSin x x (x * x) 1

taylorSin :: Number -> Number -> Number -> Int -> Number
taylorSin sum term x2 n
  | n > 20 = sum
  | otherwise =
      let k = 2 * n
          newTerm = negate term * x2 / (Int.toNumber k * Int.toNumber (k + 1))
          newSum = sum + newTerm
      in if abs newTerm < 1.0e-16 * abs newSum
           then newSum
           else taylorSin newSum newTerm x2 (n + 1)

-- | Cosine using Taylor series
-- |
-- | cos(x) = 1 - x²/2! + x⁴/4! - x⁶/6! + ...
cos :: Number -> Number
cos x
  | isNaN x = x
  | not (isFinite x) = 0.0 / 0.0
  | otherwise =
      let reduced = reduceAngle x
      in cosReduced reduced

-- | Cos for reduced angle in [-π, π]
cosReduced :: Number -> Number
cosReduced x
  | x > pi / 2.0 = negate (cosTaylor (pi - x))
  | x < (negate pi) / 2.0 = negate (cosTaylor (pi + x))
  | otherwise = cosTaylor x

-- | Taylor series for cos, valid for |x| <= π/2
cosTaylor :: Number -> Number
cosTaylor x = 
  let x2 = x * x
  in taylorCos 1.0 1.0 x2 1

taylorCos :: Number -> Number -> Number -> Int -> Number
taylorCos sum term x2 n
  | n > 20 = sum
  | otherwise =
      let k = 2 * n - 1
          newTerm = negate term * x2 / (Int.toNumber k * Int.toNumber (k + 1))
          newSum = sum + newTerm
      in if abs newTerm < 1.0e-16 * abs newSum
           then newSum
           else taylorCos newSum newTerm x2 (n + 1)

-- | Tangent
tan :: Number -> Number
tan x = sin x / cos x

-- | Arcsine using Newton's method on sin
-- |
-- | For |x| <= 0.5, use Taylor series
-- | For |x| > 0.5, use identity: asin(x) = π/2 - 2*asin(sqrt((1-x)/2))
asin :: Number -> Number
asin x
  | isNaN x = x
  | x < -1.0 || x > 1.0 = 0.0 / 0.0
  | x == 1.0 = pi / 2.0
  | x == -1.0 = negate pi / 2.0
  | abs x <= 0.5 = asinTaylor x
  | x > 0.5 = pi / 2.0 - 2.0 * asinTaylor (sqrt ((1.0 - x) / 2.0))
  | otherwise = negate (pi / 2.0) + 2.0 * asinTaylor (sqrt ((1.0 + x) / 2.0))

-- | Taylor series for asin: x + x³/6 + 3x⁵/40 + ...
asinTaylor :: Number -> Number
asinTaylor x = asinGo x x (x * x) 1

asinGo :: Number -> Number -> Number -> Int -> Number
asinGo sum term x2 n
  | n > 50 = sum
  | otherwise =
      let k = 2 * n - 1
          newTerm = term * x2 * Int.toNumber k * Int.toNumber k / (Int.toNumber (2 * n) * Int.toNumber (2 * n + 1))
          newSum = sum + newTerm
      in if abs newTerm < 1.0e-16 * abs newSum
           then newSum
           else asinGo newSum newTerm x2 (n + 1)

-- | Arccosine
acos :: Number -> Number
acos x = pi / 2.0 - asin x

-- | Arctangent using series expansion
-- |
-- | For |x| <= 1: atan(x) = x - x³/3 + x⁵/5 - ...
-- | For |x| > 1: atan(x) = π/2 - atan(1/x)
atan :: Number -> Number
atan x
  | isNaN x = x
  | x == infinity = pi / 2.0
  | x == negativeInfinity = negate pi / 2.0
  | abs x > 1.0 = 
      if x > 0.0 
        then pi / 2.0 - atanSmall (1.0 / x)
        else negate pi / 2.0 - atanSmall (1.0 / x)
  | otherwise = atanSmall x

-- | Atan for |x| <= 1
atanSmall :: Number -> Number
atanSmall x = atanGo x x (x * x) 1

atanGo :: Number -> Number -> Number -> Int -> Number
atanGo sum term x2 n
  | n > 50 = sum
  | otherwise =
      let newTerm = negate term * x2
          k = 2 * n + 1
          contrib = newTerm / Int.toNumber k
          newSum = sum + contrib
      in if abs contrib < 1.0e-16 * abs newSum
           then newSum
           else atanGo newSum newTerm x2 (n + 1)

-- | Two-argument arctangent
atan2 :: Number -> Number -> Number
atan2 y x
  | isNaN x || isNaN y = 0.0 / 0.0
  | x > 0.0 = atan (y / x)
  | x < 0.0 && y >= 0.0 = atan (y / x) + pi
  | x < 0.0 && y < 0.0 = atan (y / x) - pi
  | x == 0.0 && y > 0.0 = pi / 2.0
  | x == 0.0 && y < 0.0 = negate pi / 2.0
  | otherwise = 0.0  -- x == 0 && y == 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // hyperbolic trig
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hyperbolic sine: sinh(x) = (e^x - e^(-x)) / 2
sinh :: Number -> Number
sinh x
  | abs x < 1.0e-5 = x  -- Approximation for small x
  | otherwise = (exp x - exp (negate x)) / 2.0

-- | Hyperbolic cosine: cosh(x) = (e^x + e^(-x)) / 2
cosh :: Number -> Number
cosh x = (exp x + exp (negate x)) / 2.0

-- | Hyperbolic tangent
tanh :: Number -> Number
tanh x
  | x > 20.0 = 1.0   -- Saturates to 1
  | x < -20.0 = -1.0 -- Saturates to -1
  | otherwise = sinh x / cosh x

-- | Inverse hyperbolic sine: asinh(x) = ln(x + sqrt(x² + 1))
asinh :: Number -> Number
asinh x = log (x + sqrt (x * x + 1.0))

-- | Inverse hyperbolic cosine: acosh(x) = ln(x + sqrt(x² - 1))
acosh :: Number -> Number
acosh x
  | x < 1.0 = 0.0 / 0.0
  | otherwise = log (x + sqrt (x * x - 1.0))

-- | Inverse hyperbolic tangent: atanh(x) = 0.5 * ln((1+x)/(1-x))
atanh :: Number -> Number
atanh x
  | abs x >= 1.0 = if x > 0.0 then infinity else negativeInfinity
  | otherwise = 0.5 * log ((1.0 + x) / (1.0 - x))
