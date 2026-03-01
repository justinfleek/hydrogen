-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // math // core // exponential
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Exponential and logarithmic functions.
-- |
-- | No JavaScript. No FFI. Pure functional implementations using:
-- | - Taylor series for exp
-- | - Arctanh series for log
-- | - Range reduction for numerical stability

module Hydrogen.Math.Core.Exponential
  ( -- * Exponential
    exp
  , expm1
  
  -- * Logarithm
  , log
  , log10
  , log2
  , log1p
  ) where

import Prelude

import Data.Int (toNumber) as Int

import Hydrogen.Math.Core.Constants (infinity, negativeInfinity, isNaN, ln2, ln10)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // exponential
-- ═════════════════════════════════════════════════════════════════════════════

-- | Exponential function e^x using Taylor series
-- |
-- | e^x = 1 + x + x²/2! + x³/3! + x⁴/4! + ...
-- |
-- | For large |x|, we use range reduction: e^x = e^(x/2) * e^(x/2)
exp :: Number -> Number
exp x
  | isNaN x = x
  | x == infinity = infinity
  | x == negativeInfinity = 0.0
  | x == 0.0 = 1.0
  | x > 709.0 = infinity  -- Overflow threshold
  | x < -745.0 = 0.0       -- Underflow threshold
  | abs x > 1.0 = 
      -- Range reduction: e^x = (e^(x/2))^2
      let half = exp (x / 2.0)
      in half * half
  | otherwise = expTaylor x

-- | Local absolute value to avoid circular dependency
abs :: Number -> Number
abs n = if n < 0.0 then negate n else n

-- | Taylor series for exp, valid for |x| <= 1
expTaylor :: Number -> Number
expTaylor x = taylorExp x 1.0 1.0 1

taylorExp :: Number -> Number -> Number -> Int -> Number
taylorExp x sum term n
  | n > 30 = sum  -- 30 terms is more than enough for double precision
  | otherwise =
      let newTerm = term * x / Int.toNumber n
          newSum = sum + newTerm
      in if abs newTerm < 1.0e-16 * abs newSum
           then newSum
           else taylorExp x newSum newTerm (n + 1)

-- | exp(x) - 1, more precise for small x
expm1 :: Number -> Number
expm1 x
  | abs x < 1.0e-5 = x + x * x / 2.0  -- First-order approximation
  | otherwise = exp x - 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // logarithm
-- ═════════════════════════════════════════════════════════════════════════════

-- | Natural logarithm using series expansion
-- |
-- | For x near 1, use: ln(x) = 2 * (y + y³/3 + y⁵/5 + ...) where y = (x-1)/(x+1)
-- | For other x, use range reduction: ln(x) = ln(x/e^n) + n
log :: Number -> Number
log x
  | isNaN x = x
  | x < 0.0 = 0.0 / 0.0  -- NaN
  | x == 0.0 = negativeInfinity
  | x == infinity = infinity
  | x == 1.0 = 0.0
  | otherwise = 
      -- Range reduction to bring x close to 1
      let reduced = reduceForLog x 0
      in logNear1 reduced.value + Int.toNumber reduced.exponent * ln2

-- | Reduce x to range [0.5, 2) by dividing/multiplying by 2
reduceForLog :: Number -> Int -> { value :: Number, exponent :: Int }
reduceForLog x n
  | x >= 2.0 = reduceForLog (x / 2.0) (n + 1)
  | x < 0.5 = reduceForLog (x * 2.0) (n - 1)
  | otherwise = { value: x, exponent: n }

-- | Logarithm for values near 1 using arctanh series
-- | ln(x) = 2 * arctanh((x-1)/(x+1))
logNear1 :: Number -> Number
logNear1 x =
  let y = (x - 1.0) / (x + 1.0)
  in 2.0 * atanhSeries y

-- | Arctanh series: y + y³/3 + y⁵/5 + ...
atanhSeries :: Number -> Number
atanhSeries y = atanhSeriesGo y y (y * y) 1

atanhSeriesGo :: Number -> Number -> Number -> Int -> Number
atanhSeriesGo sum term y2 n
  | n > 50 = sum
  | otherwise =
      let newTerm = term * y2
          k = 2 * n + 1
          contrib = newTerm / Int.toNumber k
          newSum = sum + contrib
      in if abs contrib < 1.0e-16 * abs newSum
           then newSum
           else atanhSeriesGo newSum newTerm y2 (n + 1)

-- | Base-10 logarithm
log10 :: Number -> Number
log10 x = log x / ln10

-- | Base-2 logarithm  
log2 :: Number -> Number
log2 x = log x / ln2

-- | log(1 + x), more precise for small x
log1p :: Number -> Number
log1p x
  | abs x < 1.0e-5 = x - x * x / 2.0  -- First-order approximation
  | otherwise = log (1.0 + x)
