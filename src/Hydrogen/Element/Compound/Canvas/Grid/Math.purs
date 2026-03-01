-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                    // hydrogen // element // compound // canvas // grid // math
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Grid Math — Trigonometry and geometry helpers for grid generation.
-- |
-- | ## Pure Math Functions
-- |
-- | All functions are pure approximations using Taylor series or iterative
-- | methods. No FFI required.
-- |
-- | - **Trigonometry**: sin, cos, tan approximations
-- | - **Geometry**: sqrt, abs, distance
-- | - **Clipping**: Cohen-Sutherland line clipping
-- |
-- | ## Dependencies
-- |
-- | - Prelude (basic operations)
-- | - Data.Maybe (Maybe)

module Hydrogen.Element.Compound.Canvas.Grid.Math
  ( -- * Constants
    pi
  , phi
  
  -- * Trigonometry
  , sinApprox
  , cosApprox
  , tanApprox
  , degreesToRadians
  
  -- * Basic Math
  , sqrt
  , abs
  , clamp
  
  -- * Line Clipping
  , clipLineToBounds
  
  -- * Integer Operations
  , mod
  , bitwiseAnd
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (==)
  , (/=)
  , (&&)
  , max
  , min
  , negate
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pi constant.
pi :: Number
pi = 3.14159265358979323846

-- | Golden ratio (phi).
phi :: Number
phi = 1.6180339887498948482

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // trigonometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert degrees to radians.
degreesToRadians :: Number -> Number
degreesToRadians deg = deg * pi / 180.0

-- | Approximate cosine using Taylor series.
-- |
-- | Accurate to ~6 decimal places for |x| < 2π.
cosApprox :: Number -> Number
cosApprox x = 
  let 
    -- Normalize to [-π, π]
    normalized = normalizeAngle x
    x2 = normalized * normalized
    x4 = x2 * x2
    x6 = x4 * x2
    x8 = x6 * x2
  in 1.0 - (x2 / 2.0) + (x4 / 24.0) - (x6 / 720.0) + (x8 / 40320.0)

-- | Approximate sine using Taylor series.
-- |
-- | Accurate to ~6 decimal places for |x| < 2π.
sinApprox :: Number -> Number
sinApprox x = 
  let 
    normalized = normalizeAngle x
    x2 = normalized * normalized
    x3 = normalized * x2
    x5 = x3 * x2
    x7 = x5 * x2
    x9 = x7 * x2
  in normalized - (x3 / 6.0) + (x5 / 120.0) - (x7 / 5040.0) + (x9 / 362880.0)

-- | Approximate tangent.
tanApprox :: Number -> Number
tanApprox x = 
  let c = cosApprox x
  in if abs c < 0.0001 then 1000000.0  -- Avoid division by near-zero
     else sinApprox x / c

-- | Normalize angle to [-π, π].
normalizeAngle :: Number -> Number
normalizeAngle x =
  let 
    twoPi = 2.0 * pi
    shifted = x + pi
    normalized = shifted - twoPi * toNumber (floor (shifted / twoPi))
  in normalized - pi

-- | Floor for normalization (simple implementation).
floor :: Number -> Int
floor n = 
  let truncated = truncateNumber n
  in if n < 0.0 && toNumber truncated /= n 
     then truncated - 1 
     else truncated

-- | Truncate toward zero.
truncateNumber :: Number -> Int
truncateNumber n = truncateImpl n

-- | Convert Int to Number.
toNumber :: Int -> Number
toNumber = toNumberImpl

-- Implementation helpers (pure, no FFI)
truncateImpl :: Number -> Int
truncateImpl n = 
  if n >= 0.0 
    then truncatePositive n 0
    else negate (truncatePositive (negate n) 0)

truncatePositive :: Number -> Int -> Int
truncatePositive n acc =
  if n < 1.0 then acc
  else truncatePositive (n - 1.0) (acc + 1)

toNumberImpl :: Int -> Number
toNumberImpl i = 
  if i >= 0 
    then toNumberPositive i 0.0
    else negate (toNumberPositive (negate i) 0.0)

toNumberPositive :: Int -> Number -> Number
toNumberPositive i acc =
  if i <= 0 then acc
  else toNumberPositive (i - 1) (acc + 1.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // basic math
-- ═════════════════════════════════════════════════════════════════════════════

-- | Approximate square root using Newton's method.
-- |
-- | Converges in ~10 iterations for most inputs.
sqrt :: Number -> Number
sqrt n =
  if n <= 0.0 then 0.0
  else newtonSqrt n (n / 2.0) 0

-- | Newton's method for square root.
newtonSqrt :: Number -> Number -> Int -> Number
newtonSqrt n guess iterations =
  if iterations >= 10 then guess
  else 
    let nextGuess = (guess + n / guess) / 2.0
    in if abs (nextGuess - guess) < 0.0000001 
       then nextGuess 
       else newtonSqrt n nextGuess (iterations + 1)

-- | Absolute value.
abs :: Number -> Number
abs n = if n < 0.0 then negate n else n

-- | Clamp a value to a range.
clamp :: Number -> Number -> Number -> Number
clamp minVal maxVal n = max minVal (min maxVal n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // line clipping
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clip a line to a bounding box using Cohen-Sutherland algorithm.
-- |
-- | Returns Nothing if line is entirely outside bounds.
clipLineToBounds :: Number -> Number -> Number -> Number 
                 -> { x :: Number, y :: Number, width :: Number, height :: Number }
                 -> Maybe { x1 :: Number, y1 :: Number, x2 :: Number, y2 :: Number }
clipLineToBounds x1 y1 x2 y2 bounds =
  let
    xMin = bounds.x
    xMax = bounds.x + bounds.width
    yMin = bounds.y
    yMax = bounds.y + bounds.height
    
    code1 = computeOutcode x1 y1 xMin xMax yMin yMax
    code2 = computeOutcode x2 y2 xMin xMax yMin yMax
    
  in clipLineHelper x1 y1 x2 y2 code1 code2 xMin xMax yMin yMax 0

-- | Outcode bits for Cohen-Sutherland.
-- |
-- | Bit layout: TOP(8) | BOTTOM(4) | RIGHT(2) | LEFT(1)
computeOutcode :: Number -> Number -> Number -> Number -> Number -> Number -> Int
computeOutcode x y xMin xMax yMin yMax =
  let
    left = if x < xMin then 1 else 0
    right = if x > xMax then 2 else 0
    bottom = if y < yMin then 4 else 0
    top = if y > yMax then 8 else 0
  in left + right + bottom + top

-- | Iterative line clipping helper.
clipLineHelper :: Number -> Number -> Number -> Number -> Int -> Int 
               -> Number -> Number -> Number -> Number -> Int
               -> Maybe { x1 :: Number, y1 :: Number, x2 :: Number, y2 :: Number }
clipLineHelper x1 y1 x2 y2 code1 code2 xMin xMax yMin yMax iterations =
  if iterations > 10 then Nothing  -- Safety limit
  else if (code1 == 0) && (code2 == 0) then 
    -- Both inside
    Just { x1, y1, x2, y2 }
  else if (bitwiseAnd code1 code2) /= 0 then 
    -- Both outside same region
    Nothing
  else
    -- Need to clip
    let
      codeOut = if code1 /= 0 then code1 else code2
      result = findIntersection x1 y1 x2 y2 codeOut xMin xMax yMin yMax
    in case result of
      Nothing -> Nothing
      Just pt ->
        if code1 /= 0 then
          let newCode = computeOutcode pt.x pt.y xMin xMax yMin yMax
          in clipLineHelper pt.x pt.y x2 y2 newCode code2 xMin xMax yMin yMax (iterations + 1)
        else
          let newCode = computeOutcode pt.x pt.y xMin xMax yMin yMax
          in clipLineHelper x1 y1 pt.x pt.y code1 newCode xMin xMax yMin yMax (iterations + 1)

-- | Find intersection with clip boundary.
findIntersection :: Number -> Number -> Number -> Number -> Int 
                 -> Number -> Number -> Number -> Number
                 -> Maybe { x :: Number, y :: Number }
findIntersection x1 y1 x2 y2 code xMin xMax yMin yMax =
  let
    dx = x2 - x1
    dy = y2 - y1
  in
    if (bitwiseAnd code 8) /= 0 then
      -- Above (top)
      let x = x1 + dx * (yMax - y1) / dy
      in Just { x, y: yMax }
    else if (bitwiseAnd code 4) /= 0 then
      -- Below (bottom)
      let x = x1 + dx * (yMin - y1) / dy
      in Just { x, y: yMin }
    else if (bitwiseAnd code 2) /= 0 then
      -- Right
      let y = y1 + dy * (xMax - x1) / dx
      in Just { x: xMax, y }
    else if (bitwiseAnd code 1) /= 0 then
      -- Left
      let y = y1 + dy * (xMin - x1) / dx
      in Just { x: xMin, y }
    else
      Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // integer operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Integer modulo.
mod :: Int -> Int -> Int
mod a b = a - (a / b) * b

-- | Simple bitwise AND for outcodes (4-bit).
-- |
-- | Works for values 0-15 (4 bits).
bitwiseAnd :: Int -> Int -> Int
bitwiseAnd a b = 
  let
    a1 = a `mod` 2
    b1 = b `mod` 2
    a2 = (a / 2) `mod` 2
    b2 = (b / 2) `mod` 2
    a4 = (a / 4) `mod` 2
    b4 = (b / 4) `mod` 2
    a8 = (a / 8) `mod` 2
    b8 = (b / 8) `mod` 2
  in (a1 * b1) + (a2 * b2 * 2) + (a4 * b4 * 4) + (a8 * b8 * 8)
