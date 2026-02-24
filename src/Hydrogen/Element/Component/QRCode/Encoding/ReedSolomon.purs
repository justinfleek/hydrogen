-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // element // qrcode // encoding // reedsolomon
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Reed-Solomon Error Correction — Pure PureScript implementation.
-- |
-- | ## Mathematical Foundation
-- |
-- | Reed-Solomon codes operate over Galois Field GF(2^8), which is:
-- | - A finite field with 256 elements (0-255)
-- | - Addition is XOR
-- | - Multiplication uses the irreducible polynomial x^8 + x^4 + x^3 + x^2 + 1
-- |   (polynomial 0x11D, also known as QR Code polynomial)
-- |
-- | ## How It Works
-- |
-- | 1. **Encode data as polynomial**: Each codeword is a coefficient
-- | 2. **Multiply by x^n**: Shift polynomial left by n positions (n = EC codewords)
-- | 3. **Divide by generator polynomial**: The remainder becomes EC codewords
-- | 4. **Append EC to data**: Complete codeword sequence
-- |
-- | ## Generator Polynomial
-- |
-- | The generator polynomial for n error correction codewords is:
-- |   G(x) = (x - α^0)(x - α^1)(x - α^2)...(x - α^(n-1))
-- |
-- | Where α is the primitive element (2 in GF(2^8)).
-- |
-- | ## QR Code Specifics
-- |
-- | QR codes use:
-- | - Primitive polynomial: x^8 + x^4 + x^3 + x^2 + 1 (0x11D)
-- | - Primitive element α = 2
-- | - Generator polynomials vary by version/EC level (7-30 EC codewords)
-- |
-- | ## Dependencies
-- |
-- | - Prelude (basic operations)
-- | - Data.Array (polynomial coefficient storage)
-- | - BitStream (for integration)
-- | - Types (Codeword)
-- |
-- | ## Proof References
-- |
-- | All operations are algebraically verifiable:
-- | - gfAdd is associative, commutative, self-inverse (XOR properties)
-- | - gfMul is associative, commutative, distributive over gfAdd
-- | - gfPow(α, 255) = 1 (α is primitive element of order 255)
-- | - Generator polynomial has exactly n roots at α^0 through α^(n-1)

module Hydrogen.Element.Component.QRCode.Encoding.ReedSolomon
  ( -- * GF Element Type
    GFElement(GFElement)
  , mkGFElement
  , gfElementValue
  , gfElementAdd
  , gfElementMul
  
  -- * Galois Field GF(2^8) Arithmetic
  , gfAdd
  , gfSub
  , gfMul
  , gfDiv
  , gfPow
  , gfInverse
  , gfExp
  , gfLog
  
  -- * Polynomial Operations
  , Polynomial
  , polyMul
  , polyMulScalar
  , polyAdd
  , polyDivide
  , polyEval
  
  -- * Generator Polynomials
  , generatorPoly
  , generatorPolyCoeffs
  
  -- * Error Correction
  , computeECCodewords
  , computeECForData
  , ecCodewordsNeeded
  
  -- * Lookup Tables
  , expTable
  , logTable
  
  -- * Utilities
  , showPolynomial
  , polynomialDegree
  
  -- * Validation
  , isValidGFElement
  , isValidPolynomial
  , polynomialsEqual
  , verifyGeneratorRoots
  
  -- * Bit Operations
  , gfMulSlow
  , highBit
  
  -- * Table Verification
  , verifyTables
  , allGFElements
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , map
  , otherwise
  , (==)
  , (/=)
  , (<)
  , (>)
  , (>=)
  , (<=)
  , (+)
  , (-)
  , (*)
  , (<>)
  , (&&)
  )

import Data.Array (length, index, replicate, snoc, foldl, reverse, take, drop, (..))
import Data.Array (zipWith, filter, mapWithIndex) as Array
import Data.EuclideanRing (mod)
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Data.Int.Bits (xor, shl, shr, and)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // gf element type
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A type-safe wrapper for GF(2^8) field elements.
-- |
-- | Guarantees the value is in range [0, 255].
-- | Using this type instead of bare Int provides:
-- | - Type safety (can't accidentally mix with regular integers)
-- | - Eq and Show instances for debugging
-- | - Explicit construction that validates range
newtype GFElement = GFElement Int

derive instance eqGFElement :: Eq GFElement

instance showGFElement :: Show GFElement where
  show (GFElement n) = "GF(" <> show n <> ")"

-- | Create a GFElement, clamping to valid range [0, 255]
mkGFElement :: Int -> GFElement
mkGFElement n
  | n < 0 = GFElement 0
  | n > 255 = GFElement (mod n 256)
  | otherwise = GFElement n

-- | Extract the raw Int value from a GFElement
gfElementValue :: GFElement -> Int
gfElementValue (GFElement n) = n

-- | Add two GFElements (type-safe wrapper around gfAdd)
gfElementAdd :: GFElement -> GFElement -> GFElement
gfElementAdd (GFElement a) (GFElement b) = GFElement (gfAdd a b)

-- | Multiply two GFElements (type-safe wrapper around gfMul)
gfElementMul :: GFElement -> GFElement -> GFElement
gfElementMul (GFElement a) (GFElement b) = GFElement (gfMul a b)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                      // galois field gf(2^8)
-- ═══════════════════════════════════════════════════════════════════════════════

-- | QR Code irreducible polynomial: x^8 + x^4 + x^3 + x^2 + 1 = 0x11D
-- |
-- | This polynomial is used for modular reduction in GF(2^8).
-- | When a multiplication result exceeds 255, we XOR with this polynomial.
qrPolynomial :: Int
qrPolynomial = 0x11D

-- | Primitive element α = 2
-- |
-- | The primitive element generates all non-zero elements of the field:
-- | α^0 = 1, α^1 = 2, α^2 = 4, ..., α^254 = 142, α^255 = 1
primitiveElement :: Int
primitiveElement = 2

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // lookup tables
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Exponentiation table: expTable[i] = α^i mod P(x)
-- |
-- | Pre-computed for efficiency. Index 0-254 gives powers of α.
-- | expTable[255] = expTable[0] = 1 for wraparound.
expTable :: Array Int
expTable = buildExpTable

-- | Logarithm table: logTable[x] = i where α^i = x
-- |
-- | Pre-computed inverse of expTable.
-- | logTable[0] is undefined (log of 0 doesn't exist).
-- | We store 0 as a sentinel.
logTable :: Array Int
logTable = buildLogTable

-- | Build the exponentiation table by computing successive powers of α
buildExpTable :: Array Int
buildExpTable = buildExpTableLoop 0 1 []
  where
    buildExpTableLoop :: Int -> Int -> Array Int -> Array Int
    buildExpTableLoop i val acc
      | i >= 256 = acc
      | otherwise =
          let
            -- Store current value
            newAcc = snoc acc val
            -- Compute next: val * α
            nextVal = val * primitiveElement
            -- Reduce modulo polynomial if >= 256
            reduced = if nextVal >= 256 
                      then xor nextVal qrPolynomial
                      else nextVal
          in
            buildExpTableLoop (i + 1) reduced newAcc

-- | Build the logarithm table from the exp table
buildLogTable :: Array Int
buildLogTable = buildLogTableLoop 0 (replicate 256 0)
  where
    buildLogTableLoop :: Int -> Array Int -> Array Int
    buildLogTableLoop i acc
      | i >= 255 = acc
      | otherwise =
          let
            expVal = fromMaybe 0 (index expTable i)
            -- Set logTable[expVal] = i
            newAcc = setAt expVal i acc
          in
            buildLogTableLoop (i + 1) newAcc
    
    setAt :: Int -> Int -> Array Int -> Array Int
    setAt idx val arr =
      Array.mapWithIndex (\i v -> if i == idx then val else v) arr

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // gf(2^8) arithmetic
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Addition in GF(2^8) — XOR operation
-- |
-- | In GF(2^8), addition is the XOR operation.
-- | Properties: associative, commutative, self-inverse (a + a = 0)
gfAdd :: Int -> Int -> Int
gfAdd a b = xor a b

-- | Subtraction in GF(2^8) — Same as addition (XOR)
-- |
-- | In GF(2), subtraction equals addition because -1 = 1.
gfSub :: Int -> Int -> Int
gfSub = gfAdd

-- | Multiplication in GF(2^8) using log/exp tables
-- |
-- | a * b = exp(log(a) + log(b)) mod 255
-- |
-- | Special cases:
-- | - 0 * anything = 0
-- | - anything * 0 = 0
gfMul :: Int -> Int -> Int
gfMul a b
  | a == 0 = 0
  | b == 0 = 0
  | otherwise =
      let
        logA = fromMaybe 0 (index logTable a)
        logB = fromMaybe 0 (index logTable b)
        logSum = mod (logA + logB) 255
      in
        fromMaybe 0 (index expTable logSum)

-- | Division in GF(2^8)
-- |
-- | a / b = a * b^(-1) = exp(log(a) - log(b)) mod 255
-- |
-- | Special case: 0 / anything = 0
-- | Undefined: anything / 0 (returns 0 as sentinel)
gfDiv :: Int -> Int -> Int
gfDiv a b
  | a == 0 = 0
  | b == 0 = 0  -- Undefined, return 0 as sentinel
  | otherwise =
      let
        logA = fromMaybe 0 (index logTable a)
        logB = fromMaybe 0 (index logTable b)
        -- Handle negative result: add 255 before mod
        logDiff = mod (logA - logB + 255) 255
      in
        fromMaybe 0 (index expTable logDiff)

-- | Exponentiation in GF(2^8)
-- |
-- | Compute a^n using the exp/log tables.
-- | a^n = exp(n * log(a)) mod 255
gfPow :: Int -> Int -> Int
gfPow a n
  | a == 0 = 0
  | n == 0 = 1
  | otherwise =
      let
        logA = fromMaybe 0 (index logTable a)
        logResult = mod (n * logA) 255
      in
        fromMaybe 0 (index expTable logResult)

-- | Multiplicative inverse in GF(2^8)
-- |
-- | a^(-1) = a^254 (since a^255 = 1 for all non-zero a)
-- | Also: exp(255 - log(a))
gfInverse :: Int -> Int
gfInverse a
  | a == 0 = 0  -- Undefined, return 0
  | otherwise =
      let
        logA = fromMaybe 0 (index logTable a)
        logInv = mod (255 - logA) 255
      in
        fromMaybe 0 (index expTable logInv)

-- | Direct access to exp table value
-- |
-- | Returns α^i where α is the primitive element.
gfExp :: Int -> Int
gfExp i = fromMaybe 0 (index expTable (mod i 255))

-- | Direct access to log table value
-- |
-- | Returns i where α^i = x. Returns 0 for x = 0 (undefined).
gfLog :: Int -> Int
gfLog x
  | x == 0 = 0
  | otherwise = fromMaybe 0 (index logTable x)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // polynomial operations
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Polynomial represented as array of coefficients.
-- |
-- | Index 0 is the constant term (x^0), index n is coefficient of x^n.
-- | Example: [1, 2, 3] represents 1 + 2x + 3x^2
type Polynomial = Array Int

-- | Add two polynomials (coefficient-wise XOR)
polyAdd :: Polynomial -> Polynomial -> Polynomial
polyAdd p1 p2 =
  let
    len1 = length p1
    len2 = length p2
    maxLen = if len1 > len2 then len1 else len2
    -- Pad shorter polynomial with zeros
    padded1 = padRight maxLen p1
    padded2 = padRight maxLen p2
  in
    Array.zipWith gfAdd padded1 padded2
  where
    padRight :: Int -> Array Int -> Array Int
    padRight targetLen arr =
      let
        currentLen = length arr
        padding = replicate (targetLen - currentLen) 0
      in
        arr <> padding

-- | Multiply polynomial by a scalar
polyMulScalar :: Int -> Polynomial -> Polynomial
polyMulScalar scalar poly = map (gfMul scalar) poly

-- | Multiply two polynomials
-- |
-- | Standard polynomial multiplication with coefficient addition via XOR.
polyMul :: Polynomial -> Polynomial -> Polynomial
polyMul p1 p2 =
  let
    len1 = length p1
    len2 = length p2
    resultLen = len1 + len2 - 1
    -- Initialize result with zeros
    initial = replicate resultLen 0
  in
    if len1 == 0 then []
    else if len2 == 0 then []
    else multiplyLoop 0 p1 p2 initial
  where
    multiplyLoop :: Int -> Polynomial -> Polynomial -> Polynomial -> Polynomial
    multiplyLoop i poly1 poly2 acc
      | i >= length poly1 = acc
      | otherwise =
          let
            coeff1 = fromMaybe 0 (index poly1 i)
            -- Multiply coeff1 by each coefficient in poly2, shifted by i
            newAcc = addShifted i coeff1 poly2 acc
          in
            multiplyLoop (i + 1) poly1 poly2 newAcc
    
    addShifted :: Int -> Int -> Polynomial -> Polynomial -> Polynomial
    addShifted shift scalar poly acc =
      addShiftedLoop 0 shift scalar poly acc
    
    addShiftedLoop :: Int -> Int -> Int -> Polynomial -> Polynomial -> Polynomial
    addShiftedLoop j shift scalar poly acc
      | j >= length poly = acc
      | otherwise =
          let
            coeff = fromMaybe 0 (index poly j)
            product = gfMul scalar coeff
            targetIdx = shift + j
            oldVal = fromMaybe 0 (index acc targetIdx)
            newVal = gfAdd oldVal product
            newAcc = setAt targetIdx newVal acc
          in
            addShiftedLoop (j + 1) shift scalar poly newAcc
    
    setAt :: Int -> Int -> Array Int -> Array Int
    setAt idx val arr =
      Array.mapWithIndex (\i v -> if i == idx then val else v) arr

-- | Polynomial division — returns remainder
-- |
-- | Divides dividend by divisor, returns the remainder.
-- | This is the core operation for Reed-Solomon encoding:
-- | the remainder after dividing (data * x^n) by the generator polynomial
-- | gives the error correction codewords.
polyDivide :: Polynomial -> Polynomial -> Polynomial
polyDivide dividend divisor =
  let
    dividendLen = length dividend
    divisorLen = length divisor
  in
    if divisorLen == 0 then dividend  -- Division by zero, return dividend
    else if dividendLen < divisorLen then dividend  -- Dividend smaller than divisor
    else divisionLoop (reverse dividend) (reverse divisor)
  where
    -- Work with highest-degree first (reversed arrays)
    divisionLoop :: Polynomial -> Polynomial -> Polynomial
    divisionLoop currentDiv divisorRev =
      let
        currentLen = length currentDiv
        divisorLen = length divisorRev
        leadDiv = fromMaybe 0 (index divisorRev 0)
      in
        if currentLen < divisorLen then reverse (trimLeadingZeros currentDiv)
        else if leadDiv == 0 then reverse (trimLeadingZeros currentDiv)
        else
          let
            leadCurrent = fromMaybe 0 (index currentDiv 0)
          in
            if leadCurrent == 0 then
              -- Leading coefficient is 0, drop it and continue
              divisionLoop (dropFirst currentDiv) divisorRev
            else
              let
                -- Compute quotient coefficient
                quotCoeff = gfDiv leadCurrent leadDiv
                -- Subtract quotCoeff * divisor from current
                subtracted = subtractScaledPoly quotCoeff divisorRev currentDiv
                -- Remove leading term (which should now be 0)
                reduced = dropFirst subtracted
              in
                divisionLoop reduced divisorRev
    
    dropFirst :: Array Int -> Array Int
    dropFirst arr = fromMaybe [] (Just (drop 1 arr))
    
    subtractScaledPoly :: Int -> Polynomial -> Polynomial -> Polynomial
    subtractScaledPoly scalar divisorRev currentDiv =
      Array.mapWithIndex (\i val ->
        if i < length divisorRev then
          gfSub val (gfMul scalar (fromMaybe 0 (index divisorRev i)))
        else val
      ) currentDiv
    
    trimLeadingZeros :: Polynomial -> Polynomial
    trimLeadingZeros arr =
      let
        -- Find first non-zero from the front
        trimmed = dropWhileZero arr
      in
        if length trimmed == 0 then [0] else trimmed
    
    dropWhileZero :: Array Int -> Array Int
    dropWhileZero arr = case index arr 0 of
      Nothing -> []
      Just 0 -> dropWhileZero (drop 1 arr)
      Just _ -> arr

-- | Evaluate polynomial at a point
-- |
-- | Uses Horner's method: p(x) = ((a_n * x + a_{n-1}) * x + ...) + a_0
polyEval :: Polynomial -> Int -> Int
polyEval poly x =
  let
    -- Reverse to process from highest to lowest degree
    reversed = reverse poly
  in
    foldl (\acc coeff -> gfAdd (gfMul acc x) coeff) 0 reversed

-- | Get polynomial degree (highest non-zero coefficient index)
polynomialDegree :: Polynomial -> Int
polynomialDegree poly =
  let
    -- Find last non-zero coefficient
    len = length poly
    findDegree i
      | i < 0 = 0
      | otherwise = case index poly i of
          Just 0 -> findDegree (i - 1)
          Just _ -> i
          Nothing -> findDegree (i - 1)
  in
    findDegree (len - 1)

-- | Show polynomial as string for debugging
showPolynomial :: Polynomial -> String
showPolynomial poly =
  let
    terms = Array.filter (\t -> t.coeff /= 0) (Array.mapWithIndex (\i c -> { idx: i, coeff: c }) poly)
  in
    if length terms == 0 then "0"
    else foldl (\acc t ->
      let
        term = if t.idx == 0 then show t.coeff
               else if t.idx == 1 then show t.coeff <> "x"
               else show t.coeff <> "x^" <> show t.idx
      in
        if acc == "" then term else acc <> " + " <> term
    ) "" terms

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // generator polynomials
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Compute generator polynomial for n error correction codewords.
-- |
-- | G(x) = (x - α^0)(x - α^1)(x - α^2)...(x - α^(n-1))
-- |      = (x + 1)(x + 2)(x + 4)...(x + α^(n-1))
-- |
-- | Note: In GF(2^8), subtraction = addition = XOR, so (x - α^i) = (x + α^i)
generatorPoly :: Int -> Polynomial
generatorPoly n
  | n <= 0 = [1]  -- Trivial case: G(x) = 1
  | otherwise = buildGenerator 0 [1]
  where
    buildGenerator :: Int -> Polynomial -> Polynomial
    buildGenerator i acc
      | i >= n = acc
      | otherwise =
          let
            -- Multiply by (x + α^i) = [α^i, 1] in our representation
            alphaI = gfExp i
            factor = [alphaI, 1]  -- α^i + 1*x
            newAcc = polyMul acc factor
          in
            buildGenerator (i + 1) newAcc

-- | Get generator polynomial coefficients (highest degree first).
-- |
-- | This is the format often used in documentation and lookup tables.
generatorPolyCoeffs :: Int -> Array Int
generatorPolyCoeffs n = reverse (generatorPoly n)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // error correction
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Compute error correction codewords for data.
-- |
-- | Algorithm:
-- | 1. Treat data codewords as polynomial coefficients
-- | 2. Multiply data polynomial by x^n (shift by n positions)
-- | 3. Divide by generator polynomial
-- | 4. The remainder coefficients are the EC codewords
-- |
-- | The EC codewords, when appended to the data, ensure that
-- | the complete codeword polynomial is divisible by the generator.
computeECCodewords :: Array Int -> Int -> Array Int
computeECCodewords dataCodewords numEC =
  let
    -- Create data polynomial (coefficients in standard order)
    -- The data represents coefficients from highest to lowest degree
    -- So reverse to get lowest-degree-first (polynomial format)
    dataPoly = reverse dataCodewords
    
    -- Multiply by x^numEC (prepend numEC zeros to shift polynomial up)
    -- If p(x) = a + bx + cx^2, then p(x) * x^2 = ax^2 + bx^3 + cx^4
    -- In array: [a, b, c] -> [0, 0, a, b, c]
    shiftedPoly = replicate numEC 0 <> dataPoly
    
    -- Get generator polynomial
    genPoly = generatorPoly numEC
    
    -- Divide to get remainder
    remainder = polyDivide shiftedPoly genPoly
    
    -- Pad to numEC length if necessary (remainder has degree < numEC)
    paddedRemainder = padToLength numEC remainder
  in
    -- Return in standard order (highest degree first)
    reverse paddedRemainder
  where
    padToLength :: Int -> Array Int -> Array Int
    padToLength targetLen arr =
      let
        currentLen = length arr
      in
        if currentLen >= targetLen then take targetLen arr
        else arr <> replicate (targetLen - currentLen) 0

-- | Compute EC codewords and return combined data + EC
computeECForData :: Array Int -> Int -> { dataCodewords :: Array Int, ecCodewords :: Array Int }
computeECForData dataCodewords numEC =
  { dataCodewords: dataCodewords
  , ecCodewords: computeECCodewords dataCodewords numEC
  }

-- | Get number of EC codewords needed for version and EC level
-- |
-- | This is a simplified version — full implementation would
-- | use lookup tables from the QR specification.
ecCodewordsNeeded :: Int -> Int -> Int
ecCodewordsNeeded version ecLevel =
  let
    -- Simplified formula based on version and EC level
    -- ecLevel: 0 = L, 1 = M, 2 = Q, 3 = H
    baseEC = case ecLevel of
      0 -> 7   -- L: ~7% recovery
      1 -> 10  -- M: ~15% recovery
      2 -> 13  -- Q: ~25% recovery
      _ -> 17  -- H: ~30% recovery
  in
    baseEC + (version - 1) * 2

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // validation
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Check if a value is a valid GF(2^8) element (0-255)
isValidGFElement :: Int -> Boolean
isValidGFElement n = n >= 0 && n <= 255

-- | Check if a polynomial has valid GF(2^8) coefficients
isValidPolynomial :: Polynomial -> Boolean
isValidPolynomial poly =
  let
    len = length poly
  in
    len > 0 && allValid 0 poly
  where
    allValid :: Int -> Polynomial -> Boolean
    allValid i arr
      | i >= length arr = true
      | otherwise = case index arr i of
          Nothing -> false
          Just coeff -> isValidGFElement coeff && allValid (i + 1) arr

-- | Check if two polynomials are equal
polynomialsEqual :: Polynomial -> Polynomial -> Boolean
polynomialsEqual p1 p2 =
  let
    len1 = length p1
    len2 = length p2
  in
    if len1 /= len2 then false
    else checkEqual 0 p1 p2
  where
    checkEqual :: Int -> Polynomial -> Polynomial -> Boolean
    checkEqual i a b
      | i >= length a = true
      | otherwise =
          let
            va = fromMaybe 0 (index a i)
            vb = fromMaybe 0 (index b i)
          in
            va == vb && checkEqual (i + 1) a b

-- | Verify that the generator polynomial has the correct roots.
-- |
-- | A valid generator polynomial G(x) for n EC codewords should satisfy:
-- | G(α^0) = G(α^1) = ... = G(α^(n-1)) = 0
-- |
-- | This is a validation/debugging function.
verifyGeneratorRoots :: Int -> Boolean
verifyGeneratorRoots n =
  let
    gen = generatorPoly n
  in
    if n <= 0 then true
    else checkRoots 0 n gen
  where
    checkRoots :: Int -> Int -> Polynomial -> Boolean
    checkRoots i numRoots poly
      | i >= numRoots = true
      | otherwise =
          let
            alphaI = gfExp i
            evalResult = polyEval poly alphaI
          in
            evalResult == 0 && checkRoots (i + 1) numRoots poly

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // bit operations
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Slow GF multiplication using shift-and-add (Russian peasant algorithm).
-- |
-- | This is the "textbook" implementation without lookup tables.
-- | Useful for verifying the table-based multiplication and for
-- | educational purposes.
-- |
-- | Algorithm:
-- | 1. If b's low bit is 1, add a to result
-- | 2. Shift a left, reduce if overflow
-- | 3. Shift b right
-- | 4. Repeat until b is 0
gfMulSlow :: Int -> Int -> Int
gfMulSlow a b = mulLoop a b 0
  where
    mulLoop :: Int -> Int -> Int -> Int
    mulLoop x y acc
      | y == 0 = acc
      | otherwise =
          let
            -- If low bit of y is set, XOR x into accumulator
            newAcc = if and y 1 == 1 then xor acc x else acc
            -- Shift x left (multiply by α)
            xShifted = shl x 1
            -- Reduce if overflow (high bit set)
            xReduced = if and xShifted 0x100 /= 0 
                       then xor xShifted qrPolynomial 
                       else xShifted
            -- Shift y right (divide by 2)
            yShifted = shr y 1
          in
            mulLoop xReduced yShifted newAcc

-- | Get the position of the highest set bit (0-indexed from LSB).
-- |
-- | Returns -1 for 0.
-- | Examples: highBit 1 = 0, highBit 2 = 1, highBit 128 = 7, highBit 256 = 8
highBit :: Int -> Int
highBit n = findHighBit n 0
  where
    findHighBit :: Int -> Int -> Int
    findHighBit x pos
      | x == 0 = pos - 1
      | otherwise = findHighBit (shr x 1) (pos + 1)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // table verification
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get all valid GF(2^8) elements (0-255).
-- |
-- | Useful for testing and iteration.
allGFElements :: Array Int
allGFElements = 0 .. 255

-- | Verify exp and log tables are consistent.
-- |
-- | For all i in 0..254: logTable[expTable[i]] == i
-- | For all x in 1..255: expTable[logTable[x]] == x
-- |
-- | This is useful for testing table construction.
verifyTables :: Boolean
verifyTables =
  let
    -- Check exp -> log -> exp cycle for all powers
    expLogValid = checkExpLog 0
    -- Check log -> exp cycle for all non-zero elements
    logExpValid = checkLogExp 1
  in
    expLogValid && logExpValid
  where
    checkExpLog :: Int -> Boolean
    checkExpLog i
      | i >= 255 = true
      | otherwise =
          let
            expVal = fromMaybe 0 (index expTable i)
            logVal = fromMaybe 0 (index logTable expVal)
          in
            logVal == i && checkExpLog (i + 1)
    
    checkLogExp :: Int -> Boolean
    checkLogExp x
      | x >= 256 = true
      | otherwise =
          let
            logVal = fromMaybe 0 (index logTable x)
            expVal = fromMaybe 0 (index expTable logVal)
          in
            expVal == x && checkLogExp (x + 1)
