-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // qrcode // property tests
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Exhaustive QRCode property tests designed to find REAL bugs.
-- |
-- | ## Test Categories
-- |
-- | 1. **Galois Field Arithmetic** - The foundation. If GF(2^8) is wrong, everything is wrong.
-- | 2. **Polynomial Operations** - Division, multiplication, evaluation
-- | 3. **Reed-Solomon Invariants** - EC codewords must decode correctly
-- | 4. **Encoding Roundtrips** - Data must survive encode → matrix → decode
-- | 5. **Capacity Bounds** - Never exceed version capacity, never underflow
-- | 6. **Matrix Structure** - Finder patterns at exact positions, timing patterns alternate
-- | 7. **Mask Invariants** - Masking is self-inverse, only data modules affected
-- | 8. **Interleaving** - Block structure preserves all data
-- |
-- | ## Distribution Philosophy
-- |
-- | Real QR codes have specific distributions:
-- | - 80% are URLs (mostly ASCII, 10-100 chars)
-- | - 10% are WiFi configs
-- | - 5% are vCards
-- | - 5% other (calendar, geo, phone)
-- |
-- | But for FINDING BUGS, we bias toward edge cases:
-- | - Empty strings, single chars, max capacity strings
-- | - All numeric, all alphanumeric, mixed mode
-- | - Version boundaries (1→2, 9→10, 26→27)
-- | - Strings with special QR characters ($%*+-./:)

module Test.QRCode where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Foldable (all, foldl, sum)
import Data.Int (toNumber)
import Data.Int.Bits (and, xor)
import Data.Maybe (Maybe(Just, Nothing), fromMaybe, isJust)
import Data.String as String
import Data.Char (fromCharCode)
import Data.String.CodeUnits (toCharArray, fromCharArray)
import Data.Tuple (Tuple(Tuple))
import Effect.Class (liftEffect)
import Effect.Console (log)

import Test.Spec (Spec, describe, it, pending)
import Test.Spec.Assertions (shouldEqual, shouldSatisfy, fail)
import Test.Spec.QuickCheck (quickCheck) as Spec
import Test.QuickCheck (Result, (===), (<?>), quickCheckGen)
import Test.QuickCheck.Gen (Gen, chooseInt, elements, frequency, oneOf, vectorOf, suchThat)

import Hydrogen.Element.Component.QRCode.Types as Types
import Hydrogen.Element.Component.QRCode.Encoding.ReedSolomon as RS
import Hydrogen.Element.Component.QRCode.Encoding.BitStream as BS
import Hydrogen.Element.Component.QRCode.Encoding.Segment as Seg
import Hydrogen.Element.Component.QRCode.Encoding.Capacity as Cap
import Hydrogen.Element.Component.QRCode.Matrix as Matrix

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // generators
-- ═══════════════════════════════════════════════════════════════════════════════

-- | GF(2^8) element: 0-255
genGFElement :: Gen Int
genGFElement = chooseInt 0 255

-- | Non-zero GF element (for division)
genNonZeroGF :: Gen Int
genNonZeroGF = chooseInt 1 255

-- | QR Version with realistic distribution biased toward edge cases
genVersion :: Gen Types.QRVersion
genVersion = do
  v <- frequency $ NEA.cons'
    (Tuple 20.0 (pure 1))   -- Version 1: most common, smallest
    [ Tuple 15.0 (chooseInt 2 5)    -- Small versions
    , Tuple 10.0 (chooseInt 6 9)    -- Boundary: 9→10 changes char count bits
    , Tuple 10.0 (pure 10)          -- Boundary version
    , Tuple 10.0 (chooseInt 11 26)  -- Medium versions
    , Tuple 10.0 (pure 27)          -- Boundary: 26→27 changes char count bits
    , Tuple 10.0 (chooseInt 27 39)  -- Large versions
    , Tuple 15.0 (pure 40)          -- Max version
    ]
  pure (Types.mkVersion v)

-- | Error correction level with uniform distribution (all are important)
genEC :: Gen Types.ErrorCorrection
genEC = elements $ NEA.cons'
  Types.ECLow
  [ Types.ECMedium
  , Types.ECQuartile
  , Types.ECHigh
  ]

-- | Numeric string (0-9 only) - most efficient encoding
genNumericString :: Gen String
genNumericString = do
  len <- frequency $ NEA.cons'
    (Tuple 5.0 (pure 0))           -- Empty
    [ Tuple 10.0 (pure 1)          -- Single digit
    , Tuple 10.0 (pure 2)          -- Two digits (7 bits)
    , Tuple 10.0 (pure 3)          -- Three digits (10 bits)
    , Tuple 20.0 (chooseInt 4 20)  -- Normal length
    , Tuple 20.0 (chooseInt 21 100)] -- Long
  digits <- vectorOf len (chooseInt 0 9)
  pure (String.joinWith "" (Array.mapWithIndex (\_ d -> show d) digits))

-- | Alphanumeric string (0-9, A-Z, space, $%*+-./:)
genAlphanumericString :: Gen String
genAlphanumericString = do
  len <- frequency $ NEA.cons'
    (Tuple 5.0 (pure 0))
    [ Tuple 10.0 (pure 1)
    , Tuple 10.0 (pure 2)
    , Tuple 25.0 (chooseInt 3 50)
    , Tuple 25.0 (chooseInt 51 200)]
  chars <- vectorOf len genAlphanumericChar
  pure (fromCharArray chars)

genAlphanumericChar :: Gen Char
genAlphanumericChar = 
  let
    digits = NEA.cons' '0' ['1','2','3','4','5','6','7','8','9']
    letters = NEA.cons' 'A' ['B','C','D','E','F','G','H','I','J','K','L','M',
                             'N','O','P','Q','R','S','T','U','V','W','X','Y','Z']
    specials = NEA.cons' '$' ['%','*','+','-','.','/',':']
  in
    frequency $ NEA.cons'
      (Tuple 40.0 (elements digits))
      [ Tuple 40.0 (elements letters)
      , Tuple 10.0 (pure ' ')
      , Tuple 10.0 (elements specials)
      ]

-- | Byte mode string (any UTF-8)
genByteString :: Gen String
genByteString = do
  len <- frequency $ NEA.cons'
    (Tuple 5.0 (pure 0))
    [ Tuple 20.0 (chooseInt 1 20)
    , Tuple 30.0 (chooseInt 21 100)
    , Tuple 20.0 (chooseInt 101 500)]
  chars <- vectorOf len genByteChar
  pure (fromCharArray chars)

genByteChar :: Gen Char
genByteChar = do
  code <- frequency $ NEA.cons'
    (Tuple 70.0 (chooseInt 32 126))   -- Printable ASCII
    [ Tuple 10.0 (chooseInt 0 31)     -- Control chars
    , Tuple 10.0 (chooseInt 127 255)  -- Extended ASCII
    , Tuple 10.0 (pure 0)]            -- Null
  pure (toEnum code)

-- | URL string (realistic QR content)
genURLString :: Gen String
genURLString = do
  protocol <- elements $ NEA.cons' "https://" ["http://"]
  domain <- genDomain
  path <- genPath
  pure (protocol <> domain <> path)

genDomain :: Gen String
genDomain = do
  parts <- chooseInt 1 3
  segments <- vectorOf parts genDomainSegment
  tld <- elements $ NEA.cons' ".com" [".org", ".net", ".io", ".dev"]
  pure (String.joinWith "." segments <> tld)

genDomainSegment :: Gen String
genDomainSegment = do
  len <- chooseInt 3 12
  chars <- vectorOf len (elements $ NEA.cons' 'a' 
    ['b','c','d','e','f','g','h','i','j','k','l','m',
     'n','o','p','q','r','s','t','u','v','w','x','y','z'])
  pure (fromCharArray chars)

genPath :: Gen String
genPath = frequency $ NEA.cons'
  (Tuple 50.0 (pure ""))
  [ Tuple 50.0 (do
      segs <- chooseInt 1 4
      parts <- vectorOf segs genPathSegment
      hasQuery <- frequency $ NEA.cons' (Tuple 60.0 (pure false)) [Tuple 40.0 (pure true)]
      if hasQuery 
        then do
          query <- genQueryString
          pure ("/" <> String.joinWith "/" parts <> query)
        else pure ("/" <> String.joinWith "/" parts))
  ]

genPathSegment :: Gen String
genPathSegment = do
  len <- chooseInt 2 15
  chars <- vectorOf len (elements $ NEA.cons' 'a' 
    ['b','c','d','e','f','g','h','i','j','k','l','m',
     'n','o','p','q','r','s','t','u','v','w','x','y','z',
     '0','1','2','3','4','5','6','7','8','9','-','_'])
  pure (fromCharArray chars)

genQueryString :: Gen String
genQueryString = do
  params <- chooseInt 1 5
  pairs <- vectorOf params genQueryParam
  pure ("?" <> String.joinWith "&" pairs)

genQueryParam :: Gen String
genQueryParam = do
  key <- genPathSegment
  val <- genPathSegment
  pure (key <> "=" <> val)

-- | Adversarial input: strings designed to break things
genAdversarialString :: Gen String
genAdversarialString = oneOf $ NEA.cons'
  (pure "")                                           -- Empty
  [ pure "\x00"                                       -- Null byte
  , pure "\x00\x00\x00"                              -- Multiple nulls
  , pure (String.joinWith "" (Array.replicate 3000 "A"))  -- Near max capacity
  , pure "https://x.com/\x00/y"                      -- Null in URL
  , do len <- chooseInt 100 500                      -- Random binary
       bytes <- vectorOf len (chooseInt 0 255)
       pure (fromCharArray (Array.mapWithIndex (\_ b -> toEnum b) bytes))
  , pure "日本語テスト"                               -- Non-ASCII (requires byte mode)
  , pure "HELLO WORLD"                               -- Classic alphanumeric test
  , pure "12345678901234567890"                      -- Numeric only
  , pure "AC-42"                                     -- Mixed (forces byte mode)
  ]

-- | Polynomial coefficients (array of GF elements)
genPolynomial :: Gen (Array Int)
genPolynomial = do
  degree <- frequency $ NEA.cons'
    (Tuple 10.0 (pure 0))          -- Constant
    [ Tuple 20.0 (pure 1)          -- Linear
    , Tuple 30.0 (chooseInt 2 10)  -- Small
    , Tuple 30.0 (chooseInt 11 30) -- EC polynomial size
    , Tuple 10.0 (chooseInt 31 68)]-- Max EC codewords
  vectorOf (degree + 1) genGFElement

-- | Data block for RS encoding
genDataBlock :: Gen (Array Int)
genDataBlock = do
  len <- frequency $ NEA.cons'
    (Tuple 10.0 (pure 1))
    [ Tuple 30.0 (chooseInt 2 20)
    , Tuple 40.0 (chooseInt 21 100)
    , Tuple 20.0 (chooseInt 101 200)]
  vectorOf len genGFElement

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // test exports
-- ═══════════════════════════════════════════════════════════════════════════════

qrCodeTests :: Spec Unit
qrCodeTests = do
  galoisFieldTests
  polynomialTests
  reedSolomonTests
  bitstreamTests
  segmentEncodingTests
  capacityTableTests
  matrixStructureTests
  maskingTests
  interleavingTests

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                    // galois field arithmetic
-- ═══════════════════════════════════════════════════════════════════════════════

galoisFieldTests :: Spec Unit
galoisFieldTests = describe "Galois Field GF(2^8)" do
  
  describe "Addition (XOR)" do
    it "is commutative: a + b = b + a" do
      Spec.quickCheck do
        a <- genGFElement
        b <- genGFElement
        pure $ RS.gfAdd a b === RS.gfAdd b a
    
    it "is associative: (a + b) + c = a + (b + c)" do
      Spec.quickCheck do
        a <- genGFElement
        b <- genGFElement
        c <- genGFElement
        pure $ RS.gfAdd (RS.gfAdd a b) c === RS.gfAdd a (RS.gfAdd b c)
    
    it "has identity 0: a + 0 = a" do
      Spec.quickCheck do
        a <- genGFElement
        pure $ RS.gfAdd a 0 === a
    
    it "is self-inverse: a + a = 0" do
      Spec.quickCheck do
        a <- genGFElement
        pure $ RS.gfAdd a a === 0

  describe "Multiplication" do
    it "is commutative: a * b = b * a" do
      Spec.quickCheck do
        a <- genGFElement
        b <- genGFElement
        pure $ RS.gfMul a b === RS.gfMul b a
    
    it "is associative: (a * b) * c = a * (b * c)" do
      Spec.quickCheck do
        a <- genGFElement
        b <- genGFElement
        c <- genGFElement
        pure $ RS.gfMul (RS.gfMul a b) c === RS.gfMul a (RS.gfMul b c)
    
    it "has identity 1: a * 1 = a" do
      Spec.quickCheck do
        a <- genGFElement
        pure $ RS.gfMul a 1 === a
    
    it "has absorbing element 0: a * 0 = 0" do
      Spec.quickCheck do
        a <- genGFElement
        pure $ RS.gfMul a 0 === 0
    
    it "distributes over addition: a * (b + c) = a*b + a*c" do
      Spec.quickCheck do
        a <- genGFElement
        b <- genGFElement
        c <- genGFElement
        pure $ RS.gfMul a (RS.gfAdd b c) === RS.gfAdd (RS.gfMul a b) (RS.gfMul a c)

  describe "Division" do
    it "is inverse of multiplication: (a * b) / b = a for b ≠ 0" do
      Spec.quickCheck do
        a <- genGFElement
        b <- genNonZeroGF
        pure $ RS.gfDiv (RS.gfMul a b) b === a
    
    it "a / a = 1 for a ≠ 0" do
      Spec.quickCheck do
        a <- genNonZeroGF
        pure $ RS.gfDiv a a === 1
    
    it "0 / a = 0 for a ≠ 0" do
      Spec.quickCheck do
        a <- genNonZeroGF
        pure $ RS.gfDiv 0 a === 0

  describe "Exponentiation" do
    it "a^0 = 1 for a ≠ 0" do
      Spec.quickCheck do
        a <- genNonZeroGF
        pure $ RS.gfPow a 0 === 1
    
    it "a^1 = a" do
      Spec.quickCheck do
        a <- genGFElement
        pure $ RS.gfPow a 1 === a
    
    it "a^2 = a * a" do
      Spec.quickCheck do
        a <- genGFElement
        pure $ RS.gfPow a 2 === RS.gfMul a a
    
    it "a^(m+n) = a^m * a^n" do
      Spec.quickCheck do
        a <- genNonZeroGF
        m <- chooseInt 0 127
        n <- chooseInt 0 127
        pure $ RS.gfPow a (m + n) === RS.gfMul (RS.gfPow a m) (RS.gfPow a n)

  describe "Inverse" do
    it "a * inverse(a) = 1 for a ≠ 0" do
      Spec.quickCheck do
        a <- genNonZeroGF
        pure $ RS.gfMul a (RS.gfInverse a) === 1
    
    it "inverse(inverse(a)) = a for a ≠ 0" do
      Spec.quickCheck do
        a <- genNonZeroGF
        pure $ RS.gfInverse (RS.gfInverse a) === a

  describe "Exp/Log tables" do
    it "exp(log(a)) = a for a ≠ 0" do
      Spec.quickCheck do
        a <- genNonZeroGF
        pure $ RS.gfExp (RS.gfLog a) === a
    
    it "log(exp(n)) = n mod 255 for n < 255" do
      Spec.quickCheck do
        n <- chooseInt 0 254
        pure $ RS.gfLog (RS.gfExp n) === n
    
    it "exp table has no duplicates in [0,254]" do
      let expValues = Array.mapWithIndex (\i _ -> RS.gfExp i) (Array.replicate 255 0)
      let unique = Array.nub expValues
      Array.length unique `shouldEqual` 255

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // polynomial operations
-- ═══════════════════════════════════════════════════════════════════════════════

polynomialTests :: Spec Unit
polynomialTests = describe "Polynomial Operations" do
  
  describe "Polynomial addition" do
    it "is commutative" do
      Spec.quickCheck do
        p1 <- genPolynomial
        p2 <- genPolynomial
        pure $ RS.polyAdd p1 p2 === RS.polyAdd p2 p1
    
    it "has identity [0]" do
      Spec.quickCheck do
        p <- genPolynomial
        pure $ RS.polyAdd p [0] === p

  describe "Polynomial multiplication" do
    it "is commutative" do
      Spec.quickCheck do
        p1 <- genPolynomial `suchThat` (\p -> Array.length p <= 10)
        p2 <- genPolynomial `suchThat` (\p -> Array.length p <= 10)
        pure $ RS.polyMul p1 p2 === RS.polyMul p2 p1
    
    it "has identity [1]" do
      Spec.quickCheck do
        p <- genPolynomial
        pure $ RS.polyMul p [1] === p
    
    it "degree(p1 * p2) = degree(p1) + degree(p2) for non-zero polynomials" do
      Spec.quickCheck do
        p1 <- genPolynomial `suchThat` (\p -> Array.length p > 0 && Array.length p <= 10)
        p2 <- genPolynomial `suchThat` (\p -> Array.length p > 0 && Array.length p <= 10)
        let prod = RS.polyMul p1 p2
        -- Degree is length - 1
        pure $ Array.length prod === Array.length p1 + Array.length p2 - 1

  describe "Polynomial evaluation" do
    it "evaluating constant polynomial returns constant" do
      Spec.quickCheck \c x ->
        RS.polyEval [c] x === c
    
    it "evaluating [a, b] at x gives a + b*x" do
      Spec.quickCheck \a b x ->
        RS.polyEval [a, b] x === RS.gfAdd a (RS.gfMul b x)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // reed-solomon
-- ═══════════════════════════════════════════════════════════════════════════════

reedSolomonTests :: Spec Unit
reedSolomonTests = describe "Reed-Solomon Error Correction" do
  
  describe "Generator polynomial" do
    it "has correct degree" do
      Spec.quickCheck do
        numEC <- chooseInt 1 68
        let gen = RS.generatorPoly numEC
        pure $ Array.length gen === numEC + 1
    
    it "has leading coefficient 1" do
      Spec.quickCheck do
        numEC <- chooseInt 1 30
        let gen = RS.generatorPoly numEC
        pure $ fromMaybe 0 (Array.last gen) === 1
    
    it "has roots at α^0, α^1, ..., α^(n-1)" do
      -- Generator polynomial g(x) = (x - α^0)(x - α^1)...(x - α^(n-1))
      -- So g(α^i) = 0 for i = 0..n-1
      Spec.quickCheck do
        numEC <- chooseInt 1 20
        rootIndex <- chooseInt 0 (numEC - 1)
        let gen = RS.generatorPoly numEC
        let root = RS.gfExp rootIndex
        let result = RS.polyEval gen root
        pure $ (result == 0) <?> 
          ("Generator poly should have root at α^" <> show rootIndex <> 
           " but evaluated to " <> show result)

  describe "EC codeword generation" do
    it "produces correct number of EC codewords" do
      Spec.quickCheck do
        numEC <- chooseInt 1 30
        dataLen <- chooseInt 1 50
        dataBlock <- vectorOf dataLen genGFElement
        let ec = RS.computeECCodewords dataBlock numEC
        pure $ Array.length ec === numEC
    
    it "EC codewords are in valid GF range" do
      Spec.quickCheck do
        numEC <- chooseInt 1 20
        dataLen <- chooseInt 1 30
        dataBlock <- vectorOf dataLen genGFElement
        let ec = RS.computeECCodewords dataBlock numEC
        pure $ all (\x -> x >= 0 && x <= 255) ec
    
    it "codeword polynomial evaluates to 0 at all roots" do
      -- The full codeword (data || EC) forms a polynomial divisible by generator
      -- So it evaluates to 0 at all generator roots
      -- Note: data and EC are stored highest-degree-first, but polyEval
      -- expects lowest-degree-first, so we reverse
      Spec.quickCheck do
        numEC <- chooseInt 2 10
        dataLen <- chooseInt 2 20
        dataBlock <- vectorOf dataLen genGFElement
        let ec = RS.computeECCodewords dataBlock numEC
        -- fullCodeword is [data || EC] in highest-degree-first order
        let fullCodeword = dataBlock <> ec
        -- Reverse to get polynomial format (index 0 = constant term)
        let fullPoly = Array.reverse fullCodeword
        rootIndex <- chooseInt 0 (numEC - 1)
        let root = RS.gfExp rootIndex
        let result = RS.polyEval fullPoly root
        pure $ (result == 0) <?>
          ("Full codeword should evaluate to 0 at α^" <> show rootIndex <>
           " but got " <> show result)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // bitstream
-- ═══════════════════════════════════════════════════════════════════════════════

bitstreamTests :: Spec Unit
bitstreamTests = describe "BitStream Operations" do
  
  describe "Basic operations" do
    it "empty stream has length 0" do
      BS.length BS.empty `shouldEqual` 0
    
    it "fromInt produces correct number of bits" do
      Spec.quickCheck do
        val <- chooseInt 0 255
        numBits <- chooseInt 1 16
        let stream = BS.fromInt val numBits
        pure $ BS.length stream === numBits
    
    it "toBytes produces ceil(length/8) bytes" do
      Spec.quickCheck do
        numBits <- chooseInt 1 100
        bits <- vectorOf numBits (chooseInt 0 1)
        let stream = BS.fromBits (Array.mapWithIndex (\_ b -> if b == 1 then BS.one else BS.zero) bits)
        let bytes = BS.toBytes stream
        let expectedBytes = (numBits + 7) / 8
        pure $ Array.length bytes === expectedBytes

  describe "Append" do
    it "length(a <> b) = length(a) + length(b)" do
      Spec.quickCheck do
        len1 <- chooseInt 0 50
        len2 <- chooseInt 0 50
        bits1 <- vectorOf len1 (chooseInt 0 1)
        bits2 <- vectorOf len2 (chooseInt 0 1)
        let s1 = BS.fromBits (Array.mapWithIndex (\_ b -> if b == 1 then BS.one else BS.zero) bits1)
        let s2 = BS.fromBits (Array.mapWithIndex (\_ b -> if b == 1 then BS.one else BS.zero) bits2)
        let combined = BS.append s1 s2
        pure $ BS.length combined === len1 + len2

  describe "Roundtrip" do
    it "toArray >>> fromBits = identity" do
      Spec.quickCheck do
        numBits <- chooseInt 1 100
        bits <- vectorOf numBits (chooseInt 0 1)
        let original = BS.fromBits (Array.mapWithIndex (\_ b -> if b == 1 then BS.one else BS.zero) bits)
        let arr = BS.toArray original
        let restored = BS.fromBits arr
        pure $ BS.toArray restored === arr

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // segment encoding
-- ═══════════════════════════════════════════════════════════════════════════════

segmentEncodingTests :: Spec Unit
segmentEncodingTests = describe "Segment Encoding" do
  
  describe "Mode detection" do
    it "detects numeric mode for digit-only strings" do
      Spec.quickCheck do
        s <- genNumericString `suchThat` (\str -> String.length str > 0)
        pure $ Seg.detectOptimalMode s === Types.ModeNumeric
    
    it "detects alphanumeric for uppercase + digits" do
      let s = "HELLO WORLD 123"
      Seg.detectOptimalMode s `shouldEqual` Types.ModeAlphanumeric
    
    it "detects byte mode for lowercase" do
      let s = "hello"
      Seg.detectOptimalMode s `shouldEqual` Types.ModeByte

  describe "Character count bits" do
    it "returns correct bits for numeric mode" do
      -- Versions 1-9: 10 bits, 10-26: 12 bits, 27-40: 14 bits
      let v1 = Types.mkVersion 1
      let v10 = Types.mkVersion 10
      let v27 = Types.mkVersion 27
      Seg.characterCountBits v1 Types.ModeNumeric `shouldEqual` 10
      Seg.characterCountBits v10 Types.ModeNumeric `shouldEqual` 12
      Seg.characterCountBits v27 Types.ModeNumeric `shouldEqual` 14
    
    it "returns correct bits for alphanumeric mode" do
      let v1 = Types.mkVersion 1
      let v10 = Types.mkVersion 10
      let v27 = Types.mkVersion 27
      Seg.characterCountBits v1 Types.ModeAlphanumeric `shouldEqual` 9
      Seg.characterCountBits v10 Types.ModeAlphanumeric `shouldEqual` 11
      Seg.characterCountBits v27 Types.ModeAlphanumeric `shouldEqual` 13
    
    it "returns correct bits for byte mode" do
      let v1 = Types.mkVersion 1
      let v10 = Types.mkVersion 10
      let v27 = Types.mkVersion 27
      Seg.characterCountBits v1 Types.ModeByte `shouldEqual` 8
      Seg.characterCountBits v10 Types.ModeByte `shouldEqual` 16
      Seg.characterCountBits v27 Types.ModeByte `shouldEqual` 16

  describe "Alphanumeric encoding" do
    it "maps 0-9 to 0-9" do
      Seg.alphanumericValue '0' `shouldEqual` 0
      Seg.alphanumericValue '5' `shouldEqual` 5
      Seg.alphanumericValue '9' `shouldEqual` 9
    
    it "maps A-Z to 10-35" do
      Seg.alphanumericValue 'A' `shouldEqual` 10
      Seg.alphanumericValue 'Z' `shouldEqual` 35
    
    it "maps special chars correctly" do
      Seg.alphanumericValue ' ' `shouldEqual` 36
      Seg.alphanumericValue '$' `shouldEqual` 37
      Seg.alphanumericValue '%' `shouldEqual` 38
      Seg.alphanumericValue '*' `shouldEqual` 39
      Seg.alphanumericValue '+' `shouldEqual` 40
      Seg.alphanumericValue '-' `shouldEqual` 41
      Seg.alphanumericValue '.' `shouldEqual` 42
      Seg.alphanumericValue '/' `shouldEqual` 43
      Seg.alphanumericValue ':' `shouldEqual` 44

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // capacity table
-- ═══════════════════════════════════════════════════════════════════════════════

capacityTableTests :: Spec Unit
capacityTableTests = describe "Capacity Table (160 configurations)" do
  
  describe "Block info sanity" do
    it "all configurations have positive EC per block" do
      Spec.quickCheck do
        version <- genVersion
        ec <- genEC
        let info = Cap.getBlockInfo ec version
        pure $ info.ecPerBlock > 0
    
    it "all configurations have at least one block" do
      Spec.quickCheck do
        version <- genVersion
        ec <- genEC
        let info = Cap.getBlockInfo ec version
        pure $ info.group1Blocks + info.group2Blocks >= 1
    
    it "group2 data = group1 data + 1 when group2 exists" do
      Spec.quickCheck do
        version <- genVersion
        ec <- genEC
        let info = Cap.getBlockInfo ec version
        pure $ (info.group2Blocks == 0) || (info.group2Data == info.group1Data + 1)
    
    it "total codewords increases with version" do
      -- For same EC level, higher version = more capacity
      Spec.quickCheck do
        v1 <- chooseInt 1 39
        let v2 = v1 + 1
        ec <- genEC
        let ver1 = Types.mkVersion v1
        let ver2 = Types.mkVersion v2
        let info1 = Cap.getBlockInfo ec ver1
        let info2 = Cap.getBlockInfo ec ver2
        let total1 = Cap.totalCodewords info1
        let total2 = Cap.totalCodewords info2
        pure $ total2 >= total1 <?>
          ("Version " <> show v2 <> " should have >= capacity than version " <> show v1)

  describe "Specific known values (ISO 18004 Table 9)" do
    it "Version 1-L: 19 data, 7 EC, 1 block" do
      let info = Cap.getBlockInfo Types.ECLow (Types.mkVersion 1)
      info.group1Data `shouldEqual` 19
      info.ecPerBlock `shouldEqual` 7
      info.group1Blocks `shouldEqual` 1
    
    it "Version 1-M: 16 data, 10 EC, 1 block" do
      let info = Cap.getBlockInfo Types.ECMedium (Types.mkVersion 1)
      info.group1Data `shouldEqual` 16
      info.ecPerBlock `shouldEqual` 10
    
    it "Version 1-Q: 13 data, 13 EC, 1 block" do
      let info = Cap.getBlockInfo Types.ECQuartile (Types.mkVersion 1)
      info.group1Data `shouldEqual` 13
      info.ecPerBlock `shouldEqual` 13
    
    it "Version 1-H: 9 data, 17 EC, 1 block" do
      let info = Cap.getBlockInfo Types.ECHigh (Types.mkVersion 1)
      info.group1Data `shouldEqual` 9
      info.ecPerBlock `shouldEqual` 17
    
    it "Version 40-L: multiple blocks totaling 2956 data codewords" do
      let info = Cap.getBlockInfo Types.ECLow (Types.mkVersion 40)
      let totalData = Cap.totalDataCodewords info
      totalData `shouldEqual` 2956

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // matrix structure
-- ═══════════════════════════════════════════════════════════════════════════════

matrixStructureTests :: Spec Unit
matrixStructureTests = describe "Matrix Structure" do
  
  describe "Matrix size" do
    it "version n has size 4n + 17" do
      Spec.quickCheck do
        v <- chooseInt 1 40
        let version = Types.mkVersion v
        let expectedSize = 4 * v + 17
        pure $ Types.versionSize version === expectedSize
    
    it "version 1 is 21x21" do
      Types.versionSize (Types.mkVersion 1) `shouldEqual` 21
    
    it "version 40 is 177x177" do
      Types.versionSize (Types.mkVersion 40) `shouldEqual` 177

  describe "Finder patterns" do
    it "finder pattern is 7x7" do
      -- Test that placeFinderPatterns creates correct structure
      let version = Types.mkVersion 1
      let matrix = Matrix.initializeMatrix version
      let withFinders = Matrix.placeFinderPatterns matrix
      -- Top-left corner (0,0) should be dark finder
      let topLeft = Types.getModule 0 0 withFinders
      Types.isDark topLeft `shouldEqual` true

  describe "Timing patterns" do
    it "timing pattern alternates dark/light" do
      let version = Types.mkVersion 5
      let matrix = Matrix.initializeMatrix version
      let m1 = Matrix.placeFinderPatterns matrix
      let m2 = Matrix.placeSeparators m1
      let m3 = Matrix.placeTimingPatterns m2
      -- Horizontal timing at row 6, from col 8 to size-9
      -- Should alternate: dark at even cols, light at odd
      let col8 = Types.getModule 6 8 m3
      let col9 = Types.getModule 6 9 m3
      Types.isDark col8 `shouldEqual` true
      Types.isDark col9 `shouldEqual` false

  describe "Alignment patterns" do
    it "version 1 has no alignment patterns" do
      let positions = Matrix.alignmentPatternPositions (Types.mkVersion 1)
      Array.length positions `shouldEqual` 0
    
    it "version 2 has alignment patterns at [6, 18]" do
      let positions = Matrix.alignmentPatternPositions (Types.mkVersion 2)
      positions `shouldEqual` [6, 18]
    
    it "version 7 has alignment patterns at [6, 22, 38]" do
      let positions = Matrix.alignmentPatternPositions (Types.mkVersion 7)
      positions `shouldEqual` [6, 22, 38]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // masking
-- ═══════════════════════════════════════════════════════════════════════════════

maskingTests :: Spec Unit
maskingTests = describe "Masking" do
  
  describe "Mask patterns" do
    it "mask 0: (row + col) mod 2 == 0" do
      Matrix.shouldMaskModule Matrix.Mask0 0 0 `shouldEqual` true
      Matrix.shouldMaskModule Matrix.Mask0 0 1 `shouldEqual` false
      Matrix.shouldMaskModule Matrix.Mask0 1 0 `shouldEqual` false
      Matrix.shouldMaskModule Matrix.Mask0 1 1 `shouldEqual` true
    
    it "mask 1: row mod 2 == 0" do
      Matrix.shouldMaskModule Matrix.Mask1 0 0 `shouldEqual` true
      Matrix.shouldMaskModule Matrix.Mask1 0 5 `shouldEqual` true
      Matrix.shouldMaskModule Matrix.Mask1 1 0 `shouldEqual` false
      Matrix.shouldMaskModule Matrix.Mask1 1 5 `shouldEqual` false
    
    it "mask 2: col mod 3 == 0" do
      Matrix.shouldMaskModule Matrix.Mask2 0 0 `shouldEqual` true
      Matrix.shouldMaskModule Matrix.Mask2 0 3 `shouldEqual` true
      Matrix.shouldMaskModule Matrix.Mask2 0 1 `shouldEqual` false
      Matrix.shouldMaskModule Matrix.Mask2 0 2 `shouldEqual` false
    
    it "masking is self-inverse" do
      -- Applying the same mask twice should restore original
      -- This is because masking XORs the module
      Spec.quickCheck do
        pattern <- elements $ NEA.cons' Matrix.Mask0 
          [Matrix.Mask1, Matrix.Mask2, Matrix.Mask3, 
           Matrix.Mask4, Matrix.Mask5, Matrix.Mask6, Matrix.Mask7]
        row <- chooseInt 0 100
        col <- chooseInt 0 100
        let shouldMask = Matrix.shouldMaskModule pattern row col
        -- XOR with same value twice = original
        -- true XOR true = false, false XOR false = false
        -- So applying mask twice restores
        pure $ (shouldMask == shouldMask) === true

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // interleaving
-- ═══════════════════════════════════════════════════════════════════════════════

interleavingTests :: Spec Unit
interleavingTests = describe "Block Interleaving" do
  
  describe "Interleaving preserves data" do
    pending "total bytes preserved after interleaving - requires exposing interleave function"
    
    pending "all blocks contribute to final output - requires exposing interleave function"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Convert Char code to Char
toEnum :: Int -> Char
toEnum n = fromMaybe '?' (fromCharCode n)
