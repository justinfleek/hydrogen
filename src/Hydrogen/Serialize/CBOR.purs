-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                             // hydrogen // serialize // cbor
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | CBOR Serialization — Pure PureScript implementation of RFC 8949.
-- |
-- | CBOR (Concise Binary Object Representation) is a binary format that's:
-- | - More compact than JSON
-- | - Self-describing (schema embedded in data)
-- | - Language-agnostic (Haskell, Rust, C all speak it)
-- |
-- | ## Why Pure Implementation?
-- |
-- | No FFI. No npm. No JavaScript. Just bytes.
-- |
-- | The wire format is the contract. PureScript encodes to CBOR bytes,
-- | Haskell decodes from CBOR bytes. The RFC is the shared specification.
-- | Both implementations are independent but interoperable.
-- |
-- | ## CBOR Wire Format (RFC 8949)
-- |
-- | Each value starts with a byte encoding:
-- | - Bits 7-5: Major type (0-7)
-- | - Bits 4-0: Additional info
-- |
-- | Major types:
-- | - 0: Unsigned integer
-- | - 1: Negative integer
-- | - 2: Byte string
-- | - 3: Text string (UTF-8)
-- | - 4: Array
-- | - 5: Map
-- | - 6: Tagged value
-- | - 7: Simple/float
-- |
-- | Additional info:
-- | - 0-23: Immediate value
-- | - 24: Next byte is value
-- | - 25: Next 2 bytes (big-endian)
-- | - 26: Next 4 bytes
-- | - 27: Next 8 bytes
-- | - 31: Indefinite length (for arrays/maps)

module Hydrogen.Serialize.CBOR
  ( -- * CBOR Value Type
    CBORValue
      ( CBORUInt
      , CBORNInt
      , CBORBytes
      , CBORText
      , CBORArray
      , CBORMap
      , CBORBool
      , CBORNull
      , CBORFloat32
      , CBORFloat64
      )
  
  -- * Encoding Typeclass
  , class CBOREncode
  , encode
  
  -- * Decoding Typeclass
  , class CBORDecode
  , decode
  
  -- * Byte Array
  , Bytes
  , emptyBytes
  , singleByte
  , appendBytes
  , bytesLength
  , bytesToArray
  
  -- * Serialization
  , serialize
  , serializeToArray
  
  -- * Primitive Encoders
  , encodeInt
  , encodeNumber
  , encodeString
  , encodeBool
  , encodeNull
  
  -- * Compound Encoders
  , encodeArray
  , encodeMap
  , encodePair
  
  -- * Map Field Decoders
  , decodeField
  , decodeFieldMaybe
  , lookupField
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , compare
  , map
  , otherwise
  , negate
  , (+)
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
  , (||)
  , (<>)
  , ($)
  )

import Data.Array as Array
import Data.Either (Either(Left, Right))
import Data.Enum (fromEnum)
import Data.Foldable (foldl)
import Data.Int (toNumber, floor)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Int.Bits (shr, shl, and)


import Data.Number (abs, log, ln2)
import Data.String as String
import Data.Tuple (Tuple(Tuple))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // bytes
-- ═════════════════════════════════════════════════════════════════════════════

-- | A sequence of bytes (0-255 values).
-- |
-- | This is pure data — an array of integers in the byte range.
-- | At the boundary (when writing to a pipe/file), these become actual bytes.
newtype Bytes = Bytes (Array Int)

derive instance eqBytes :: Eq Bytes

instance showBytes :: Show Bytes where
  show (Bytes arr) = "(Bytes [" <> showHex arr <> "])"
    where
      showHex :: Array Int -> String
      showHex a = String.joinWith " " (map toHex a)
      
      toHex :: Int -> String
      toHex n = 
        let hi = hexDigit (shr n 4)
            lo = hexDigit (and n 15)
        in hi <> lo
      
      hexDigit :: Int -> String
      hexDigit 0 = "0"
      hexDigit 1 = "1"
      hexDigit 2 = "2"
      hexDigit 3 = "3"
      hexDigit 4 = "4"
      hexDigit 5 = "5"
      hexDigit 6 = "6"
      hexDigit 7 = "7"
      hexDigit 8 = "8"
      hexDigit 9 = "9"
      hexDigit 10 = "a"
      hexDigit 11 = "b"
      hexDigit 12 = "c"
      hexDigit 13 = "d"
      hexDigit 14 = "e"
      hexDigit _ = "f"

-- | Empty byte sequence.
emptyBytes :: Bytes
emptyBytes = Bytes []

-- | Single byte.
singleByte :: Int -> Bytes
singleByte b = Bytes [and b 255]

-- | Append two byte sequences.
appendBytes :: Bytes -> Bytes -> Bytes
appendBytes (Bytes a) (Bytes b) = Bytes (a <> b)

-- | Length of byte sequence.
bytesLength :: Bytes -> Int
bytesLength (Bytes arr) = Array.length arr

-- | Convert to raw array of ints.
bytesToArray :: Bytes -> Array Int
bytesToArray (Bytes arr) = arr

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // cbor // value
-- ═════════════════════════════════════════════════════════════════════════════

-- | CBOR value representation (RFC 8949 data model).
-- |
-- | This is the intermediate representation before encoding to bytes.
data CBORValue
  = CBORUInt Int              -- ^ Unsigned integer (major type 0)
  | CBORNInt Int              -- ^ Negative integer as -(1+n) (major type 1)
  | CBORBytes Bytes           -- ^ Byte string (major type 2)
  | CBORText String           -- ^ UTF-8 text string (major type 3)
  | CBORArray (Array CBORValue)  -- ^ Array (major type 4)
  | CBORMap (Array (Tuple CBORValue CBORValue))  -- ^ Map (major type 5)
  | CBORBool Boolean          -- ^ True/false (major type 7, values 20/21)
  | CBORNull                  -- ^ Null (major type 7, value 22)
  | CBORFloat32 Number        -- ^ 32-bit float (major type 7, value 26)
  | CBORFloat64 Number        -- ^ 64-bit float (major type 7, value 27)

derive instance eqCBORValue :: Eq CBORValue

instance showCBORValue :: Show CBORValue where
  show (CBORUInt n) = "(CBORUInt " <> show n <> ")"
  show (CBORNInt n) = "(CBORNInt " <> show n <> ")"
  show (CBORBytes b) = "(CBORBytes " <> show b <> ")"
  show (CBORText s) = "(CBORText " <> show s <> ")"
  show (CBORArray arr) = "(CBORArray " <> show arr <> ")"
  show (CBORMap pairs) = "(CBORMap " <> show pairs <> ")"
  show (CBORBool b) = "(CBORBool " <> show b <> ")"
  show CBORNull = "CBORNull"
  show (CBORFloat32 n) = "(CBORFloat32 " <> show n <> ")"
  show (CBORFloat64 n) = "(CBORFloat64 " <> show n <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // encode // class
-- ═════════════════════════════════════════════════════════════════════════════

-- | Typeclass for encoding values to CBOR.
class CBOREncode a where
  encode :: a -> CBORValue

-- | Typeclass for decoding values from CBOR.
class CBORDecode a where
  decode :: CBORValue -> Either String a

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // primitive // encoders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Encode an integer (positive or negative).
encodeInt :: Int -> CBORValue
encodeInt n
  | n >= 0 = CBORUInt n
  | otherwise = CBORNInt (negate n - 1)

-- | Encode a floating point number.
encodeNumber :: Number -> CBORValue
encodeNumber = CBORFloat64

-- | Encode a UTF-8 string.
encodeString :: String -> CBORValue
encodeString = CBORText

-- | Encode a boolean.
encodeBool :: Boolean -> CBORValue
encodeBool = CBORBool

-- | Encode null.
encodeNull :: CBORValue
encodeNull = CBORNull

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // compound // encoders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Encode an array.
encodeArray :: forall a. CBOREncode a => Array a -> CBORValue
encodeArray arr = CBORArray (map encode arr)

-- | Encode a map with string keys.
-- |
-- | Convenience function: takes string keys, produces CBOR map.
encodeMap :: Array (Tuple String CBORValue) -> CBORValue
encodeMap pairs = CBORMap (map toKV pairs)
  where
    toKV :: Tuple String CBORValue -> Tuple CBORValue CBORValue
    toKV (Tuple k v) = Tuple (CBORText k) v

-- | Create a key-value pair for a map.
encodePair :: forall a. CBOREncode a => String -> a -> Tuple String CBORValue
encodePair key value = Tuple key (encode value)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // primitive // instances
-- ═════════════════════════════════════════════════════════════════════════════

instance cborEncodeInt :: CBOREncode Int where
  encode = encodeInt

instance cborEncodeNumber :: CBOREncode Number where
  encode = encodeNumber

instance cborEncodeString :: CBOREncode String where
  encode = encodeString

instance cborEncodeBool :: CBOREncode Boolean where
  encode = encodeBool

instance cborEncodeArray :: CBOREncode a => CBOREncode (Array a) where
  encode = encodeArray

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // traverse // either
-- ═════════════════════════════════════════════════════════════════════════════

-- | Traverse an array with an Either-returning function.
-- |
-- | Returns Right with all results if all succeed, Left with first error if any fail.
traverseEither :: forall a b. (a -> Either String b) -> Array a -> Either String (Array b)
traverseEither f arr = foldl go (Right []) arr
  where
  go :: Either String (Array b) -> a -> Either String (Array b)
  go (Left err) _ = Left err
  go (Right acc) x = case f x of
    Left err -> Left err
    Right y -> Right (acc <> [y])

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // primitive // decoders
-- ═════════════════════════════════════════════════════════════════════════════

instance cborDecodeInt :: CBORDecode Int where
  decode (CBORUInt n) = Right n
  decode (CBORNInt n) = Right (negate (n + 1))
  decode _ = Left "Expected integer"

instance cborDecodeNumber :: CBORDecode Number where
  decode (CBORFloat32 n) = Right n
  decode (CBORFloat64 n) = Right n
  decode (CBORUInt n) = Right (toNumber n)
  decode (CBORNInt n) = Right (toNumber (negate (n + 1)))
  decode _ = Left "Expected number"

instance cborDecodeString :: CBORDecode String where
  decode (CBORText s) = Right s
  decode _ = Left "Expected string"

instance cborDecodeBool :: CBORDecode Boolean where
  decode (CBORBool b) = Right b
  decode _ = Left "Expected boolean"

instance cborDecodeArray :: CBORDecode a => CBORDecode (Array a) where
  decode (CBORArray arr) = traverseEither decode arr
  decode _ = Left "Expected array"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // map // field // decoders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Look up a field in a CBOR map by string key.
-- |
-- | Returns Nothing if the key is not present.
lookupField :: String -> CBORValue -> Maybe CBORValue
lookupField key (CBORMap pairs) = findInPairs pairs
  where
  findInPairs :: Array (Tuple CBORValue CBORValue) -> Maybe CBORValue
  findInPairs arr = case Array.uncons arr of
    Nothing -> Nothing
    Just { head: Tuple (CBORText k) v, tail } ->
      if k == key then Just v else findInPairs tail
    Just { head: _, tail } -> findInPairs tail
lookupField _ _ = Nothing

-- | Decode a required field from a CBOR map.
-- |
-- | Returns Left if the field is missing or cannot be decoded.
decodeField :: forall a. CBORDecode a => String -> CBORValue -> Either String a
decodeField key cbor = case lookupField key cbor of
  Nothing -> Left ("Missing required field: " <> key)
  Just v -> decode v

-- | Decode an optional field from a CBOR map.
-- |
-- | Returns Right Nothing if the field is missing, Right (Just a) if present
-- | and decodable, Left if present but not decodable.
decodeFieldMaybe :: forall a. CBORDecode a => String -> CBORValue -> Either String (Maybe a)
decodeFieldMaybe key cbor = case lookupField key cbor of
  Nothing -> Right Nothing
  Just v -> case decode v of
    Left err -> Left ("Field '" <> key <> "': " <> err)
    Right a -> Right (Just a)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize a CBORValue to bytes (the actual wire format).
serialize :: CBORValue -> Bytes
serialize value = case value of
  CBORUInt n -> serializeUInt 0 n
  CBORNInt n -> serializeUInt 1 n
  CBORBytes (Bytes arr) -> serializeUInt 2 (Array.length arr) `appendBytes` Bytes arr
  CBORText s -> 
    let utf8 = stringToUTF8 s
    in serializeUInt 3 (Array.length utf8) `appendBytes` Bytes utf8
  CBORArray arr ->
    let header = serializeUInt 4 (Array.length arr)
        items = foldl (\acc x -> acc `appendBytes` serialize x) emptyBytes arr
    in header `appendBytes` items
  CBORMap pairs ->
    let header = serializeUInt 5 (Array.length pairs)
        items = foldl serializePair emptyBytes pairs
    in header `appendBytes` items
  CBORBool true -> singleByte 245   -- 0xf5 = major 7, additional 21
  CBORBool false -> singleByte 244  -- 0xf4 = major 7, additional 20
  CBORNull -> singleByte 246        -- 0xf6 = major 7, additional 22
  CBORFloat32 n -> serializeFloat32 n
  CBORFloat64 n -> serializeFloat64 n
  where
    serializePair :: Bytes -> Tuple CBORValue CBORValue -> Bytes
    serializePair acc (Tuple k v) = acc `appendBytes` serialize k `appendBytes` serialize v

-- | Serialize to raw int array.
serializeToArray :: CBORValue -> Array Int
serializeToArray value = bytesToArray (serialize value)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // wire // format // impl
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize an unsigned integer with major type.
-- |
-- | Major type goes in bits 7-5, value encoding in bits 4-0 and following bytes.
serializeUInt :: Int -> Int -> Bytes
serializeUInt majorType n
  | n < 0 = serializeUInt majorType 0  -- Safety: treat negative as 0
  | n <= 23 = singleByte (majorType * 32 + n)
  | n <= 255 = Bytes [majorType * 32 + 24, n]
  | n <= 65535 = Bytes 
      [ majorType * 32 + 25
      , shr n 8
      , and n 255
      ]
  | otherwise = Bytes
      [ majorType * 32 + 26
      , and (shr n 24) 255
      , and (shr n 16) 255
      , and (shr n 8) 255
      , and n 255
      ]

-- | Serialize a 32-bit float.
-- |
-- | Format: 0xfa followed by 4 bytes (IEEE 754 single precision).
serializeFloat32 :: Number -> Bytes
serializeFloat32 n = 
  let bits = floatToInt32Bits n
  in Bytes
       [ 250  -- 0xfa = major 7, additional 26
       , bits.b0
       , bits.b1
       , bits.b2
       , bits.b3
       ]

-- | Serialize a 64-bit float.
-- |
-- | Format: 0xfb followed by 8 bytes (IEEE 754 double precision).
-- |
-- | Note: PureScript Int is 32-bit, so we split the double into
-- | high and low 32-bit words, each returned as 4 bytes.
serializeFloat64 :: Number -> Bytes
serializeFloat64 n =
  let high = floatToInt64High n
      low = floatToInt64Low n
  in Bytes
       [ 251  -- 0xfb = major 7, additional 27
       , high.b0
       , high.b1
       , high.b2
       , high.b3
       , low.b0
       , low.b1
       , low.b2
       , low.b3
       ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // float // conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert a Number to IEEE 754 single precision bits.
-- |
-- | IMPORTANT: This assumes bounded types — no NaN, no Infinity.
-- | All Hydrogen numeric types are bounded by construction.
-- | If you pass NaN or Infinity, behavior is undefined (but the type
-- | system should prevent this at the source).
-- |
-- | Returns bytes as 4 separate values to avoid 32-bit overflow.
floatToInt32Bits :: Number -> { b0 :: Int, b1 :: Int, b2 :: Int, b3 :: Int }
floatToInt32Bits n
  | n == 0.0 = { b0: 0, b1: 0, b2: 0, b3: 0 }
  | otherwise =
      let signBit = if n < 0.0 then 128 else 0  -- 0x80 for sign in high byte
          absVal = abs n
          -- Floor of log2 using natural log
          logBase2 = floor (log absVal / ln2)
          exponent = logBase2 + 127
          -- Mantissa: 23 bits (2^23 = 8388608)
          mantissa = floor ((absVal / pow2 logBase2 - 1.0) * 8388608.0)
          -- Split into bytes (big-endian)
          -- Byte 0: sign (1) + exponent high (7)
          b0 = signBit + shr exponent 1
          -- Byte 1: exponent low (1) + mantissa high (7)
          b1 = and (shl exponent 7) 128 + shr mantissa 16
          -- Byte 2: mantissa mid
          b2 = and (shr mantissa 8) 255
          -- Byte 3: mantissa low
          b3 = and mantissa 255
      in { b0, b1, b2, b3 }

-- | High 32 bits of IEEE 754 double precision.
-- |
-- | Assumes bounded input — no NaN/Infinity checks.
-- | Returns bytes as 4 separate values to avoid 32-bit overflow.
floatToInt64High :: Number -> { b0 :: Int, b1 :: Int, b2 :: Int, b3 :: Int }
floatToInt64High n
  | n == 0.0 = { b0: 0, b1: 0, b2: 0, b3: 0 }
  | otherwise =
      let signBit = if n < 0.0 then 128 else 0  -- 0x80 for sign in high byte
          absVal = abs n
          logBase2 = floor (log absVal / ln2)
          exponent = logBase2 + 1023
          -- High 20 bits of 52-bit mantissa
          mantissaFull = (absVal / pow2 logBase2 - 1.0) * 4503599627370496.0
          mantissaHigh = floor (mantissaFull / 4294967296.0)
          -- Split into bytes (big-endian)
          -- Byte 0: sign (1) + exponent high (7)
          b0 = signBit + shr exponent 4
          -- Byte 1: exponent low (4) + mantissa high (4)
          b1 = and (shl exponent 4) 240 + shr mantissaHigh 16
          -- Byte 2: mantissa mid-high
          b2 = and (shr mantissaHigh 8) 255
          -- Byte 3: mantissa mid-low
          b3 = and mantissaHigh 255
      in { b0, b1, b2, b3 }

-- | Low 32 bits of IEEE 754 double precision.
-- |
-- | Assumes bounded input — no NaN/Infinity checks.
-- | Returns bytes as 4 separate values to avoid 32-bit overflow.
floatToInt64Low :: Number -> { b0 :: Int, b1 :: Int, b2 :: Int, b3 :: Int }
floatToInt64Low n
  | n == 0.0 = { b0: 0, b1: 0, b2: 0, b3: 0 }
  | otherwise =
      let absVal = abs n
          logBase2 = floor (log absVal / ln2)
          mantissaFull = (absVal / pow2 logBase2 - 1.0) * 4503599627370496.0
          -- Low 32 bits of mantissa
          high20 = floor (mantissaFull / 4294967296.0)
          low32 = floor (mantissaFull - toNumber high20 * 4294967296.0)
          -- Split low32 into bytes
          b0 = and (shr low32 24) 255
          b1 = and (shr low32 16) 255
          b2 = and (shr low32 8) 255
          b3 = and low32 255
      in { b0, b1, b2, b3 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // math // utils
-- ═════════════════════════════════════════════════════════════════════════════

-- | Power of 2 (for integer exponents).
-- |
-- | Uses repeated multiplication for small exponents.
-- | For large exponents, this is less efficient but pure.
pow2 :: Int -> Number
pow2 exp
  | exp < 0 = 1.0 / pow2Pos (negate exp)
  | otherwise = pow2Pos exp

-- | Power of 2 for non-negative exponents.
pow2Pos :: Int -> Number
pow2Pos e
  | e <= 0 = 1.0
  | otherwise = 2.0 * pow2Pos (e - 1)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // utf8 // encode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert a string to UTF-8 bytes.
-- |
-- | Pure implementation of UTF-8 encoding.
stringToUTF8 :: String -> Array Int
stringToUTF8 s = foldl encodeChar [] (stringToCodePoints s)
  where
    encodeChar :: Array Int -> Int -> Array Int
    encodeChar acc cp
      | cp < 128 = acc <> [cp]
      | cp < 2048 = acc <> 
          [ 192 + shr cp 6
          , 128 + and cp 63
          ]
      | cp < 65536 = acc <>
          [ 224 + shr cp 12
          , 128 + and (shr cp 6) 63
          , 128 + and cp 63
          ]
      | otherwise = acc <>
          [ 240 + shr cp 18
          , 128 + and (shr cp 12) 63
          , 128 + and (shr cp 6) 63
          , 128 + and cp 63
          ]

-- | Convert string to code points.
-- |
-- | Uses String.toCodePointArray from purescript-strings.
stringToCodePoints :: String -> Array Int
stringToCodePoints s = map fromEnum (String.toCodePointArray s)
