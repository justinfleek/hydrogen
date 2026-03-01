-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // gpu // binary // lowlevel
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Low-level byte operations for binary GPU command serialization.
-- |
-- | This module provides primitive read/write operations for converting
-- | between PureScript types and little-endian byte arrays.
-- |
-- | ## IEEE 754 Implementation
-- |
-- | All floating point operations use IEEE 754 single precision (32-bit).
-- | The implementation is pure PureScript without FFI.

module Hydrogen.GPU.Binary.LowLevel
  ( -- * Byte array operations
    toByteArray
  , fromByteArray
  
  -- * Write operations
  , writeF32
  , writeU32
  , writeU16
  , writeU8
  , writeI8
  
  -- * Read operations
  , readF32
  , readU32
  , readU8
  
  -- * String conversion
  , stringToBytes
  ) where

import Prelude
  ( mod
  , otherwise
  , (+)
  , (-)
  , (/)
  , (<)
  , (==)
  , (>=)
  , (*)
  )

import Data.Array (index, snoc) as Array
import Data.Enum (fromEnum)
import Data.Int (floor, toNumber)
import Data.Int.Bits (shl, shr, (.&.), (.|.))
import Data.Maybe (Maybe(Just, Nothing))
import Data.String.CodeUnits (toCharArray) as String
import Hydrogen.GPU.Binary.Types (Bytes(Bytes))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // byte array operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Bytes to raw byte array.
toByteArray :: Bytes -> Array Int
toByteArray (Bytes arr) = arr

-- | Create Bytes from raw byte array.
fromByteArray :: Array Int -> Bytes
fromByteArray = Bytes

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // write operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Write a 32-bit float as 4 bytes (little-endian).
-- | IEEE 754 single precision.
writeF32 :: Number -> Array Int
writeF32 n =
  let
    -- Convert float to IEEE 754 bits
    bits = floatToBits n
  in
    [ bits .&. 0xFF
    , (shr bits 8) .&. 0xFF
    , (shr bits 16) .&. 0xFF
    , (shr bits 24) .&. 0xFF
    ]

-- | Write a 32-bit unsigned integer as 4 bytes (little-endian).
writeU32 :: Int -> Array Int
writeU32 n =
  [ n .&. 0xFF
  , (shr n 8) .&. 0xFF
  , (shr n 16) .&. 0xFF
  , (shr n 24) .&. 0xFF
  ]

-- | Write a 16-bit unsigned integer as 2 bytes (little-endian).
writeU16 :: Int -> Array Int
writeU16 n =
  [ n .&. 0xFF
  , (shr n 8) .&. 0xFF
  ]

-- | Write an 8-bit unsigned integer.
writeU8 :: Int -> Array Int
writeU8 n = [n .&. 0xFF]

-- | Write a signed 8-bit integer (stored as unsigned).
-- | Values -128 to 127 are stored as 0-255.
writeI8 :: Int -> Array Int
writeI8 n = 
  let unsigned = if n < 0 then 256 + n else n
  in [unsigned .&. 0xFF]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // read operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Read a 32-bit float from bytes at offset.
readF32 :: Array Int -> Int -> Maybe Number
readF32 arr offset =
  case Array.index arr offset
     , Array.index arr (offset + 1)
     , Array.index arr (offset + 2)
     , Array.index arr (offset + 3) of
    Just b0, Just b1, Just b2, Just b3 ->
      let bits = b0 .|. (shl b1 8) .|. (shl b2 16) .|. (shl b3 24)
      in Just (bitsToFloat bits)
    _, _, _, _ -> Nothing

-- | Read a 32-bit unsigned integer from bytes at offset.
readU32 :: Array Int -> Int -> Maybe Int
readU32 arr offset =
  case Array.index arr offset
     , Array.index arr (offset + 1)
     , Array.index arr (offset + 2)
     , Array.index arr (offset + 3) of
    Just b0, Just b1, Just b2, Just b3 ->
      Just (b0 .|. (shl b1 8) .|. (shl b2 16) .|. (shl b3 24))
    _, _, _, _ -> Nothing

-- | Read an 8-bit unsigned integer from bytes at offset.
readU8 :: Array Int -> Int -> Maybe Int
readU8 arr offset = Array.index arr offset

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // string conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert String to byte array (ASCII).
-- | Characters outside ASCII range are replaced with '?' (63).
stringToBytes :: String -> Array Int
stringToBytes str = charArrayToBytes (String.toCharArray str)
  where
    charArrayToBytes :: Array Char -> Array Int
    charArrayToBytes chars = mapArray charToByte chars
    
    charToByte :: Char -> Int
    charToByte c =
      let code = fromEnum c
      in if code < 128 then code else 63  -- '?' for non-ASCII

    mapArray :: forall a b. (a -> b) -> Array a -> Array b
    mapArray f arr = mapArrayHelper f arr 0 []
    
    mapArrayHelper :: forall a b. (a -> b) -> Array a -> Int -> Array b -> Array b
    mapArrayHelper f arr idx acc =
      case Array.index arr idx of
        Nothing -> acc
        Just x -> mapArrayHelper f arr (idx + 1) (Array.snoc acc (f x))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // ieee 754 conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert float to IEEE 754 bits.
-- | Pure implementation without FFI.
floatToBits :: Number -> Int
floatToBits n
  | n == 0.0 = 0
  | otherwise =
      let
        sign = if n < 0.0 then 1 else 0
        absN = if n < 0.0 then negate n else n
        
        -- Find exponent and mantissa
        -- This is a simplified implementation
        -- For production, would need proper IEEE 754 handling
        logResult = log2Approx absN
        exp = floor logResult + 127
        mantissa = floor ((absN / pow2 (exp - 127) - 1.0) * 8388608.0)
      in
        (shl sign 31) .|. (shl (exp .&. 0xFF) 23) .|. (mantissa .&. 0x7FFFFF)
  where
    negate x = 0.0 - x

-- | Convert IEEE 754 bits to float.
bitsToFloat :: Int -> Number
bitsToFloat bits =
  let
    sign = shr bits 31
    exp = (shr bits 23) .&. 0xFF
    mantissa = bits .&. 0x7FFFFF
    
    signMult = if sign == 0 then 1.0 else (0.0 - 1.0)
  in
    if exp == 0 then
      if mantissa == 0 then 0.0
      else signMult * pow2 (exp - 127) * (1.0 + toNumber mantissa / 8388608.0)
    else signMult * pow2 (exp - 127) * (1.0 + toNumber mantissa / 8388608.0)

-- | Approximate log base 2.
log2Approx :: Number -> Number
log2Approx n = nativeLog n / nativeLog 2.0

-- | Power of 2.
pow2 :: Int -> Number
pow2 e = 
  if e >= 0 
    then pow2Positive e 1.0
    else 1.0 / pow2Positive (0 - e) 1.0
  where
    pow2Positive :: Int -> Number -> Number
    pow2Positive 0 acc = acc
    pow2Positive pn acc = pow2Positive (pn - 1) (acc * 2.0)

-- | Native log function (using series expansion for purity).
-- | For production, this would use a more efficient method.
nativeLog :: Number -> Number
nativeLog x = 
  if x == 1.0 
    then 0.0
  else if x >= 0.0 then
    if x < 2.0 
      then logSeries (x - 1.0) 1 0.0
    else log2Const + nativeLog (x / 2.0)
  else 0.0  -- Invalid input, return 0
  where
    log2Const :: Number
    log2Const = 0.6931471805599453
    
    logSeries :: Number -> Int -> Number -> Number
    logSeries _ 100 acc = acc  -- Limit iterations
    logSeries y pn acc =
      let term = (if mod pn 2 == 0 then (0.0 - 1.0) else 1.0) * powNum y pn / toNumber pn
      in logSeries y (pn + 1) (acc + term)
    
    powNum :: Number -> Int -> Number
    powNum _ 0 = 1.0
    powNum base pexp = base * powNum base (pexp - 1)
