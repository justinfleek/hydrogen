-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // tensor // dtype // properties
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DType Properties — Query functions for tensor element types.
-- |
-- | This module provides functions to inspect DType properties:
-- | - Bit/byte widths for memory calculations
-- | - Type classification (float, int, quantized)
-- | - Format details (exponent bits, mantissa bits)
-- | - Special value support (Inf/NaN)
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Boolean, Int, comparisons)
-- | - DType.Types (core definitions)

module Hydrogen.Schema.Tensor.DType.Properties
  ( -- * Bit Width
    bitWidth
  , byteWidth
  
  -- * Type Classification
  , isFloatingPoint
  , isInteger
  , isQuantized
  , isSigned
  , isNumeric
  
  -- * Format Details
  , hasInfNaN
  , exponentBits
  , mantissaBits
  
  -- * Memory Calculation
  , elementsPerByte
  , bytesForElements
  
  -- * Array Operations
  , bitWidths
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( map
  , (/=)
  , (/)
  , (*)
  , (+)
  , (<)
  , (>=)
  )

import Hydrogen.Schema.Tensor.DType.Types
  ( DType
      ( FloatType
      , IntType
      , QuantizedType
      )
  , FloatFormat
      ( IEEE_FP32
      , IEEE_FP16
      , BF16
      , FP8_E4M3
      , FP8_E5M2
      , FP4_E2M1
      , MXFP4_E2M1
      )
  , IntFormat
      ( Int4Signed
      , Int4Unsigned
      , Int8Signed
      , Int8Unsigned
      , Bool
      )
  , floatBitWidth
  , intBitWidth
  , bool
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // bit width
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get bit width of data type
bitWidth :: DType -> Int
bitWidth (FloatType fmt) = floatBitWidth fmt
bitWidth (IntType fmt) = intBitWidth fmt
bitWidth (QuantizedType q) = bitWidth q.baseType

-- | Get byte width (rounded up for sub-byte types)
byteWidth :: DType -> Int
byteWidth dtype = 
  let bits = bitWidth dtype
  in if bits < 8 then 1 else bits / 8

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // type classification
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is this a floating point type?
isFloatingPoint :: DType -> Boolean
isFloatingPoint (FloatType _) = true
isFloatingPoint (IntType _) = false
isFloatingPoint (QuantizedType q) = isFloatingPoint q.baseType

-- | Is this an integer type?
isInteger :: DType -> Boolean
isInteger (FloatType _) = false
isInteger (IntType _) = true
isInteger (QuantizedType q) = isInteger q.baseType

-- | Is this a quantized type?
isQuantized :: DType -> Boolean
isQuantized (QuantizedType _) = true
isQuantized _ = false

-- | Is this type signed?
isSigned :: DType -> Boolean
isSigned (FloatType _) = true  -- All floats are signed
isSigned (IntType Int4Unsigned) = false
isSigned (IntType Int8Unsigned) = false
isSigned (IntType Bool) = false
isSigned (IntType _) = true
isSigned (QuantizedType q) = isSigned q.baseType

-- | Check if dtype is NOT a boolean type.
-- |
-- | Used to validate numeric operations.
isNumeric :: DType -> Boolean
isNumeric dtype = dtype /= bool

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // format details
-- ═════════════════════════════════════════════════════════════════════════════

-- | Does this type support Inf/NaN?
hasInfNaN :: DType -> Boolean
hasInfNaN (FloatType IEEE_FP32) = true
hasInfNaN (FloatType IEEE_FP16) = true
hasInfNaN (FloatType BF16) = true
hasInfNaN (FloatType FP8_E4M3) = true  -- Has NaN only (no Inf)
hasInfNaN (FloatType FP8_E5M2) = true
hasInfNaN (FloatType FP4_E2M1) = false  -- NVFP4 is "FN" (Finite)
hasInfNaN (FloatType MXFP4_E2M1) = false
hasInfNaN (IntType _) = false
hasInfNaN (QuantizedType q) = hasInfNaN q.baseType

-- | Get exponent bits (0 for integers)
exponentBits :: DType -> Int
exponentBits (FloatType IEEE_FP32) = 8
exponentBits (FloatType IEEE_FP16) = 5
exponentBits (FloatType BF16) = 8
exponentBits (FloatType FP8_E4M3) = 4
exponentBits (FloatType FP8_E5M2) = 5
exponentBits (FloatType FP4_E2M1) = 2
exponentBits (FloatType MXFP4_E2M1) = 2
exponentBits (IntType _) = 0
exponentBits (QuantizedType q) = exponentBits q.baseType

-- | Get mantissa bits (0 for integers)
mantissaBits :: DType -> Int
mantissaBits (FloatType IEEE_FP32) = 23
mantissaBits (FloatType IEEE_FP16) = 10
mantissaBits (FloatType BF16) = 7
mantissaBits (FloatType FP8_E4M3) = 3
mantissaBits (FloatType FP8_E5M2) = 2
mantissaBits (FloatType FP4_E2M1) = 1
mantissaBits (FloatType MXFP4_E2M1) = 1
mantissaBits (IntType _) = 0
mantissaBits (QuantizedType q) = mantissaBits q.baseType

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // memory calculation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Number of elements that fit in one byte
-- |
-- | For sub-byte types (INT4, FP4), multiple elements pack into one byte.
elementsPerByte :: DType -> Int
elementsPerByte dtype =
  let bits = bitWidth dtype
  in if bits >= 8 then 1 else 8 / bits

-- | Bytes needed to store N elements
-- |
-- | Rounds up for sub-byte types.
bytesForElements :: DType -> Int -> Int
bytesForElements dtype count =
  let 
    bits = bitWidth dtype
    totalBits = bits * count
    -- Ceiling division: (a + b - 1) / b
  in (totalBits + 7) / 8

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // array operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get bit widths for an array of dtypes.
-- |
-- | Useful for computing total memory footprint.
bitWidths :: Array DType -> Array Int
bitWidths = map bitWidth
