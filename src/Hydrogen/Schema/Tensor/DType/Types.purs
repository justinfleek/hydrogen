-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // tensor // dtype // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core DType definitions — data type atoms for tensor elements.
-- |
-- | This module defines the fundamental data types used in ML tensors:
-- | - FloatFormat: IEEE and NVIDIA floating point formats
-- | - IntFormat: Integer formats including sub-byte quantization
-- | - QuantFormat: Quantization scale granularity
-- | - DType: Unified tensor element type
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)

module Hydrogen.Schema.Tensor.DType.Types
  ( -- * Float Format
    FloatFormat(..)
  
  -- * Integer Format
  , IntFormat(..)
  
  -- * Quantization Format
  , QuantFormat(..)
  
  -- * Core DType
  , DType(..)
  
  -- * Smart Constructors
  , float32
  , float16
  , bfloat16
  , fp8e4m3
  , fp8e5m2
  , nvfp4
  , mxfp4
  , int8
  , uint8
  , int4
  , int32
  , int64
  , bool
  
  -- * String Representation
  , dtypeToString
  
  -- * Internal Helpers (for submodules)
  , floatBitWidth
  , intBitWidth
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // float format
-- ═════════════════════════════════════════════════════════════════════════════

-- | Floating point format specification.
-- |
-- | Defines the bit layout: sign, exponent, mantissa, and special value handling.
data FloatFormat
  = IEEE_FP32      -- ^ 1 sign, 8 exp, 23 mantissa (standard float)
  | IEEE_FP16      -- ^ 1 sign, 5 exp, 10 mantissa (half precision)
  | BF16           -- ^ 1 sign, 8 exp, 7 mantissa (brain float)
  | FP8_E4M3       -- ^ 1 sign, 4 exp, 3 mantissa (NVIDIA FP8)
  | FP8_E5M2       -- ^ 1 sign, 5 exp, 2 mantissa (NVIDIA FP8)
  | FP4_E2M1       -- ^ 1 sign, 2 exp, 1 mantissa (NVFP4, no inf/NaN)
  | MXFP4_E2M1     -- ^ FP4 with microscaling (block scale factors)

derive instance eqFloatFormat :: Eq FloatFormat
derive instance ordFloatFormat :: Ord FloatFormat

instance showFloatFormat :: Show FloatFormat where
  show IEEE_FP32 = "FP32"
  show IEEE_FP16 = "FP16"
  show BF16 = "BF16"
  show FP8_E4M3 = "FP8_E4M3"
  show FP8_E5M2 = "FP8_E5M2"
  show FP4_E2M1 = "NVFP4"
  show MXFP4_E2M1 = "MXFP4"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // int format
-- ═════════════════════════════════════════════════════════════════════════════

-- | Integer format specification.
data IntFormat
  = Int4Signed     -- ^ 4-bit signed integer (-8 to 7)
  | Int4Unsigned   -- ^ 4-bit unsigned integer (0 to 15)
  | Int8Signed     -- ^ 8-bit signed integer (-128 to 127)
  | Int8Unsigned   -- ^ 8-bit unsigned integer (0 to 255)
  | Int16Signed    -- ^ 16-bit signed integer
  | Int32Signed    -- ^ 32-bit signed integer
  | Int64Signed    -- ^ 64-bit signed integer
  | Bool           -- ^ Boolean (1 bit logical, typically 8 bits storage)

derive instance eqIntFormat :: Eq IntFormat
derive instance ordIntFormat :: Ord IntFormat

instance showIntFormat :: Show IntFormat where
  show Int4Signed = "INT4"
  show Int4Unsigned = "UINT4"
  show Int8Signed = "INT8"
  show Int8Unsigned = "UINT8"
  show Int16Signed = "INT16"
  show Int32Signed = "INT32"
  show Int64Signed = "INT64"
  show Bool = "BOOL"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // quant format
-- ═════════════════════════════════════════════════════════════════════════════

-- | Quantization format specification.
-- |
-- | Quantized formats require scale factors and sometimes zero points.
data QuantFormat
  = PerTensor      -- ^ Single scale for entire tensor
  | PerChannel     -- ^ Scale per output channel
  | PerGroup       -- ^ Scale per group of elements (e.g., 128 elements)
      { groupSize :: Int }
  | PerBlock       -- ^ Microscaling: scale per block (MXFP4)
      { blockSize :: Int }

derive instance eqQuantFormat :: Eq QuantFormat
derive instance ordQuantFormat :: Ord QuantFormat

instance showQuantFormat :: Show QuantFormat where
  show PerTensor = "PerTensor"
  show PerChannel = "PerChannel"
  show (PerGroup g) = "PerGroup(" <> show g.groupSize <> ")"
  show (PerBlock b) = "PerBlock(" <> show b.blockSize <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // dtype
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tensor element data type.
-- |
-- | Encompasses all supported numeric formats for tensor elements.
data DType
  = FloatType FloatFormat
  | IntType IntFormat
  | QuantizedType
      { baseType :: DType       -- ^ Underlying storage type
      , quantFormat :: QuantFormat  -- ^ How scales are applied
      }

derive instance eqDType :: Eq DType

instance showDType :: Show DType where
  show = dtypeToString

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | 32-bit IEEE floating point
float32 :: DType
float32 = FloatType IEEE_FP32

-- | 16-bit IEEE floating point (half precision)
float16 :: DType
float16 = FloatType IEEE_FP16

-- | 16-bit Brain Float (wider range than FP16)
bfloat16 :: DType
bfloat16 = FloatType BF16

-- | 8-bit float with 4 exponent, 3 mantissa bits
-- |
-- | Higher precision variant of FP8. Preferred for inference.
fp8e4m3 :: DType
fp8e4m3 = FloatType FP8_E4M3

-- | 8-bit float with 5 exponent, 2 mantissa bits
-- |
-- | Wider dynamic range variant of FP8. Preferred for training gradients.
fp8e5m2 :: DType
fp8e5m2 = FloatType FP8_E5M2

-- | NVIDIA 4-bit float (FP4_E2M1)
-- |
-- | 4 bits total: 1 sign, 2 exponent, 1 mantissa.
-- | No infinity or NaN representations (all bit patterns are finite).
-- | Used in TensorRT-LLM for weight quantization.
nvfp4 :: DType
nvfp4 = FloatType FP4_E2M1

-- | Microscaling FP4 (MXFP4)
-- |
-- | Like NVFP4 but with block-level scaling factors for better accuracy.
-- | Each block of values shares a common scale factor.
mxfp4 :: DType
mxfp4 = FloatType MXFP4_E2M1

-- | 8-bit signed integer
int8 :: DType
int8 = IntType Int8Signed

-- | 8-bit unsigned integer
uint8 :: DType
uint8 = IntType Int8Unsigned

-- | 4-bit signed integer (for weight quantization)
int4 :: DType
int4 = IntType Int4Signed

-- | 32-bit signed integer
int32 :: DType
int32 = IntType Int32Signed

-- | 64-bit signed integer
int64 :: DType
int64 = IntType Int64Signed

-- | Boolean type
bool :: DType
bool = IntType Bool

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // string representation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert dtype to string representation
dtypeToString :: DType -> String
dtypeToString (FloatType fmt) = show fmt
dtypeToString (IntType fmt) = show fmt
dtypeToString (QuantizedType q) = 
  "Quantized(" <> dtypeToString q.baseType <> ", " <> show q.quantFormat <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bit width for float formats
floatBitWidth :: FloatFormat -> Int
floatBitWidth IEEE_FP32 = 32
floatBitWidth IEEE_FP16 = 16
floatBitWidth BF16 = 16
floatBitWidth FP8_E4M3 = 8
floatBitWidth FP8_E5M2 = 8
floatBitWidth FP4_E2M1 = 4
floatBitWidth MXFP4_E2M1 = 4

-- | Bit width for int formats
intBitWidth :: IntFormat -> Int
intBitWidth Int4Signed = 4
intBitWidth Int4Unsigned = 4
intBitWidth Int8Signed = 8
intBitWidth Int8Unsigned = 8
intBitWidth Int16Signed = 16
intBitWidth Int32Signed = 32
intBitWidth Int64Signed = 64
intBitWidth Bool = 1
