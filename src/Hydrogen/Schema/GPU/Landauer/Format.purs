-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // gpu // landauer // format
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Hardware precision formats for Landauer-aware precision selection.
-- |
-- | This module defines the available hardware precision formats and their
-- | properties. Format selection is entropy-driven: given measured entropy,
-- | we select the minimum format that can represent the information content.

module Hydrogen.Schema.GPU.Landauer.Format
  ( -- * Precision Formats
    PrecisionFormat(FP32, FP16, BF16, FP8E4M3, FP8E5M2, FP4, INT8, INT4)
  , formatBits
  , formatForEntropy
  , formatCapacity
  ) where

import Prelude
  ( class Eq
  , class Show
  , otherwise
  , (<=)
  )

import Hydrogen.Schema.GPU.Landauer.Internal (Entropy(Entropy))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // precision formats
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hardware precision formats.
data PrecisionFormat
  = FP32      -- 32-bit float
  | FP16      -- 16-bit float
  | BF16      -- 16-bit bfloat
  | FP8E4M3   -- 8-bit float (4 exp, 3 mantissa)
  | FP8E5M2   -- 8-bit float (5 exp, 2 mantissa)
  | FP4       -- 4-bit float (NVFP4)
  | INT8      -- 8-bit integer
  | INT4      -- 4-bit integer

derive instance eqPrecisionFormat :: Eq PrecisionFormat

instance showPrecisionFormat :: Show PrecisionFormat where
  show FP32 = "FP32"
  show FP16 = "FP16"
  show BF16 = "BF16"
  show FP8E4M3 = "FP8E4M3"
  show FP8E5M2 = "FP8E5M2"
  show FP4 = "FP4"
  show INT8 = "INT8"
  show INT4 = "INT4"

-- | Get bit width of format
formatBits :: PrecisionFormat -> Int
formatBits FP32 = 32
formatBits FP16 = 16
formatBits BF16 = 16
formatBits FP8E4M3 = 8
formatBits FP8E5M2 = 8
formatBits FP4 = 4
formatBits INT8 = 8
formatBits INT4 = 4

-- | Get effective capacity (usable bits) of format
-- |
-- | This accounts for format overhead (exponent, sign, etc.)
formatCapacity :: PrecisionFormat -> Number
formatCapacity FP32 = 24.0    -- 23 mantissa + implicit
formatCapacity FP16 = 11.0    -- 10 mantissa + implicit
formatCapacity BF16 = 8.0     -- 7 mantissa + implicit
formatCapacity FP8E4M3 = 4.0  -- 3 mantissa + implicit
formatCapacity FP8E5M2 = 3.0  -- 2 mantissa + implicit
formatCapacity FP4 = 2.5      -- ~2.5 effective bits
formatCapacity INT8 = 8.0
formatCapacity INT4 = 4.0

-- | Select the minimum precision format that can hold the entropy.
formatForEntropy :: Entropy -> PrecisionFormat
formatForEntropy (Entropy h)
  | h <= 2.5 = FP4
  | h <= 3.0 = FP8E5M2
  | h <= 4.0 = FP8E4M3
  | h <= 8.0 = BF16
  | h <= 11.0 = FP16
  | otherwise = FP32
