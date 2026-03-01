-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // tensor // dtype
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DType — Tensor element data types for ML inference.
-- |
-- | ## Design Philosophy
-- |
-- | Tensor data types define how individual elements are stored and computed.
-- | This module provides bounded atoms for all common ML precision formats,
-- | including cutting-edge quantization formats from NVIDIA TensorRT-LLM.
-- |
-- | ## Format Categories
-- |
-- | **Standard IEEE Formats**:
-- | - Float32 (FP32): Full precision, 32 bits
-- | - Float16 (FP16): Half precision, 16 bits
-- | - BFloat16 (BF16): Brain float, 16 bits (8 exp, 7 mantissa)
-- |
-- | **NVIDIA 8-bit Formats**:
-- | - FP8_E4M3: 8 bits (4 exp, 3 mantissa) — higher precision
-- | - FP8_E5M2: 8 bits (5 exp, 2 mantissa) — wider range
-- |
-- | **NVIDIA 4-bit Formats** (TensorRT-LLM):
-- | - NVFP4 (FP4_E2M1): 4 bits (2 exp, 1 mantissa, no inf/NaN)
-- | - MXFP4: Microscaling FP4 with block-level scaling factors
-- | - INT4: 4-bit integer quantization
-- |
-- | **Integer Quantization**:
-- | - INT8: 8-bit integer (signed or unsigned)
-- | - INT4: 4-bit integer (weight-only quantization)
-- |
-- | ## Quantization Modes
-- |
-- | From TensorRT-LLM quantization.mode:
-- | - W8A8: Weights and activations both INT8
-- | - W4A16: Weights INT4, activations FP16
-- | - W4A8_NVFP4_FP8: Weights NVFP4, activations FP8
-- | - W4A8_MXFP4_FP8: Weights MXFP4, activations FP8
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from:
-- | - `DType.Types`: Core type definitions and constructors
-- | - `DType.QuantMode`: Quantization mode specifications
-- | - `DType.Properties`: Type property queries
-- | - `DType.Operations`: Comparison and transformation

module Hydrogen.Schema.Tensor.DType
  ( module Types
  , module QuantMode
  , module Properties
  , module Operations
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Tensor.DType.Types as Types
import Hydrogen.Schema.Tensor.DType.QuantMode as QuantMode
import Hydrogen.Schema.Tensor.DType.Properties as Properties
import Hydrogen.Schema.Tensor.DType.Operations as Operations
