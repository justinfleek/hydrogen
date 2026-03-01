-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // tensor // dtype // quantmode
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | QuantMode — Quantization mode specifications for ML inference.
-- |
-- | Defines how model weights and activations are quantized. Based on
-- | TensorRT-LLM quantization.mode.QuantAlgo specifications.
-- |
-- | ## Nomenclature
-- |
-- | W{bits}A{bits} means:
-- | - W = Weights at {bits} precision
-- | - A = Activations at {bits} precision
-- |
-- | ## Hardware Support
-- |
-- | - Blackwell: All modes including NVFP4/MXFP4
-- | - Hopper: FP8 but not NVFP4
-- | - Ampere: INT8/INT4 only
-- | - Older: INT8 only
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)
-- | - DType.Types (for dtype mappings)

module Hydrogen.Schema.Tensor.DType.QuantMode
  ( -- * Quantization Mode
    QuantMode(..)
  
  -- * Smart Constructors
  , quantNone
  , quantW8A8
  , quantW4A16
  , quantW4A8NVFP4
  , quantW4A8MXFP4
  , quantFP8
  
  -- * String Representation
  , quantModeToString
  
  -- * Properties
  , requiresScaling
  , weightDType
  , activationDType
  , supportedQuantModes
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  )

import Hydrogen.Schema.Tensor.DType.Types
  ( DType
  , float16
  , int8
  , int4
  , fp8e4m3
  , nvfp4
  , mxfp4
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // quantization modes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Quantization mode for model weights and activations.
-- |
-- | Nomenclature: W{bits}A{bits} means weights at {bits} and activations at {bits}.
-- | From TensorRT-LLM quantization.mode.QuantAlgo.
data QuantMode
  = NoQuant                    -- ^ No quantization (full precision)
  | W8A8_SQ                    -- ^ SmoothQuant: INT8 weights, INT8 activations
  | W8A16                      -- ^ INT8 weights, FP16 activations
  | W4A16                      -- ^ INT4 weights, FP16 activations (AWQ/GPTQ style)
  | W4A16_AWQ                  -- ^ Activation-aware Weight Quantization
  | W4A16_GPTQ                 -- ^ GPTQ quantization
  | FP8_Linear                 -- ^ FP8 for linear layers only
  | FP8_Full                   -- ^ FP8 for all operations
  | W4A8_NVFP4_FP8             -- ^ NVFP4 weights, FP8 activations
  | W4A8_MXFP4_FP8             -- ^ MXFP4 weights, FP8 activations
  | W8A8_FP8                   -- ^ FP8 weights, FP8 activations

derive instance eqQuantMode :: Eq QuantMode
derive instance ordQuantMode :: Ord QuantMode

instance showQuantMode :: Show QuantMode where
  show = quantModeToString

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // smart constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | No quantization
quantNone :: QuantMode
quantNone = NoQuant

-- | INT8 weights and activations (SmoothQuant)
quantW8A8 :: QuantMode
quantW8A8 = W8A8_SQ

-- | INT4 weights, FP16 activations
quantW4A16 :: QuantMode
quantW4A16 = W4A16

-- | NVFP4 weights, FP8 activations
-- |
-- | State-of-the-art quantization from NVIDIA Blackwell architecture.
quantW4A8NVFP4 :: QuantMode
quantW4A8NVFP4 = W4A8_NVFP4_FP8

-- | MXFP4 weights, FP8 activations
-- |
-- | Microscaling variant for higher accuracy.
quantW4A8MXFP4 :: QuantMode
quantW4A8MXFP4 = W4A8_MXFP4_FP8

-- | FP8 quantization
quantFP8 :: QuantMode
quantFP8 = FP8_Full

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // string representation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert quantization mode to string
quantModeToString :: QuantMode -> String
quantModeToString NoQuant = "None"
quantModeToString W8A8_SQ = "W8A8_SQ"
quantModeToString W8A16 = "W8A16"
quantModeToString W4A16 = "W4A16"
quantModeToString W4A16_AWQ = "W4A16_AWQ"
quantModeToString W4A16_GPTQ = "W4A16_GPTQ"
quantModeToString FP8_Linear = "FP8_Linear"
quantModeToString FP8_Full = "FP8"
quantModeToString W4A8_NVFP4_FP8 = "W4A8_NVFP4_FP8"
quantModeToString W4A8_MXFP4_FP8 = "W4A8_MXFP4_FP8"
quantModeToString W8A8_FP8 = "W8A8_FP8"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | Does this quantization mode require scaling factors?
-- |
-- | Most quantization modes require per-tensor or per-channel scales.
requiresScaling :: QuantMode -> Boolean
requiresScaling NoQuant = false
requiresScaling _ = true

-- | Get the weight dtype for a quantization mode
weightDType :: QuantMode -> DType
weightDType NoQuant = float16
weightDType W8A8_SQ = int8
weightDType W8A16 = int8
weightDType W4A16 = int4
weightDType W4A16_AWQ = int4
weightDType W4A16_GPTQ = int4
weightDType FP8_Linear = fp8e4m3
weightDType FP8_Full = fp8e4m3
weightDType W4A8_NVFP4_FP8 = nvfp4
weightDType W4A8_MXFP4_FP8 = mxfp4
weightDType W8A8_FP8 = fp8e4m3

-- | Get the activation dtype for a quantization mode
activationDType :: QuantMode -> DType
activationDType NoQuant = float16
activationDType W8A8_SQ = int8
activationDType W8A16 = float16
activationDType W4A16 = float16
activationDType W4A16_AWQ = float16
activationDType W4A16_GPTQ = float16
activationDType FP8_Linear = fp8e4m3
activationDType FP8_Full = fp8e4m3
activationDType W4A8_NVFP4_FP8 = fp8e4m3
activationDType W4A8_MXFP4_FP8 = fp8e4m3
activationDType W8A8_FP8 = fp8e4m3

-- | List all supported quantization modes for a target hardware.
-- |
-- | Blackwell supports all modes including NVFP4.
-- | Hopper supports FP8 but not NVFP4.
-- | Older hardware only supports INT8.
supportedQuantModes :: String -> Array QuantMode
supportedQuantModes hardware = case hardware of
  "blackwell" -> allModes
  "hopper" -> hopperModes
  "ampere" -> ampereModes
  _ -> baseModes
  where
    allModes :: Array QuantMode
    allModes = 
      [ NoQuant
      , W8A8_SQ
      , W8A16
      , W4A16
      , W4A16_AWQ
      , W4A16_GPTQ
      , FP8_Linear
      , FP8_Full
      , W4A8_NVFP4_FP8
      , W4A8_MXFP4_FP8
      , W8A8_FP8
      ]
    
    -- Hopper: no NVFP4/MXFP4
    hopperModes :: Array QuantMode
    hopperModes =
      [ NoQuant
      , W8A8_SQ
      , W8A16
      , W4A16
      , W4A16_AWQ
      , W4A16_GPTQ
      , FP8_Linear
      , FP8_Full
      , W8A8_FP8
      ]
    
    -- Ampere: no FP8, no NVFP4
    ampereModes :: Array QuantMode
    ampereModes =
      [ NoQuant
      , W8A8_SQ
      , W8A16
      , W4A16
      , W4A16_AWQ
      , W4A16_GPTQ
      ]
    
    -- Base modes for older hardware
    baseModes :: Array QuantMode
    baseModes = [NoQuant, W8A8_SQ, W8A16, W4A16]
