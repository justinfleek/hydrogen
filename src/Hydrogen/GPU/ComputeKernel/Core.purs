-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // gpu // compute-kernel/core
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ComputeKernel/Core — Core Types for GPU Compute Kernels
-- |
-- | This module defines the foundational types for compute kernel operations:
-- | - Input/output specifications
-- | - Kernel configuration
-- | - Quality and condition types
-- |
-- | These types are imported by all other kernel submodules.

module Hydrogen.GPU.ComputeKernel.Core
  ( -- * Workgroup & Dispatch
    WorkgroupSize
  , DispatchSize
  
  -- * Input/Output
  , KernelInput(InputTexture, InputBuffer, InputUniform, InputPrevious, InputConstant)
  , KernelOutput(OutputTexture, OutputBuffer, OutputNext, OutputScreen)
  , KernelConfig
  
  -- * Conditions
  , KernelCondition(ConditionQuality, ConditionSize, ConditionPerformance, ConditionAlways)
  , QualityLevel(QualityLow, QualityMedium, QualityHigh, QualityUltra)
  , SizeThreshold
  
  -- * Helpers
  , defaultConfig
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // workgroup & dispatch
-- ═════════════════════════════════════════════════════════════════════════════

-- | Workgroup size for compute dispatch
-- |
-- | Defines thread dimensions for GPU compute workgroups.
-- | Common configurations:
-- | - 16×16×1: 2D image processing
-- | - 8×8×8: 3D operations (noise with octaves)
-- | - 256×1×1: 1D particle arrays
type WorkgroupSize =
  { x :: Int               -- Threads in X (typically 8, 16, or 32)
  , y :: Int               -- Threads in Y
  , z :: Int               -- Threads in Z
  }

-- | Dispatch dimensions (number of workgroups)
-- |
-- | Calculated from output dimensions / workgroup size.
type DispatchSize =
  { x :: Int               -- Workgroups in X
  , y :: Int               -- Workgroups in Y
  , z :: Int               -- Workgroups in Z
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // input/output
-- ═════════════════════════════════════════════════════════════════════════════

-- | Input source for kernel
-- |
-- | Specifies where the kernel reads data from:
-- | - Textures for image data
-- | - Buffers for structured data (particles, meshes)
-- | - Uniforms for parameters
-- | - Previous kernel output for chaining
-- | - Constants for fixed values
data KernelInput
  = InputTexture Int           -- Texture by index
  | InputBuffer Int            -- Storage buffer by index
  | InputUniform Int           -- Uniform buffer by index
  | InputPrevious              -- Output of previous kernel in chain
  | InputConstant Number       -- Constant value

derive instance eqKernelInput :: Eq KernelInput

instance showKernelInput :: Show KernelInput where
  show (InputTexture i) = "(InputTexture " <> show i <> ")"
  show (InputBuffer i) = "(InputBuffer " <> show i <> ")"
  show (InputUniform i) = "(InputUniform " <> show i <> ")"
  show InputPrevious = "InputPrevious"
  show (InputConstant v) = "(InputConstant " <> show v <> ")"

-- | Output target for kernel
-- |
-- | Specifies where the kernel writes results:
-- | - Textures for image output
-- | - Buffers for structured output
-- | - Next kernel in chain
-- | - Screen for final presentation
data KernelOutput
  = OutputTexture Int          -- Write to texture by index
  | OutputBuffer Int           -- Write to storage buffer
  | OutputNext                 -- Feed to next kernel
  | OutputScreen               -- Final output to screen

derive instance eqKernelOutput :: Eq KernelOutput

instance showKernelOutput :: Show KernelOutput where
  show (OutputTexture i) = "(OutputTexture " <> show i <> ")"
  show (OutputBuffer i) = "(OutputBuffer " <> show i <> ")"
  show OutputNext = "OutputNext"
  show OutputScreen = "OutputScreen"

-- | Kernel configuration
-- |
-- | Common configuration shared by all kernel types.
type KernelConfig =
  { workgroupSize :: WorkgroupSize
  , input :: KernelInput
  , output :: KernelOutput
  , width :: Int               -- Output width in pixels
  , height :: Int              -- Output height in pixels
  , channels :: Int            -- Number of channels (typically 4 for RGBA)
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // conditions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Condition for kernel execution
-- |
-- | Enables adaptive kernel selection based on runtime conditions:
-- | - Quality settings for LOD systems
-- | - Size thresholds for scaling
-- | - Performance budgets for real-time constraints
data KernelCondition
  = ConditionQuality QualityLevel    -- Based on quality setting
  | ConditionSize SizeThreshold      -- Based on output size
  | ConditionPerformance Number      -- Based on GPU budget (ms)
  | ConditionAlways                  -- Always true

derive instance eqKernelCondition :: Eq KernelCondition

-- | Quality levels for adaptive processing
-- |
-- | At billion-agent scale, quality selection determines GPU budget allocation.
data QualityLevel
  = QualityLow
  | QualityMedium
  | QualityHigh
  | QualityUltra

derive instance eqQualityLevel :: Eq QualityLevel

-- | Size threshold for conditional kernels
type SizeThreshold =
  { minWidth :: Int
  , minHeight :: Int
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default kernel config
-- |
-- | Creates a standard configuration for 2D image processing.
defaultConfig :: Int -> Int -> KernelConfig
defaultConfig w h =
  { workgroupSize: { x: 16, y: 16, z: 1 }
  , input: InputPrevious
  , output: OutputNext
  , width: w
  , height: h
  , channels: 4
  }
