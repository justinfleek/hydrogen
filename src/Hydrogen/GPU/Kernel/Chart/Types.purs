-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // gpu // kernel // chart // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core Types for Chart Rendering Kernels
-- |
-- | ## Purpose
-- |
-- | Foundational types used across all chart kernel variants:
-- | - Workgroup and dispatch sizing
-- | - Kernel input/output specifications
-- | - Color representation
-- | - Base configuration

module Hydrogen.GPU.Kernel.Chart.Types
  ( -- * Workgroup Configuration
    WorkgroupSize
  , DispatchSize
  
  -- * Kernel I/O
  , KernelInput
      ( InputSampleBuffer
      , InputTexture
      , InputUniform
      , InputPrevious
      )
  , KernelOutput
      ( OutputTexture
      , OutputBuffer
      , OutputScreen
      )
  
  -- * Color
  , ChartColor
  
  -- * Configuration
  , ChartKernelConfig
  , defaultChartKernelConfig
  , medicalECGConfig
  , audioWaveformConfig
  , financialChartConfig
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
--                                                                 // core types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Workgroup size for chart compute dispatch
type WorkgroupSize =
  { x :: Int
  , y :: Int
  , z :: Int
  }

-- | Dispatch dimensions
type DispatchSize =
  { x :: Int
  , y :: Int
  , z :: Int
  }

-- | Chart kernel input source
data KernelInput
  = InputSampleBuffer Int    -- Sample data buffer
  | InputTexture Int         -- Texture input
  | InputUniform Int         -- Uniform buffer
  | InputPrevious            -- Previous kernel output

derive instance eqKernelInput :: Eq KernelInput

instance showKernelInput :: Show KernelInput where
  show (InputSampleBuffer i) = "(InputSampleBuffer " <> show i <> ")"
  show (InputTexture i) = "(InputTexture " <> show i <> ")"
  show (InputUniform i) = "(InputUniform " <> show i <> ")"
  show InputPrevious = "InputPrevious"

-- | Chart kernel output target
data KernelOutput
  = OutputTexture Int        -- Render to texture
  | OutputBuffer Int         -- Write to buffer
  | OutputScreen             -- Final screen output

derive instance eqKernelOutput :: Eq KernelOutput

instance showKernelOutput :: Show KernelOutput where
  show (OutputTexture i) = "(OutputTexture " <> show i <> ")"
  show (OutputBuffer i) = "(OutputBuffer " <> show i <> ")"
  show OutputScreen = "OutputScreen"

-- | RGBA color for charts
type ChartColor =
  { r :: Number
  , g :: Number
  , b :: Number
  , a :: Number
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Chart kernel configuration
type ChartKernelConfig =
  { workgroupSize :: WorkgroupSize
  , input :: KernelInput
  , output :: KernelOutput
  , width :: Int
  , height :: Int
  , backgroundColor :: ChartColor
  }

-- | Default chart kernel configuration
defaultChartKernelConfig :: ChartKernelConfig
defaultChartKernelConfig =
  { workgroupSize: { x: 16, y: 16, z: 1 }
  , input: InputSampleBuffer 0
  , output: OutputScreen
  , width: 800
  , height: 400
  , backgroundColor: { r: 0.0, g: 0.0, b: 0.0, a: 1.0 }
  }

-- | Medical ECG configuration (IEC 60601-1 compliant)
medicalECGConfig :: Int -> Int -> ChartKernelConfig
medicalECGConfig width height =
  { workgroupSize: { x: 16, y: 1, z: 1 }  -- Optimized for horizontal sweep
  , input: InputSampleBuffer 0
  , output: OutputScreen
  , width
  , height
  , backgroundColor: { r: 0.0, g: 0.0, b: 0.0, a: 1.0 }  -- Black background
  }

-- | Audio waveform configuration
audioWaveformConfig :: Int -> Int -> ChartKernelConfig
audioWaveformConfig width height =
  { workgroupSize: { x: 32, y: 1, z: 1 }  -- Wide for sample processing
  , input: InputSampleBuffer 0
  , output: OutputScreen
  , width
  , height
  , backgroundColor: { r: 0.1, g: 0.1, b: 0.1, a: 1.0 }  -- Dark gray
  }

-- | Financial chart configuration
financialChartConfig :: Int -> Int -> ChartKernelConfig
financialChartConfig width height =
  { workgroupSize: { x: 16, y: 16, z: 1 }
  , input: InputSampleBuffer 0
  , output: OutputScreen
  , width
  , height
  , backgroundColor: { r: 1.0, g: 1.0, b: 1.0, a: 1.0 }  -- White background
  }
