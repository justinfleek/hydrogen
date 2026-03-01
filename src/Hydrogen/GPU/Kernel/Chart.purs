-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // gpu // kernel // chart
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Chart Rendering Kernels — Waveforms, Trends, and Data Visualization
-- |
-- | ## Purpose
-- |
-- | High-performance chart rendering for:
-- |
-- | - Medical dashboards (ECG waveforms, vital sign trends)
-- | - Audio workstations (waveform display, spectrum analyzers)
-- | - Financial dashboards (real-time price charts)
-- | - Industrial monitoring (sensor data visualization)
-- |
-- | ## Waveform Rendering Pipeline
-- |
-- | ```
-- | Sample Buffer -> Downsample -> Line/Fill Render -> Anti-aliasing
-- |                                    |
-- |                              Threshold Overlay
-- |                                    |
-- |                              Composited Output
-- | ```
-- |
-- | ## Medical Display Requirements (IEC 60601-1)
-- |
-- | - Minimum 25mm/s sweep speed for ECG
-- | - 1mV = 10mm calibration
-- | - Grid overlay with major/minor divisions
-- | - Color-coded alarm thresholds
-- | - Signal quality indicators
-- |
-- | ## Audio Display Requirements
-- |
-- | - Waveform with peak hold
-- | - RMS envelope overlay
-- | - Zero-crossing indicators
-- | - Stereo correlation
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Chart kernels are deterministic:
-- | - Same samples + config = same pixels (always)
-- | - Sample buffers are content-addressed
-- | - Downsampling is pure function
-- | - Multiple agents can share visualization cache
-- |
-- | ## Module Structure
-- |
-- | This is the leader module. Implementation is split across:
-- |
-- | - `Chart.Types`: Core types and configuration
-- | - `Chart.Waveform`: Waveform rendering kernel
-- | - `Chart.Sparkline`: Inline mini chart kernel
-- | - `Chart.LinePlot`: Multi-series line charts
-- | - `Chart.AreaFill`: Filled area charts
-- | - `Chart.BarChart`: Categorical bar charts
-- | - `Chart.Overlay`: Threshold and grid overlays
-- | - `Chart.Kernel`: Kernel ADT and composition
-- | - `Chart.Presets`: Pre-configured pipelines

module Hydrogen.GPU.Kernel.Chart
  ( -- * Core Types
    module Hydrogen.GPU.Kernel.Chart.Types
  
  -- * Kernel ADT
  , module Hydrogen.GPU.Kernel.Chart.Kernel
  
  -- * Waveform Rendering
  , module Hydrogen.GPU.Kernel.Chart.Waveform
  
  -- * Sparkline (Inline Charts)
  , module Hydrogen.GPU.Kernel.Chart.Sparkline
  
  -- * Line Plot (Multi-series)
  , module Hydrogen.GPU.Kernel.Chart.LinePlot
  
  -- * Area Fill
  , module Hydrogen.GPU.Kernel.Chart.AreaFill
  
  -- * Bar Chart
  , module Hydrogen.GPU.Kernel.Chart.BarChart
  
  -- * Overlays
  , module Hydrogen.GPU.Kernel.Chart.Overlay
  
  -- * Presets
  , module Hydrogen.GPU.Kernel.Chart.Presets
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.GPU.Kernel.Chart.Types
  ( WorkgroupSize
  , DispatchSize
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
  , ChartColor
  , ChartKernelConfig
  , defaultChartKernelConfig
  , medicalECGConfig
  , audioWaveformConfig
  , financialChartConfig
  )

import Hydrogen.GPU.Kernel.Chart.Waveform
  ( WaveformKernel(WaveformKernel)
  , WaveformStyle
      ( WaveformLine
      , WaveformFilled
      , WaveformBars
      , WaveformPoints
      , WaveformMinMax
      )
  , WaveformConfig
  , mkWaveformKernel
  )

import Hydrogen.GPU.Kernel.Chart.Sparkline
  ( SparklineKernel(SparklineKernel)
  , SparklineStyle
      ( SparklineLine
      , SparklineArea
      , SparklineBar
      , SparklineWinLoss
      )
  , SparklineConfig
  , mkSparklineKernel
  )

import Hydrogen.GPU.Kernel.Chart.LinePlot
  ( LinePlotKernel(LinePlotKernel)
  , LineStyle
      ( LineSolid
      , LineDashed
      , LineDotted
      , LineStepBefore
      , LineStepAfter
      , LineCardinal
      , LineMonotone
      )
  , SeriesConfig
  , mkLinePlotKernel
  )

import Hydrogen.GPU.Kernel.Chart.AreaFill
  ( AreaFillKernel(AreaFillKernel)
  , FillMode
      ( FillToZero
      , FillToMin
      , FillBetween
      , FillGradient
      )
  , GradientDirection
      ( GradientVertical
      , GradientHorizontal
      )
  , mkAreaFillKernel
  )

import Hydrogen.GPU.Kernel.Chart.BarChart
  ( BarChartKernel(BarChartKernel)
  , BarOrientation
      ( BarVertical
      , BarHorizontal
      )
  , BarGrouping
      ( BarStacked
      , BarGrouped
      , BarOverlapped
      )
  , mkBarChartKernel
  )

import Hydrogen.GPU.Kernel.Chart.Overlay
  ( ThresholdOverlayKernel(ThresholdOverlayKernel)
  , ThresholdZone
  , ThresholdSeverity
      ( SeverityNormal
      , SeverityWarning
      , SeverityCritical
      , SeverityDanger
      )
  , mkThresholdOverlayKernel
  , GridOverlayKernel(GridOverlayKernel)
  , GridStyle
      ( GridLines
      , GridDots
      , GridDashes
      )
  , GridDivisions
  , mkGridOverlayKernel
  )

import Hydrogen.GPU.Kernel.Chart.Kernel
  ( ChartKernel
      ( KernelWaveform
      , KernelSparkline
      , KernelLinePlot
      , KernelAreaFill
      , KernelBarChart
      , KernelThresholdOverlay
      , KernelGridOverlay
      , KernelChartSequence
      , KernelChartNoop
      )
  , sequenceChartKernels
  , conditionalChartKernel
  , computeChartWorkgroupSize
  , computeChartDispatchSize
  , getChartKernelDimensions
  , estimateChartKernelCost
  )

import Hydrogen.GPU.Kernel.Chart.Presets
  ( ecgMonitorPipeline
  , vitalSignsTrendPipeline
  , audioWaveformPipeline
  , spectrumAnalyzerPipeline
  , stockChartPipeline
  )
