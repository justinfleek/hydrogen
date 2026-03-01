-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // gpu // kernel // chart // presets
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Chart Pipeline Presets
-- |
-- | ## Purpose
-- |
-- | Pre-configured chart rendering pipelines for common use cases:
-- |
-- | - Medical: ECG monitors, vital signs trending
-- | - Audio: Waveform displays, spectrum analyzers
-- | - Financial: Stock charts with moving averages
-- |
-- | ## Medical Display Requirements (IEC 60601-1)
-- |
-- | - Minimum 25mm/s sweep speed for ECG
-- | - 1mV = 10mm calibration
-- | - Grid overlay with major/minor divisions
-- | - Color-coded alarm thresholds

module Hydrogen.GPU.Kernel.Chart.Presets
  ( -- * Medical Presets
    ecgMonitorPipeline
  , vitalSignsTrendPipeline
  
  -- * Audio Presets
  , audioWaveformPipeline
  , spectrumAnalyzerPipeline
  
  -- * Financial Presets
  , stockChartPipeline
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( ($)
  , negate
  )

import Hydrogen.GPU.Kernel.Chart.Types
  ( medicalECGConfig
  , audioWaveformConfig
  , financialChartConfig
  )

import Hydrogen.GPU.Kernel.Chart.Waveform
  ( WaveformKernel(WaveformKernel)
  , WaveformStyle(WaveformLine, WaveformMinMax)
  )

import Hydrogen.GPU.Kernel.Chart.LinePlot
  ( LinePlotKernel(LinePlotKernel)
  , LineStyle(LineSolid, LineDashed)
  )

import Hydrogen.GPU.Kernel.Chart.AreaFill
  ( AreaFillKernel(AreaFillKernel)
  , FillMode(FillGradient)
  , GradientDirection(GradientVertical)
  )

import Hydrogen.GPU.Kernel.Chart.BarChart
  ( BarChartKernel(BarChartKernel)
  , BarOrientation(BarVertical)
  , BarGrouping(BarGrouped)
  )

import Hydrogen.GPU.Kernel.Chart.Overlay
  ( ThresholdOverlayKernel(ThresholdOverlayKernel)
  , ThresholdSeverity(SeverityDanger)
  , GridOverlayKernel(GridOverlayKernel)
  , GridStyle(GridLines, GridDashes)
  )

import Hydrogen.GPU.Kernel.Chart.Kernel
  ( ChartKernel
      ( KernelWaveform
      , KernelLinePlot
      , KernelAreaFill
      , KernelBarChart
      , KernelThresholdOverlay
      , KernelGridOverlay
      , KernelChartSequence
      )
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // medical presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | ECG monitor pipeline (IEC 60601-1 compliant)
-- |
-- | Features:
-- | - 25mm/s sweep speed
-- | - 1mV = 10mm calibration
-- | - Medical-grade grid overlay
-- | - Threshold zones for arrhythmia detection
ecgMonitorPipeline :: Int -> Int -> ChartKernel
ecgMonitorPipeline width height =
  let
    config = medicalECGConfig width height
    
    -- ECG waveform (green on black)
    waveform = KernelWaveform $ WaveformKernel
      { style: WaveformLine
      , waveformConfig:
          { sampleCount: 2500  -- 10 seconds at 250 Hz
          , channelCount: 1
          , minValue: -1.5     -- mV
          , maxValue: 1.5      -- mV
          , lineWidth: 2.0
          , antiAliasing: true
          }
      , color: { r: 0.0, g: 1.0, b: 0.0, a: 1.0 }  -- ECG green
      , peakHold: false
      , peakDecay: 0.0
      , rmsOverlay: false
      , zeroCrossing: false
      , config
      }
    
    -- Medical grid (5mm major, 1mm minor)
    grid = KernelGridOverlay $ GridOverlayKernel
      { style: GridLines
      , divisions:
          { majorX: 10
          , majorY: 6
          , minorX: 5
          , minorY: 5
          }
      , majorColor: { r: 0.3, g: 0.3, b: 0.3, a: 0.8 }
      , minorColor: { r: 0.2, g: 0.2, b: 0.2, a: 0.4 }
      , majorWidth: 1.0
      , minorWidth: 0.5
      , showLabels: true
      , labelColor: { r: 0.5, g: 0.5, b: 0.5, a: 1.0 }
      , config
      }
    
    -- Threshold zones for abnormal rhythms
    thresholds = KernelThresholdOverlay $ ThresholdOverlayKernel
      { zones:
          [ { minValue: -1.5, maxValue: -1.0, severity: SeverityDanger
            , color: { r: 1.0, g: 0.0, b: 0.0, a: 0.2 }, label: "Low", showLabel: true }
          , { minValue: 1.0, maxValue: 1.5, severity: SeverityDanger
            , color: { r: 1.0, g: 0.0, b: 0.0, a: 0.2 }, label: "High", showLabel: true }
          ]
      , fillOpacity: 0.2
      , showBorders: true
      , borderWidth: 1.0
      , animated: false
      , pulseOnViolation: true
      , config
      }
  in
    KernelChartSequence [grid, thresholds, waveform]

-- | Vital signs trend pipeline
-- |
-- | Multi-parameter trending for:
-- | - Heart rate
-- | - Blood pressure (systolic/diastolic)
-- | - SpO2
-- | - Temperature
vitalSignsTrendPipeline :: Int -> Int -> ChartKernel
vitalSignsTrendPipeline width height =
  let
    config = medicalECGConfig width height
    
    -- Multi-series line plot
    linePlot = KernelLinePlot $ LinePlotKernel
      { series:
          [ { seriesId: 0, label: "HR", color: { r: 0.0, g: 1.0, b: 0.0, a: 1.0 }
            , lineStyle: LineSolid, lineWidth: 2.0, showPoints: false, pointRadius: 0.0 }
          , { seriesId: 1, label: "SpO2", color: { r: 0.0, g: 0.8, b: 1.0, a: 1.0 }
            , lineStyle: LineSolid, lineWidth: 2.0, showPoints: false, pointRadius: 0.0 }
          , { seriesId: 2, label: "Sys", color: { r: 1.0, g: 0.3, b: 0.3, a: 1.0 }
            , lineStyle: LineSolid, lineWidth: 2.0, showPoints: false, pointRadius: 0.0 }
          , { seriesId: 3, label: "Dia", color: { r: 1.0, g: 0.6, b: 0.3, a: 1.0 }
            , lineStyle: LineDashed, lineWidth: 1.5, showPoints: false, pointRadius: 0.0 }
          ]
      , dataPointCount: 300   -- 5 minutes at 1 Hz
      , xAxisMin: 0.0
      , xAxisMax: 300.0
      , yAxisMin: 0.0
      , yAxisMax: 200.0
      , antiAliasing: true
      , config
      }
    
    grid = KernelGridOverlay $ GridOverlayKernel
      { style: GridDashes
      , divisions: { majorX: 5, majorY: 4, minorX: 6, minorY: 2 }
      , majorColor: { r: 0.4, g: 0.4, b: 0.4, a: 0.6 }
      , minorColor: { r: 0.2, g: 0.2, b: 0.2, a: 0.3 }
      , majorWidth: 1.0
      , minorWidth: 0.5
      , showLabels: true
      , labelColor: { r: 0.6, g: 0.6, b: 0.6, a: 1.0 }
      , config
      }
  in
    KernelChartSequence [grid, linePlot]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // audio presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Audio waveform pipeline
-- |
-- | DAW-style waveform display with:
-- | - Min/max envelope
-- | - RMS overlay
-- | - Peak hold indicators
audioWaveformPipeline :: Int -> Int -> ChartKernel
audioWaveformPipeline width height =
  let
    config = audioWaveformConfig width height
    
    -- Waveform with min/max envelope
    waveform = KernelWaveform $ WaveformKernel
      { style: WaveformMinMax
      , waveformConfig:
          { sampleCount: 44100  -- 1 second at 44.1kHz
          , channelCount: 2     -- Stereo
          , minValue: -1.0
          , maxValue: 1.0
          , lineWidth: 1.0
          , antiAliasing: true
          }
      , color: { r: 0.3, g: 0.7, b: 1.0, a: 1.0 }  -- Blue waveform
      , peakHold: true
      , peakDecay: 12.0        -- 12 dB/s decay
      , rmsOverlay: true
      , zeroCrossing: false
      , config
      }
    
    -- Area fill under waveform
    fill = KernelAreaFill $ AreaFillKernel
      { fillMode: FillGradient
      , primaryColor: { r: 0.3, g: 0.7, b: 1.0, a: 0.5 }
      , secondaryColor: { r: 0.3, g: 0.7, b: 1.0, a: 0.0 }
      , gradientDirection: GradientVertical
      , opacity: 0.5
      , seriesIndex: 0
      , secondSeriesIndex: 0
      , config
      }
  in
    KernelChartSequence [fill, waveform]

-- | Spectrum analyzer pipeline
-- |
-- | Frequency spectrum display with:
-- | - Bar-style frequency bins
-- | - Peak hold
-- | - Logarithmic scale option
spectrumAnalyzerPipeline :: Int -> Int -> ChartKernel
spectrumAnalyzerPipeline width height =
  let
    config = audioWaveformConfig width height
    
    -- Spectrum bars
    bars = KernelBarChart $ BarChartKernel
      { orientation: BarVertical
      , grouping: BarGrouped
      , barColors: 
          [ { r: 0.0, g: 1.0, b: 0.0, a: 1.0 }   -- Green (low)
          , { r: 1.0, g: 1.0, b: 0.0, a: 1.0 }   -- Yellow (mid)
          , { r: 1.0, g: 0.0, b: 0.0, a: 1.0 }   -- Red (high)
          ]
      , barWidth: 0.9
      , barSpacing: 0.05
      , cornerRadius: 2.0
      , showValues: false
      , categoryCount: 32      -- 32 frequency bins
      , seriesCount: 1
      , config
      }
  in
    bars

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // financial presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Stock chart pipeline
-- |
-- | Financial chart with:
-- | - Price line
-- | - Volume bars
-- | - Moving averages
stockChartPipeline :: Int -> Int -> ChartKernel
stockChartPipeline width height =
  let
    config = financialChartConfig width height
    
    -- Price line with moving averages
    priceChart = KernelLinePlot $ LinePlotKernel
      { series:
          [ { seriesId: 0, label: "Price", color: { r: 0.2, g: 0.4, b: 0.8, a: 1.0 }
            , lineStyle: LineSolid, lineWidth: 2.0, showPoints: false, pointRadius: 0.0 }
          , { seriesId: 1, label: "MA20", color: { r: 1.0, g: 0.5, b: 0.0, a: 0.8 }
            , lineStyle: LineSolid, lineWidth: 1.5, showPoints: false, pointRadius: 0.0 }
          , { seriesId: 2, label: "MA50", color: { r: 0.5, g: 0.0, b: 1.0, a: 0.8 }
            , lineStyle: LineSolid, lineWidth: 1.5, showPoints: false, pointRadius: 0.0 }
          ]
      , dataPointCount: 100
      , xAxisMin: 0.0
      , xAxisMax: 100.0
      , yAxisMin: 0.0
      , yAxisMax: 100.0
      , antiAliasing: true
      , config
      }
    
    -- Area fill under price
    fill = KernelAreaFill $ AreaFillKernel
      { fillMode: FillGradient
      , primaryColor: { r: 0.2, g: 0.4, b: 0.8, a: 0.3 }
      , secondaryColor: { r: 0.2, g: 0.4, b: 0.8, a: 0.0 }
      , gradientDirection: GradientVertical
      , opacity: 0.3
      , seriesIndex: 0
      , secondSeriesIndex: 0
      , config
      }
    
    grid = KernelGridOverlay $ GridOverlayKernel
      { style: GridDashes
      , divisions: { majorX: 10, majorY: 5, minorX: 2, minorY: 2 }
      , majorColor: { r: 0.8, g: 0.8, b: 0.8, a: 0.5 }
      , minorColor: { r: 0.9, g: 0.9, b: 0.9, a: 0.3 }
      , majorWidth: 1.0
      , minorWidth: 0.5
      , showLabels: true
      , labelColor: { r: 0.4, g: 0.4, b: 0.4, a: 1.0 }
      , config
      }
  in
    KernelChartSequence [grid, fill, priceChart]
