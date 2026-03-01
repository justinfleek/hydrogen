-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // gpu // kernel // chart // kernel
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Chart Kernel ADT and Composition
-- |
-- | ## Purpose
-- |
-- | The unified `ChartKernel` sum type that encompasses all chart rendering
-- | variants, along with composition and dispatch calculation utilities.
-- |
-- | ## Kernel Variants
-- |
-- | - Waveform: Audio/medical waveform display
-- | - Sparkline: Inline mini charts
-- | - LinePlot: Multi-series line charts
-- | - AreaFill: Filled area charts
-- | - BarChart: Categorical bar charts
-- | - ThresholdOverlay: Alarm zone visualization
-- | - GridOverlay: Measurement grids
-- | - Sequence: Composed kernel pipelines
-- | - Noop: Identity kernel

module Hydrogen.GPU.Kernel.Chart.Kernel
  ( -- * Chart Kernel ADT
    ChartKernel
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
  
  -- * Composition
  , sequenceChartKernels
  , conditionalChartKernel
  
  -- * Dispatch Calculation
  , computeChartWorkgroupSize
  , computeChartDispatchSize
  , getChartKernelDimensions
  , estimateChartKernelCost
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  )

import Data.Array as Array
import Data.Int as Int
import Data.Maybe (Maybe(Nothing, Just))

import Hydrogen.GPU.Kernel.Chart.Types
  ( WorkgroupSize
  , DispatchSize
  )

import Hydrogen.GPU.Kernel.Chart.Waveform
  ( WaveformKernel(WaveformKernel)
  )

import Hydrogen.GPU.Kernel.Chart.Sparkline
  ( SparklineKernel(SparklineKernel)
  )

import Hydrogen.GPU.Kernel.Chart.LinePlot
  ( LinePlotKernel(LinePlotKernel)
  )

import Hydrogen.GPU.Kernel.Chart.AreaFill
  ( AreaFillKernel(AreaFillKernel)
  )

import Hydrogen.GPU.Kernel.Chart.BarChart
  ( BarChartKernel(BarChartKernel)
  )

import Hydrogen.GPU.Kernel.Chart.Overlay
  ( ThresholdOverlayKernel(ThresholdOverlayKernel)
  , GridOverlayKernel(GridOverlayKernel)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // chart kernel adt
-- ═════════════════════════════════════════════════════════════════════════════

-- | Chart rendering kernel variants
data ChartKernel
  = KernelWaveform WaveformKernel
  | KernelSparkline SparklineKernel
  | KernelLinePlot LinePlotKernel
  | KernelAreaFill AreaFillKernel
  | KernelBarChart BarChartKernel
  | KernelThresholdOverlay ThresholdOverlayKernel
  | KernelGridOverlay GridOverlayKernel
  | KernelChartSequence (Array ChartKernel)
  | KernelChartNoop

derive instance eqChartKernel :: Eq ChartKernel

instance showChartKernel :: Show ChartKernel where
  show (KernelWaveform k) = "(KernelWaveform " <> show k <> ")"
  show (KernelSparkline k) = "(KernelSparkline " <> show k <> ")"
  show (KernelLinePlot k) = "(KernelLinePlot " <> show k <> ")"
  show (KernelAreaFill k) = "(KernelAreaFill " <> show k <> ")"
  show (KernelBarChart k) = "(KernelBarChart " <> show k <> ")"
  show (KernelThresholdOverlay k) = "(KernelThresholdOverlay " <> show k <> ")"
  show (KernelGridOverlay k) = "(KernelGridOverlay " <> show k <> ")"
  show (KernelChartSequence _) = "(KernelChartSequence [...])"
  show KernelChartNoop = "KernelChartNoop"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // kernel composition
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sequence multiple chart kernels
sequenceChartKernels :: Array ChartKernel -> ChartKernel
sequenceChartKernels kernels =
  case Array.length kernels of
    0 -> KernelChartNoop
    1 -> case Array.head kernels of
           Nothing -> KernelChartNoop
           Just k -> k
    _ -> KernelChartSequence kernels

-- | Conditional chart kernel execution
conditionalChartKernel 
  :: Boolean 
  -> ChartKernel 
  -> ChartKernel 
  -> ChartKernel
conditionalChartKernel condition thenKernel elseKernel =
  if condition
    then thenKernel
    else elseKernel

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // dispatch calculation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute workgroup size for chart kernel
computeChartWorkgroupSize :: ChartKernel -> WorkgroupSize
computeChartWorkgroupSize kernel =
  case kernel of
    KernelWaveform (WaveformKernel k) -> k.config.workgroupSize
    KernelSparkline (SparklineKernel k) -> k.config.workgroupSize
    KernelLinePlot (LinePlotKernel k) -> k.config.workgroupSize
    KernelAreaFill (AreaFillKernel k) -> k.config.workgroupSize
    KernelBarChart (BarChartKernel k) -> k.config.workgroupSize
    KernelThresholdOverlay (ThresholdOverlayKernel k) -> k.config.workgroupSize
    KernelGridOverlay (GridOverlayKernel k) -> k.config.workgroupSize
    KernelChartSequence kernels -> 
      case Array.head kernels of
        Nothing -> { x: 16, y: 16, z: 1 }
        Just k -> computeChartWorkgroupSize k
    KernelChartNoop -> { x: 1, y: 1, z: 1 }

-- | Compute dispatch size for chart kernel
computeChartDispatchSize :: ChartKernel -> DispatchSize
computeChartDispatchSize kernel =
  let
    workgroup = computeChartWorkgroupSize kernel
    dims = getChartKernelDimensions kernel
    divCeil a b = (a + b - 1) / b
  in
    { x: divCeil dims.width workgroup.x
    , y: divCeil dims.height workgroup.y
    , z: 1
    }

-- | Get kernel dimensions
getChartKernelDimensions :: ChartKernel -> { width :: Int, height :: Int }
getChartKernelDimensions kernel =
  case kernel of
    KernelWaveform (WaveformKernel k) -> 
      { width: k.config.width, height: k.config.height }
    KernelSparkline (SparklineKernel k) -> 
      { width: k.config.width, height: k.config.height }
    KernelLinePlot (LinePlotKernel k) -> 
      { width: k.config.width, height: k.config.height }
    KernelAreaFill (AreaFillKernel k) -> 
      { width: k.config.width, height: k.config.height }
    KernelBarChart (BarChartKernel k) -> 
      { width: k.config.width, height: k.config.height }
    KernelThresholdOverlay (ThresholdOverlayKernel k) -> 
      { width: k.config.width, height: k.config.height }
    KernelGridOverlay (GridOverlayKernel k) -> 
      { width: k.config.width, height: k.config.height }
    KernelChartSequence kernels ->
      case Array.head kernels of
        Nothing -> { width: 0, height: 0 }
        Just k -> getChartKernelDimensions k
    KernelChartNoop -> { width: 0, height: 0 }

-- | Estimate kernel execution cost (microseconds)
estimateChartKernelCost :: ChartKernel -> Number
estimateChartKernelCost kernel =
  case kernel of
    KernelWaveform (WaveformKernel k) ->
      -- Waveform: ~2μs per 1K samples
      Int.toNumber k.waveformConfig.sampleCount / 500.0
    KernelSparkline (SparklineKernel k) ->
      -- Sparkline: ~1μs per point
      Int.toNumber k.sparklineConfig.dataPoints
    KernelLinePlot (LinePlotKernel k) ->
      -- Line plot: ~5μs per series per 1K points
      Int.toNumber (Array.length k.series * k.dataPointCount) / 200.0
    KernelAreaFill (AreaFillKernel k) ->
      -- Area fill: ~10μs per 1K pixels
      Int.toNumber (k.config.width * k.config.height) / 100.0
    KernelBarChart (BarChartKernel k) ->
      -- Bar chart: ~1μs per bar
      Int.toNumber (k.categoryCount * k.seriesCount)
    KernelThresholdOverlay (ThresholdOverlayKernel k) ->
      -- Threshold: ~5μs per zone per 1K pixels
      Int.toNumber (Array.length k.zones) * 
      Int.toNumber (k.config.width * k.config.height) / 200.0
    KernelGridOverlay (GridOverlayKernel k) ->
      -- Grid: ~2μs per line
      Int.toNumber (k.divisions.majorX + k.divisions.majorY + 
                    k.divisions.minorX * k.divisions.majorX + 
                    k.divisions.minorY * k.divisions.majorY) * 2.0
    KernelChartSequence kernels ->
      foldlArray (\acc k -> acc + estimateChartKernelCost k) 0.0 kernels
    KernelChartNoop -> 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fold left over array
foldlArray :: forall a b. (b -> a -> b) -> b -> Array a -> b
foldlArray f init arr =
  case Array.uncons arr of
    Nothing -> init
    Just { head, tail } -> foldlArray f (f init head) tail
