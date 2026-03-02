-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // element // compound // charts
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Advanced Chart Components — SVG-based data visualization.
-- |
-- | ## Components
-- |
-- | - **PieChart**: Circular chart showing proportions
-- | - **DonutChart**: Pie chart with center cutout
-- | - **RadarChart**: Multi-axis comparison chart
-- | - **ScatterPlot**: X/Y coordinate point visualization
-- | - **GaugeChart**: Radial progress/value indicator
-- | - **Heatmap**: Color-coded matrix visualization
-- | - **Sparkline**: Inline mini chart
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Charts as Charts
-- |
-- | -- Pie chart
-- | Charts.pieChart []
-- |   [ { value: 30.0, label: "A", color: "#3b82f6" }
-- |   , { value: 50.0, label: "B", color: "#22c55e" }
-- |   , { value: 20.0, label: "C", color: "#eab308" }
-- |   ]
-- |
-- | -- Gauge chart
-- | Charts.gaugeChart [ Charts.gaugeMax 100.0 ]
-- |   { value: 75.0, label: "Progress" }
-- |
-- | -- Sparkline
-- | Charts.sparkline [ Charts.sparklineShowArea true ]
-- |   [10.0, 15.0, 12.0, 18.0, 22.0, 20.0]
-- | ```

module Hydrogen.Element.Compound.Charts
  ( -- * Re-exports
    module Hydrogen.Element.Compound.Charts.Types
  , module Hydrogen.Element.Compound.Charts.Pie
  , module Hydrogen.Element.Compound.Charts.Radar
  , module Hydrogen.Element.Compound.Charts.Scatter
  , module Hydrogen.Element.Compound.Charts.Gauge
  , module Hydrogen.Element.Compound.Charts.Heatmap
  , module Hydrogen.Element.Compound.Charts.Sparkline
  ) where

import Hydrogen.Element.Compound.Charts.Types
  ( ColorScale(Sequential, Diverging, Categorical)
  , valueToColor
  )

import Hydrogen.Element.Compound.Charts.Pie
  ( pieChart
  , donutChart
  , PieChartProps
  , PieChartProp
  , PieSlice
  , defaultPieProps
  , pieSize
  , pieInnerRadius
  , pieShowLabels
  , pieShowLegend
  )

import Hydrogen.Element.Compound.Charts.Radar
  ( radarChart
  , RadarChartProps
  , RadarChartProp
  , RadarData
  , RadarSeries
  , defaultRadarProps
  , radarSize
  , radarShowGrid
  , radarShowLabels
  , radarFillOpacity
  )

import Hydrogen.Element.Compound.Charts.Scatter
  ( scatterPlot
  , ScatterPlotProps
  , ScatterPlotProp
  , ScatterPoint
  , defaultScatterProps
  , scatterWidth
  , scatterHeight
  , scatterShowGrid
  , scatterShowAxes
  , scatterPointSize
  )

import Hydrogen.Element.Compound.Charts.Gauge
  ( gaugeChart
  , GaugeChartProps
  , GaugeChartProp
  , GaugeData
  , defaultGaugeProps
  , gaugeSize
  , gaugeMin
  , gaugeMax
  , gaugeThickness
  , gaugeShowValue
  , gaugeColor
  )

import Hydrogen.Element.Compound.Charts.Heatmap
  ( heatmap
  , HeatmapProps
  , HeatmapProp
  , HeatmapData
  , HeatmapCell
  , defaultHeatmapProps
  , heatmapCellSize
  , heatmapGap
  , heatmapShowLabels
  , heatmapColorScale
  )

import Hydrogen.Element.Compound.Charts.Sparkline
  ( sparkline
  , SparklineProps
  , SparklineProp
  , defaultSparklineProps
  , sparklineWidth
  , sparklineHeight
  , sparklineColor
  , sparklineShowArea
  , sparklineShowDots
  )
