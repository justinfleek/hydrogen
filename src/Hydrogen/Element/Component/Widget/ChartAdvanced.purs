-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // element // widget // chart-advanced
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Advanced Chart Types — Waterfall, Grouped, Stacked, Rainfall, DualAxis.
-- |
-- | ## Design Philosophy
-- |
-- | These chart types extend the base Chart module with more complex
-- | visualizations commonly seen in business dashboards and KPI widgets.
-- |
-- | Implements chart types from COMPASS bento reference PNGs:
-- | - Waterfall: Shows cumulative effect of sequential values
-- | - GroupedBar: Multiple bars per category for comparison
-- | - StackedBar/Column: Stacked segments showing composition
-- | - Rainfall: Dual distribution (bidirectional histogram)
-- | - DualAxis: Line + Column on same chart with two Y-axes
-- |
-- | Pure Element output — no framework dependencies.

module Hydrogen.Element.Component.Widget.ChartAdvanced
  ( -- * Waterfall Chart
    waterfallChart
  , WaterfallData
  , WaterfallConfig
  , defaultWaterfallConfig
  
  -- * Grouped Bar Chart
  , groupedBarChart
  , GroupedBarData
  , GroupedBarConfig
  , defaultGroupedBarConfig
  
  -- * Stacked Bar/Column Chart
  , stackedBarChart
  , stackedColumnChart
  , StackedData
  , StackedConfig
  , defaultStackedConfig
  
  -- * Rainfall/Distribution Chart
  , rainfallChart
  , RainfallData
  , RainfallConfig
  , defaultRainfallConfig
  
  -- * Dual Axis Chart
  , dualAxisChart
  , DualAxisData
  , DualAxisConfig
  , defaultDualAxisConfig
  ) where

import Prelude
  ( class Show
  , show
  , (==)
  , (&&)
  , (||)
  , (<>)
  , (<=)
  , (<)
  , (>)
  , (+)
  , (-)
  , (*)
  , (/)
  , negate
  , mod
  , not
  )

import Data.Array (foldl, index, length, mapWithIndex)
import Data.Int (toNumber)
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Hydrogen.Math.Core as Math
import Hydrogen.Render.Element as E

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // waterfall chart
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Waterfall chart data point.
-- |
-- | Each bar shows the delta from the previous cumulative value.
-- | Positive values go up, negative values go down.
type WaterfallData =
  { label :: String
  , value :: Number       -- ^ Delta value (positive or negative)
  , isTotal :: Boolean    -- ^ If true, shows as total bar (different styling)
  }

-- | Waterfall chart configuration.
type WaterfallConfig =
  { title :: Maybe String
  , width :: Number
  , height :: Number
  , positiveColor :: String
  , negativeColor :: String
  , totalColor :: String
  , showConnectors :: Boolean
  , className :: String
  }

-- | Default waterfall configuration.
defaultWaterfallConfig :: WaterfallConfig
defaultWaterfallConfig =
  { title: Nothing
  , width: 400.0
  , height: 200.0
  , positiveColor: "#22C55E"  -- Neon green
  , negativeColor: "#EF4444"  -- Neon red
  , totalColor: "#3B82F6"     -- Blue
  , showConnectors: true
  , className: ""
  }

-- | Render a waterfall chart.
-- |
-- | Shows cumulative effect of sequential positive/negative values.
-- | Bars float to show running total.
waterfallChart :: forall msg. WaterfallConfig -> Array WaterfallData -> E.Element msg
waterfallChart cfg dataPoints =
  let
    viewBox = "0 0 " <> show cfg.width <> " " <> show cfg.height
    padding = 40.0
    plotWidth = cfg.width - padding * 2.0
    plotHeight = cfg.height - padding * 2.0
    numBars = length dataPoints
    barWidth = if numBars <= 0 then 30.0 else (plotWidth / toNumber numBars) * 0.7
    barGap = if numBars <= 0 then 10.0 else (plotWidth / toNumber numBars) * 0.3
    
    -- Calculate cumulative values and range
    cumulativeValues = calculateCumulative dataPoints
    minVal = arrayMin cumulativeValues
    maxVal = arrayMax cumulativeValues
    range = if maxVal - minVal == 0.0 then 1.0 else maxVal - minVal
    
    -- Scale Y value to plot coordinates
    scaleY :: Number -> Number
    scaleY v = padding + plotHeight - ((v - minVal) / range) * plotHeight
    
    baseline = scaleY 0.0
  in
    E.svg_
      [ E.attr "viewBox" viewBox
      , E.class_ ("w-full h-full " <> cfg.className)
      , E.attr "preserveAspectRatio" "xMidYMid meet"
      ]
      [ -- Axis
        E.line_
          [ E.attr "x1" (show padding)
          , E.attr "y1" (show baseline)
          , E.attr "x2" (show (cfg.width - padding))
          , E.attr "y2" (show baseline)
          , E.attr "stroke" "currentColor"
          , E.attr "stroke-opacity" "0.2"
          ]
      -- Bars
      , E.g_
          [ E.class_ "waterfall-bars" ]
          (mapWithIndex (renderWaterfallBar cfg padding barWidth barGap scaleY cumulativeValues) dataPoints)
      ]

-- | Calculate cumulative values for waterfall.
calculateCumulative :: Array WaterfallData -> Array Number
calculateCumulative dataPoints =
  let
    go :: { running :: Number, values :: Array Number } -> WaterfallData -> { running :: Number, values :: Array Number }
    go acc d =
      if d.isTotal
        then { running: d.value, values: acc.values <> [d.value] }
        else 
          let newRunning = acc.running + d.value
          in { running: newRunning, values: acc.values <> [newRunning] }
    
    result = foldl go { running: 0.0, values: [] } dataPoints
  in
    result.values

-- | Render a single waterfall bar.
renderWaterfallBar :: forall msg. 
  WaterfallConfig -> 
  Number -> 
  Number -> 
  Number -> 
  (Number -> Number) -> 
  Array Number -> 
  Int -> 
  WaterfallData -> 
  E.Element msg
renderWaterfallBar cfg padding barWidth barGap scaleY cumulatives idx d =
  let
    x = padding + toNumber idx * (barWidth + barGap) + barGap / 2.0
    
    -- Get cumulative before and after
    prevCumulative = if idx == 0 then 0.0 else fromMaybe 0.0 (index cumulatives (idx - 1))
    currCumulative = fromMaybe 0.0 (index cumulatives idx)
    
    -- Bar position
    yTop = scaleY (Math.max prevCumulative currCumulative)
    yBottom = scaleY (Math.min prevCumulative currCumulative)
    barHeight = yBottom - yTop
    
    -- Color based on positive/negative/total
    color = if d.isTotal 
            then cfg.totalColor
            else if d.value > 0.0 then cfg.positiveColor else cfg.negativeColor
  in
    E.g_
      []
      [ -- Bar with glow
        E.rect_
          [ E.attr "x" (show x)
          , E.attr "y" (show yTop)
          , E.attr "width" (show barWidth)
          , E.attr "height" (show (Math.max 1.0 barHeight))
          , E.attr "fill" color
          , E.attr "rx" "2"
          , E.style "filter" ("drop-shadow(0 0 6px " <> color <> "80)")
          ]
      -- Label
      , E.text_
          [ E.attr "x" (show (x + barWidth / 2.0))
          , E.attr "y" (show (cfg.height - 10.0))
          , E.attr "text-anchor" "middle"
          , E.attr "font-size" "10"
          , E.attr "fill" "currentColor"
          , E.attr "fill-opacity" "0.7"
          ]
          [ E.text d.label ]
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // grouped bar chart
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Grouped bar chart data.
-- |
-- | Each category has multiple values (one per series).
type GroupedBarData =
  { category :: String
  , values :: Array Number  -- ^ One value per series
  }

-- | Grouped bar chart configuration.
type GroupedBarConfig =
  { title :: Maybe String
  , width :: Number
  , height :: Number
  , seriesNames :: Array String
  , seriesColors :: Array String
  , horizontal :: Boolean
  , className :: String
  }

-- | Default grouped bar configuration.
defaultGroupedBarConfig :: GroupedBarConfig
defaultGroupedBarConfig =
  { title: Nothing
  , width: 400.0
  , height: 200.0
  , seriesNames: []
  , seriesColors: ["#3B82F6", "#22C55E", "#FBBF24", "#8B5CF6", "#F43F5E"]
  , horizontal: false
  , className: ""
  }

-- | Render a grouped bar chart.
-- |
-- | Multiple bars per category, side by side for comparison.
groupedBarChart :: forall msg. GroupedBarConfig -> Array GroupedBarData -> E.Element msg
groupedBarChart cfg dataPoints =
  let
    viewBox = "0 0 " <> show cfg.width <> " " <> show cfg.height
    padding = 40.0
    plotWidth = cfg.width - padding * 2.0
    plotHeight = cfg.height - padding * 2.0
    
    numCategories = length dataPoints
    numSeries = case index dataPoints 0 of
      Nothing -> 0
      Just d -> length d.values
    
    -- Calculate dimensions
    categoryWidth = if numCategories <= 0 then 50.0 else plotWidth / toNumber numCategories
    barWidth = if numSeries <= 0 then 20.0 else (categoryWidth * 0.8) / toNumber numSeries
    
    -- Get value range
    allValues = foldl (\acc d -> acc <> d.values) [] dataPoints
    maxVal = arrayMax allValues
    minVal = Math.min 0.0 (arrayMin allValues)  -- Include 0 in range
    range = if maxVal - minVal == 0.0 then 1.0 else maxVal - minVal
    
    scaleY :: Number -> Number
    scaleY v = padding + plotHeight - ((v - minVal) / range) * plotHeight
    
    baseline = scaleY 0.0
  in
    E.svg_
      [ E.attr "viewBox" viewBox
      , E.class_ ("w-full h-full " <> cfg.className)
      , E.attr "preserveAspectRatio" "xMidYMid meet"
      ]
      [ -- Baseline
        E.line_
          [ E.attr "x1" (show padding)
          , E.attr "y1" (show baseline)
          , E.attr "x2" (show (cfg.width - padding))
          , E.attr "y2" (show baseline)
          , E.attr "stroke" "currentColor"
          , E.attr "stroke-opacity" "0.2"
          ]
      -- Category groups
      , E.g_
          [ E.class_ "grouped-bars" ]
          (mapWithIndex (renderCategoryGroup cfg padding categoryWidth barWidth scaleY baseline) dataPoints)
      ]

-- | Render a single category group with multiple bars.
renderCategoryGroup :: forall msg.
  GroupedBarConfig ->
  Number ->
  Number ->
  Number ->
  (Number -> Number) ->
  Number ->
  Int ->
  GroupedBarData ->
  E.Element msg
renderCategoryGroup cfg padding categoryWidth barWidth scaleY baseline catIdx catData =
  let
    catX = padding + toNumber catIdx * categoryWidth + categoryWidth * 0.1
  in
    E.g_
      []
      ([ -- Category label
         E.text_
           [ E.attr "x" (show (catX + categoryWidth * 0.4))
           , E.attr "y" (show (cfg.height - 10.0))
           , E.attr "text-anchor" "middle"
           , E.attr "font-size" "10"
           , E.attr "fill" "currentColor"
           , E.attr "fill-opacity" "0.7"
           ]
           [ E.text catData.category ]
       ] <> mapWithIndex (renderGroupedBar cfg catX barWidth scaleY baseline) catData.values)

-- | Render a single bar within a group.
renderGroupedBar :: forall msg.
  GroupedBarConfig ->
  Number ->
  Number ->
  (Number -> Number) ->
  Number ->
  Int ->
  Number ->
  E.Element msg
renderGroupedBar cfg catX barWidth scaleY baseline seriesIdx value =
  let
    x = catX + toNumber seriesIdx * barWidth
    yTop = scaleY value
    barHeight = baseline - yTop
    color = fromMaybe "#3B82F6" (index cfg.seriesColors seriesIdx)
  in
    E.rect_
      [ E.attr "x" (show x)
      , E.attr "y" (show (if value > 0.0 then yTop else baseline))
      , E.attr "width" (show (barWidth * 0.9))
      , E.attr "height" (show (Math.abs barHeight))
      , E.attr "fill" color
      , E.attr "rx" "2"
      , E.style "filter" ("drop-shadow(0 0 8px " <> color <> "60)")
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // stacked charts
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Stacked chart data (same structure as grouped).
type StackedData = GroupedBarData

-- | Stacked chart configuration.
type StackedConfig =
  { title :: Maybe String
  , width :: Number
  , height :: Number
  , seriesNames :: Array String
  , seriesColors :: Array String
  , className :: String
  }

-- | Default stacked configuration.
defaultStackedConfig :: StackedConfig
defaultStackedConfig =
  { title: Nothing
  , width: 400.0
  , height: 200.0
  , seriesNames: []
  , seriesColors: ["#22C55E", "#8B5CF6", "#3B82F6", "#FBBF24", "#F43F5E"]
  , className: ""
  }

-- | Render a stacked bar chart (horizontal).
stackedBarChart :: forall msg. StackedConfig -> Array StackedData -> E.Element msg
stackedBarChart cfg dataPoints =
  let
    viewBox = "0 0 " <> show cfg.width <> " " <> show cfg.height
    padding = 40.0
    plotWidth = cfg.width - padding * 2.0
    plotHeight = cfg.height - padding * 2.0
    
    numCategories = length dataPoints
    barHeight = if numCategories <= 0 then 20.0 else (plotHeight / toNumber numCategories) * 0.7
    
    -- Get max total for scaling
    totals = mapWithIndex (\_ d -> foldl (+) 0.0 d.values) dataPoints
    maxTotal = arrayMax totals
    
    scaleX :: Number -> Number
    scaleX v = if maxTotal == 0.0 then 0.0 else (v / maxTotal) * plotWidth
  in
    E.svg_
      [ E.attr "viewBox" viewBox
      , E.class_ ("w-full h-full " <> cfg.className)
      , E.attr "preserveAspectRatio" "xMidYMid meet"
      ]
      [ E.g_
          [ E.class_ "stacked-bars" ]
          (mapWithIndex (renderStackedBarRow cfg padding barHeight scaleX) dataPoints)
      ]

-- | Render a single stacked bar row.
renderStackedBarRow :: forall msg.
  StackedConfig ->
  Number ->
  Number ->
  (Number -> Number) ->
  Int ->
  StackedData ->
  E.Element msg
renderStackedBarRow cfg padding barHeight scaleX rowIdx rowData =
  let
    y = padding + toNumber rowIdx * (barHeight * 1.4)
    
    -- Calculate segment positions
    segments = calculateStackedSegments cfg.seriesColors rowData.values scaleX
  in
    E.g_
      []
      ([ E.text_
           [ E.attr "x" (show (padding - 5.0))
           , E.attr "y" (show (y + barHeight / 2.0))
           , E.attr "text-anchor" "end"
           , E.attr "dominant-baseline" "middle"
           , E.attr "font-size" "10"
           , E.attr "fill" "currentColor"
           , E.attr "fill-opacity" "0.7"
           ]
           [ E.text rowData.category ]
       ] <> mapWithIndex (\segIdx seg ->
         E.rect_
           [ E.attr "x" (show (padding + seg.x))
           , E.attr "y" (show y)
           , E.attr "width" (show seg.width)
           , E.attr "height" (show barHeight)
           , E.attr "fill" seg.color
           , E.attr "rx" "2"
           , E.style "filter" ("drop-shadow(0 0 6px " <> seg.color <> "50)")
           ]
       ) segments)

-- | Calculate stacked segment positions.
calculateStackedSegments :: Array String -> Array Number -> (Number -> Number) -> Array { x :: Number, width :: Number, color :: String }
calculateStackedSegments colors values scaleX =
  let
    go :: { runningX :: Number, segments :: Array { x :: Number, width :: Number, color :: String } } -> 
          { idx :: Int, value :: Number } -> 
          { runningX :: Number, segments :: Array { x :: Number, width :: Number, color :: String } }
    go acc item =
      let
        width = scaleX item.value
        color = fromMaybe "#3B82F6" (index colors item.idx)
        segment = { x: acc.runningX, width: width, color: color }
      in
        { runningX: acc.runningX + width, segments: acc.segments <> [segment] }
    
    indexed = mapWithIndex (\idx v -> { idx: idx, value: v }) values
    result = foldl go { runningX: 0.0, segments: [] } indexed
  in
    result.segments

-- | Render a stacked column chart (vertical).
stackedColumnChart :: forall msg. StackedConfig -> Array StackedData -> E.Element msg
stackedColumnChart cfg dataPoints =
  let
    viewBox = "0 0 " <> show cfg.width <> " " <> show cfg.height
    padding = 40.0
    plotWidth = cfg.width - padding * 2.0
    plotHeight = cfg.height - padding * 2.0
    
    numCategories = length dataPoints
    barWidth = if numCategories <= 0 then 30.0 else (plotWidth / toNumber numCategories) * 0.7
    
    -- Get max total for scaling
    totals = mapWithIndex (\_ d -> foldl (+) 0.0 d.values) dataPoints
    maxTotal = arrayMax totals
    
    scaleY :: Number -> Number
    scaleY v = if maxTotal == 0.0 then 0.0 else (v / maxTotal) * plotHeight
  in
    E.svg_
      [ E.attr "viewBox" viewBox
      , E.class_ ("w-full h-full " <> cfg.className)
      , E.attr "preserveAspectRatio" "xMidYMid meet"
      ]
      [ E.g_
          [ E.class_ "stacked-columns" ]
          (mapWithIndex (renderStackedColumnGroup cfg padding plotHeight barWidth scaleY) dataPoints)
      ]

-- | Render a single stacked column.
renderStackedColumnGroup :: forall msg.
  StackedConfig ->
  Number ->
  Number ->
  Number ->
  (Number -> Number) ->
  Int ->
  StackedData ->
  E.Element msg
renderStackedColumnGroup cfg padding plotHeight barWidth scaleY colIdx colData =
  let
    x = padding + toNumber colIdx * (barWidth * 1.4) + barWidth * 0.2
    baseline = padding + plotHeight
    
    -- Calculate segment positions (bottom to top)
    segments = calculateStackedColumnSegments cfg.seriesColors colData.values scaleY baseline
  in
    E.g_
      []
      ([ E.text_
           [ E.attr "x" (show (x + barWidth / 2.0))
           , E.attr "y" (show (baseline + 15.0))
           , E.attr "text-anchor" "middle"
           , E.attr "font-size" "10"
           , E.attr "fill" "currentColor"
           , E.attr "fill-opacity" "0.7"
           ]
           [ E.text colData.category ]
       ] <> mapWithIndex (\_ seg ->
         E.rect_
           [ E.attr "x" (show x)
           , E.attr "y" (show seg.y)
           , E.attr "width" (show barWidth)
           , E.attr "height" (show seg.height)
           , E.attr "fill" seg.color
           , E.attr "rx" "2"
           , E.style "filter" ("drop-shadow(0 0 6px " <> seg.color <> "50)")
           ]
       ) segments)

-- | Calculate stacked column segment positions.
calculateStackedColumnSegments :: Array String -> Array Number -> (Number -> Number) -> Number -> Array { y :: Number, height :: Number, color :: String }
calculateStackedColumnSegments colors values scaleY baseline =
  let
    go :: { runningY :: Number, segments :: Array { y :: Number, height :: Number, color :: String } } -> 
          { idx :: Int, value :: Number } -> 
          { runningY :: Number, segments :: Array { y :: Number, height :: Number, color :: String } }
    go acc item =
      let
        height = scaleY item.value
        color = fromMaybe "#3B82F6" (index colors item.idx)
        y = acc.runningY - height
        segment = { y: y, height: height, color: color }
      in
        { runningY: y, segments: acc.segments <> [segment] }
    
    indexed = mapWithIndex (\idx v -> { idx: idx, value: v }) values
    result = foldl go { runningY: baseline, segments: [] } indexed
  in
    result.segments

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // rainfall chart
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Rainfall/distribution chart data.
-- |
-- | Shows two distributions (left and right) meeting at center.
type RainfallData =
  { leftValues :: Array Number   -- ^ Left distribution (e.g., Monthly)
  , rightValues :: Array Number  -- ^ Right distribution (e.g., Yearly)
  , leftLabel :: String
  , rightLabel :: String
  }

-- | Rainfall chart configuration.
type RainfallConfig =
  { title :: Maybe String
  , width :: Number
  , height :: Number
  , leftColor :: String
  , rightColor :: String
  , className :: String
  }

-- | Default rainfall configuration.
defaultRainfallConfig :: RainfallConfig
defaultRainfallConfig =
  { title: Nothing
  , width: 400.0
  , height: 200.0
  , leftColor: "#FBBF24"   -- Yellow/amber
  , rightColor: "#8B5CF6"  -- Purple
  , className: ""
  }

-- | Render a rainfall/distribution chart.
-- |
-- | Shows two distributions as fine lines tapering to/from center.
rainfallChart :: forall msg. RainfallConfig -> RainfallData -> E.Element msg
rainfallChart cfg rdata =
  let
    viewBox = "0 0 " <> show cfg.width <> " " <> show cfg.height
    padding = 20.0
    centerX = cfg.width / 2.0
    plotHeight = cfg.height - padding * 2.0
    halfWidth = (cfg.width - padding * 2.0) / 2.0
    
    numLeftLines = length rdata.leftValues
    numRightLines = length rdata.rightValues
    
    maxLeft = arrayMax rdata.leftValues
    maxRight = arrayMax rdata.rightValues
  in
    E.svg_
      [ E.attr "viewBox" viewBox
      , E.class_ ("w-full h-full " <> cfg.className)
      , E.attr "preserveAspectRatio" "xMidYMid meet"
      ]
      [ -- Left distribution (grows left from center)
        E.g_
          [ E.class_ "rainfall-left" ]
          (mapWithIndex (renderRainfallLine cfg.leftColor centerX halfWidth plotHeight padding numLeftLines maxLeft true) rdata.leftValues)
      
      -- Right distribution (grows right from center)
      , E.g_
          [ E.class_ "rainfall-right" ]
          (mapWithIndex (renderRainfallLine cfg.rightColor centerX halfWidth plotHeight padding numRightLines maxRight false) rdata.rightValues)
      
      -- Labels
      , E.text_
          [ E.attr "x" (show (padding + 10.0))
          , E.attr "y" (show (cfg.height - 5.0))
          , E.attr "font-size" "10"
          , E.attr "fill" cfg.leftColor
          ]
          [ E.text rdata.leftLabel ]
      , E.text_
          [ E.attr "x" (show (cfg.width - padding - 10.0))
          , E.attr "y" (show (cfg.height - 5.0))
          , E.attr "text-anchor" "end"
          , E.attr "font-size" "10"
          , E.attr "fill" cfg.rightColor
          ]
          [ E.text rdata.rightLabel ]
      ]

-- | Render a single rainfall distribution line.
renderRainfallLine :: forall msg.
  String ->
  Number ->
  Number ->
  Number ->
  Number ->
  Int ->
  Number ->
  Boolean ->
  Int ->
  Number ->
  E.Element msg
renderRainfallLine color centerX halfWidth plotHeight padding numLines maxVal isLeft idx value =
  let
    -- Y position distributed vertically
    divisor = Math.max 1.0 (toNumber (numLines - 1))
    y = padding + (toNumber idx / divisor) * plotHeight
    
    -- Line length based on value
    lineLength = if maxVal == 0.0 then 0.0 else (value / maxVal) * halfWidth
    
    -- X positions
    x1 = if isLeft then centerX else centerX
    x2 = if isLeft then centerX - lineLength else centerX + lineLength
  in
    E.line_
      [ E.attr "x1" (show x1)
      , E.attr "y1" (show y)
      , E.attr "x2" (show x2)
      , E.attr "y2" (show y)
      , E.attr "stroke" color
      , E.attr "stroke-width" "1.5"
      , E.attr "stroke-opacity" "0.7"
      , E.style "filter" ("drop-shadow(0 0 3px " <> color <> "60)")
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // dual axis chart
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Dual axis chart data.
-- |
-- | Shows line data on primary Y-axis and column data on secondary Y-axis.
type DualAxisData =
  { categories :: Array String
  , lineSeries :: Array Number   -- ^ Values for line (primary Y-axis)
  , columnSeries :: Array Number -- ^ Values for columns (secondary Y-axis)
  , lineLabel :: String
  , columnLabel :: String
  }

-- | Dual axis chart configuration.
type DualAxisConfig =
  { title :: Maybe String
  , width :: Number
  , height :: Number
  , lineColor :: String
  , columnColor :: String
  , className :: String
  }

-- | Default dual axis configuration.
defaultDualAxisConfig :: DualAxisConfig
defaultDualAxisConfig =
  { title: Nothing
  , width: 400.0
  , height: 200.0
  , lineColor: "#3B82F6"   -- Blue
  , columnColor: "#22C55E" -- Green
  , className: ""
  }

-- | Render a dual axis chart (line + column).
-- |
-- | Combines line chart and column chart on same axes.
dualAxisChart :: forall msg. DualAxisConfig -> DualAxisData -> E.Element msg
dualAxisChart cfg ddata =
  let
    viewBox = "0 0 " <> show cfg.width <> " " <> show cfg.height
    padding = 50.0
    plotWidth = cfg.width - padding * 2.0
    plotHeight = cfg.height - padding * 2.0
    
    numPoints = length ddata.categories
    columnWidth = if numPoints <= 0 then 20.0 else (plotWidth / toNumber numPoints) * 0.6
    
    -- Scale for columns
    maxColumn = arrayMax ddata.columnSeries
    scaleColumn :: Number -> Number
    scaleColumn v = if maxColumn == 0.0 then 0.0 else (v / maxColumn) * plotHeight
    
    -- Scale for line
    maxLine = arrayMax ddata.lineSeries
    minLine = arrayMin ddata.lineSeries
    lineRange = if maxLine - minLine == 0.0 then 1.0 else maxLine - minLine
    scaleLine :: Number -> Number
    scaleLine v = padding + plotHeight - ((v - minLine) / lineRange) * plotHeight
    
    baseline = padding + plotHeight
  in
    E.svg_
      [ E.attr "viewBox" viewBox
      , E.class_ ("w-full h-full " <> cfg.className)
      , E.attr "preserveAspectRatio" "xMidYMid meet"
      ]
      [ -- Columns (render first, behind line)
        E.g_
          [ E.class_ "dual-columns" ]
          (mapWithIndex (renderDualColumn cfg padding columnWidth plotWidth baseline scaleColumn numPoints) ddata.columnSeries)
      
      -- Line
      , E.path_
          [ E.attr "d" (generateDualLinePath padding plotWidth scaleLine numPoints ddata.lineSeries)
          , E.attr "fill" "none"
          , E.attr "stroke" cfg.lineColor
          , E.attr "stroke-width" "2"
          , E.style "filter" ("drop-shadow(0 0 6px " <> cfg.lineColor <> "80)")
          ]
      
      -- Line points
      , E.g_
          [ E.class_ "dual-line-points" ]
          (mapWithIndex (renderDualLinePoint cfg padding plotWidth scaleLine numPoints) ddata.lineSeries)
      ]

-- | Render a column in dual axis chart.
renderDualColumn :: forall msg.
  DualAxisConfig ->
  Number ->
  Number ->
  Number ->
  Number ->
  (Number -> Number) ->
  Int ->
  Int ->
  Number ->
  E.Element msg
renderDualColumn cfg padding columnWidth plotWidth baseline scaleColumn numPoints idx value =
  let
    divisor = Math.max 1.0 (toNumber (numPoints - 1))
    x = padding + (toNumber idx / divisor) * plotWidth - columnWidth / 2.0
    height = scaleColumn value
    y = baseline - height
  in
    E.rect_
      [ E.attr "x" (show x)
      , E.attr "y" (show y)
      , E.attr "width" (show columnWidth)
      , E.attr "height" (show height)
      , E.attr "fill" cfg.columnColor
      , E.attr "fill-opacity" "0.7"
      , E.attr "rx" "2"
      , E.style "filter" ("drop-shadow(0 0 6px " <> cfg.columnColor <> "40)")
      ]

-- | Generate path data for dual axis line.
generateDualLinePath :: Number -> Number -> (Number -> Number) -> Int -> Array Number -> String
generateDualLinePath padding plotWidth scaleLine numPoints values =
  let
    divisor = Math.max 1.0 (toNumber (numPoints - 1))
    pathParts = mapWithIndex (\idx v ->
      let 
        x = padding + (toNumber idx / divisor) * plotWidth
        y = scaleLine v
      in 
        if idx == 0
          then "M " <> show x <> " " <> show y
          else "L " <> show x <> " " <> show y
    ) values
  in
    foldl (\acc part -> acc <> " " <> part) "" pathParts

-- | Render a point on the dual axis line.
renderDualLinePoint :: forall msg.
  DualAxisConfig ->
  Number ->
  Number ->
  (Number -> Number) ->
  Int ->
  Int ->
  Number ->
  E.Element msg
renderDualLinePoint cfg padding plotWidth scaleLine numPoints idx value =
  let
    divisor = Math.max 1.0 (toNumber (numPoints - 1))
    x = padding + (toNumber idx / divisor) * plotWidth
    y = scaleLine value
  in
    E.circle_
      [ E.attr "cx" (show x)
      , E.attr "cy" (show y)
      , E.attr "r" "4"
      , E.attr "fill" cfg.lineColor
      , E.style "filter" ("drop-shadow(0 0 4px " <> cfg.lineColor <> "80)")
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // math helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get minimum value from array.
arrayMin :: Array Number -> Number
arrayMin arr = case index arr 0 of
  Nothing -> 0.0
  Just first -> foldl Math.min first arr

-- | Get maximum value from array.
arrayMax :: Array Number -> Number
arrayMax arr = case index arr 0 of
  Nothing -> 0.0
  Just first -> foldl Math.max first arr
