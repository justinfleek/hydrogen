-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // hydrogen // barchart
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Bar/Column chart component
-- |
-- | SVG-based bar charts with multiple variants and interactivity.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Chart.BarChart as BarChart
-- |
-- | -- Simple vertical bar chart
-- | BarChart.barChart
-- |   { data: [ { label: "Jan", value: 100.0 }
-- |           , { label: "Feb", value: 150.0 }
-- |           , { label: "Mar", value: 120.0 }
-- |           ]
-- |   , width: 400
-- |   , height: 300
-- |   }
-- |
-- | -- Horizontal bar chart
-- | BarChart.barChartWithProps
-- |   defaultProps
-- |     { data = myData
-- |     , orientation = Horizontal
-- |     }
-- |
-- | -- Stacked bar chart
-- | BarChart.stackedBarChart
-- |   { data: [ { label: "Q1", values: [30.0, 20.0, 10.0] }
-- |           , { label: "Q2", values: [40.0, 25.0, 15.0] }
-- |           ]
-- |   , colors: ["#3b82f6", "#10b981", "#f59e0b"]
-- |   , width: 400
-- |   , height: 300
-- |   }
-- |
-- | -- Grouped bar chart
-- | BarChart.groupedBarChart
-- |   { data: groupedData
-- |   , colors: seriesColors
-- |   , width: 400
-- |   , height: 300
-- |   }
-- | ```
module Hydrogen.Chart.BarChart
  ( -- * Simple Bar Chart
    barChart
  , barChartWithProps
  , BarChartConfig
  , BarChartProps
  , defaultProps
    -- * Stacked Bar Chart
  , stackedBarChart
  , StackedBarConfig
    -- * Grouped Bar Chart
  , groupedBarChart
  , GroupedBarConfig
    -- * Data Types
  , BarDataPoint
  , StackedDataPoint
  , GroupedDataPoint
    -- * Orientation
  , Orientation(Vertical, Horizontal)
    -- * Prop Builders
  , orientation
  , showGrid
  , showTooltip
  , showLegend
  , showAxisLabels
  , animated
  , barColors
  , className
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl, maximum, sum)
import Data.Int (toNumber)
import Data.Maybe (Maybe, fromMaybe)
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Hydrogen.UI.Core (cls, svgNS, svgCls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // data types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Single bar data point
type BarDataPoint =
  { label :: String
  , value :: Number
  }

-- | Stacked bar data point (multiple values per bar)
type StackedDataPoint =
  { label :: String
  , values :: Array Number
  }

-- | Grouped bar data point (same as stacked, different rendering)
type GroupedDataPoint =
  { label :: String
  , values :: Array Number
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // orientation
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Bar chart orientation
data Orientation
  = Vertical    -- ^ Columns (bars go up)
  | Horizontal  -- ^ Bars (bars go right)

derive instance eqOrientation :: Eq Orientation

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // config
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Basic bar chart configuration
type BarChartConfig =
  { data :: Array BarDataPoint
  , width :: Int
  , height :: Int
  }

-- | Full bar chart properties
type BarChartProps =
  { data :: Array BarDataPoint
  , width :: Int
  , height :: Int
  , orientation :: Orientation
  , showGrid :: Boolean
  , showTooltip :: Boolean
  , showLegend :: Boolean
  , showAxisLabels :: Boolean
  , animated :: Boolean
  , barColors :: Array String
  , barRadius :: Number
  , barGap :: Number
  , padding :: { top :: Number, right :: Number, bottom :: Number, left :: Number }
  , className :: String
  }

-- | Default bar chart properties
defaultProps :: BarChartProps
defaultProps =
  { data: []
  , width: 400
  , height: 300
  , orientation: Vertical
  , showGrid: true
  , showTooltip: true
  , showLegend: false
  , showAxisLabels: true
  , animated: true
  , barColors: ["#3b82f6", "#10b981", "#f59e0b", "#ef4444", "#8b5cf6", "#ec4899"]
  , barRadius: 4.0
  , barGap: 0.2  -- Gap as fraction of bar width
  , padding: { top: 20.0, right: 20.0, bottom: 40.0, left: 50.0 }
  , className: ""
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

type BarChartProp = BarChartProps -> BarChartProps

-- | Set bar chart orientation
orientation :: Orientation -> BarChartProp
orientation o props = props { orientation = o }

-- | Enable/disable grid lines
showGrid :: Boolean -> BarChartProp
showGrid v props = props { showGrid = v }

-- | Enable/disable tooltips
showTooltip :: Boolean -> BarChartProp
showTooltip v props = props { showTooltip = v }

-- | Enable/disable legend
showLegend :: Boolean -> BarChartProp
showLegend v props = props { showLegend = v }

-- | Enable/disable axis labels
showAxisLabels :: Boolean -> BarChartProp
showAxisLabels v props = props { showAxisLabels = v }

-- | Enable/disable animation
animated :: Boolean -> BarChartProp
animated v props = props { animated = v }

-- | Set bar colors
barColors :: Array String -> BarChartProp
barColors cs props = props { barColors = cs }

-- | Add custom class
className :: String -> BarChartProp
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // simple bar chart
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Simple bar chart with basic config
barChart :: forall w i. BarChartConfig -> HH.HTML w i
barChart config = barChartWithProps
  defaultProps
    { data = config.data
    , width = config.width
    , height = config.height
    }

-- | Bar chart with full props
barChartWithProps :: forall w i. BarChartProps -> HH.HTML w i
barChartWithProps props =
  let
    chartWidth = toNumber props.width - props.padding.left - props.padding.right
    chartHeight = toNumber props.height - props.padding.top - props.padding.bottom
    dataLen = Array.length props.data
    maxVal = fromMaybe 1.0 (maximum (map _.value props.data))
    
    -- Bar dimensions
    barWidth = if dataLen > 0 
               then chartWidth / toNumber dataLen * (1.0 - props.barGap)
               else 0.0
    barSpacing = chartWidth / toNumber dataLen
    
    -- Get color for bar
    getColor idx = fromMaybe "#3b82f6" (Array.index props.barColors (idx `mod` Array.length props.barColors))
    
    -- Generate bars
    bars = Array.mapWithIndex (\idx point ->
      let
        barHeight = (point.value / maxVal) * chartHeight
        x = props.padding.left + (toNumber idx * barSpacing) + (barSpacing - barWidth) / 2.0
        y = props.padding.top + chartHeight - barHeight
        color = getColor idx
        animStyle = if props.animated
                    then "transition: height 0.3s ease-out, y 0.3s ease-out;"
                    else ""
      in
        HH.elementNS svgNS (HH.ElemName "g")
          [ svgCls [ "bar-group cursor-pointer" ]
          , HP.attr (HH.AttrName "data-index") (show idx)
          ]
          [ -- Bar rectangle
            HH.elementNS svgNS (HH.ElemName "rect")
              [ HP.attr (HH.AttrName "x") (show x)
              , HP.attr (HH.AttrName "y") (show y)
              , HP.attr (HH.AttrName "width") (show barWidth)
              , HP.attr (HH.AttrName "height") (show barHeight)
              , HP.attr (HH.AttrName "rx") (show props.barRadius)
              , HP.attr (HH.AttrName "fill") color
              , HP.attr (HH.AttrName "style") animStyle
              , svgCls [ "hover:opacity-80 transition-opacity" ]
              ]
              []
          , -- Tooltip trigger area (invisible larger rect for hover)
            HH.elementNS svgNS (HH.ElemName "title")
              []
              [ HH.text (point.label <> ": " <> show point.value) ]
          ]
    ) props.data

    -- Grid lines
    gridLines = if props.showGrid
      then
        let
          numLines = 5
          lineSpacing = chartHeight / toNumber numLines
        in
          Array.mapWithIndex (\idx _ ->
            let y = props.padding.top + (toNumber idx * lineSpacing)
            in HH.elementNS svgNS (HH.ElemName "line")
                [ HP.attr (HH.AttrName "x1") (show props.padding.left)
                , HP.attr (HH.AttrName "y1") (show y)
                , HP.attr (HH.AttrName "x2") (show (props.padding.left + chartWidth))
                , HP.attr (HH.AttrName "y2") (show y)
                , svgCls [ "stroke-muted-foreground/20" ]
                , HP.attr (HH.AttrName "stroke-dasharray") "4,4"
                ]
                []
          ) (Array.replicate (numLines + 1) unit)
      else []

    -- Y-axis labels
    yAxisLabels = if props.showAxisLabels
      then
        let
          numLabels = 5
          labelSpacing = chartHeight / toNumber numLabels
          valueSpacing = maxVal / toNumber numLabels
        in
          Array.mapWithIndex (\idx _ ->
            let 
              y = props.padding.top + (toNumber (numLabels - idx) * labelSpacing)
              val = toNumber idx * valueSpacing
            in HH.elementNS svgNS (HH.ElemName "text")
                [ HP.attr (HH.AttrName "x") (show (props.padding.left - 8.0))
                , HP.attr (HH.AttrName "y") (show (y + 4.0))
                , HP.attr (HH.AttrName "text-anchor") "end"
                , svgCls [ "fill-muted-foreground text-xs" ]
                ]
                [ HH.text (formatNumber val) ]
          ) (Array.replicate (numLabels + 1) unit)
      else []

    -- X-axis labels
    xAxisLabels = if props.showAxisLabels
      then
        Array.mapWithIndex (\idx point ->
          let 
            x = props.padding.left + (toNumber idx * barSpacing) + barSpacing / 2.0
            y = props.padding.top + chartHeight + 20.0
          in HH.elementNS svgNS (HH.ElemName "text")
              [ HP.attr (HH.AttrName "x") (show x)
              , HP.attr (HH.AttrName "y") (show y)
              , HP.attr (HH.AttrName "text-anchor") "middle"
              , svgCls [ "fill-muted-foreground text-xs" ]
              ]
              [ HH.text point.label ]
        ) props.data
      else []
  in
    HH.div
      [ cls [ "relative", props.className ] ]
      [ HH.elementNS svgNS (HH.ElemName "svg")
          [ svgCls [ "w-full h-auto" ]
          , HP.attr (HH.AttrName "viewBox") ("0 0 " <> show props.width <> " " <> show props.height)
          , HP.attr (HH.AttrName "preserveAspectRatio") "xMidYMid meet"
          ]
          (gridLines <> yAxisLabels <> bars <> xAxisLabels)
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // stacked bar chart
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Stacked bar chart configuration
type StackedBarConfig =
  { data :: Array StackedDataPoint
  , colors :: Array String
  , width :: Int
  , height :: Int
  }

-- | Stacked bar chart
stackedBarChart :: forall w i. StackedBarConfig -> HH.HTML w i
stackedBarChart config =
  let
    props = defaultProps
    chartWidth = toNumber config.width - props.padding.left - props.padding.right
    chartHeight = toNumber config.height - props.padding.top - props.padding.bottom
    dataLen = Array.length config.data
    
    -- Calculate max stacked value
    maxVal = fromMaybe 1.0 (maximum (map (\d -> sum d.values) config.data))
    
    barWidth = if dataLen > 0 
               then chartWidth / toNumber dataLen * (1.0 - props.barGap)
               else 0.0
    barSpacing = chartWidth / toNumber dataLen
    
    getColor idx = fromMaybe "#3b82f6" (Array.index config.colors (idx `mod` Array.length config.colors))
    
    -- Generate stacked bars
    bars = Array.mapWithIndex (\barIdx point ->
      let
        x = props.padding.left + (toNumber barIdx * barSpacing) + (barSpacing - barWidth) / 2.0
        -- Build stack segments
        segments = foldl (\acc segData ->
          let
            segIdx = acc.idx
            segValue = segData
            segHeight = (segValue / maxVal) * chartHeight
            y = acc.currentY - segHeight
            color = getColor segIdx
          in
            { idx: segIdx + 1
            , currentY: y
            , elements: acc.elements <> 
                [ HH.elementNS svgNS (HH.ElemName "rect")
                    [ HP.attr (HH.AttrName "x") (show x)
                    , HP.attr (HH.AttrName "y") (show y)
                    , HP.attr (HH.AttrName "width") (show barWidth)
                    , HP.attr (HH.AttrName "height") (show segHeight)
                    , HP.attr (HH.AttrName "fill") color
                    , svgCls [ "hover:opacity-80 transition-opacity" ]
                    ]
                    [ HH.elementNS svgNS (HH.ElemName "title")
                        []
                        [ HH.text (point.label <> " [" <> show segIdx <> "]: " <> show segValue) ]
                    ]
                ]
            }
        ) { idx: 0, currentY: props.padding.top + chartHeight, elements: [] } point.values
      in
        HH.elementNS svgNS (HH.ElemName "g")
          [ svgCls [ "stacked-bar-group" ] ]
          segments.elements
    ) config.data

    -- X-axis labels
    xAxisLabels = Array.mapWithIndex (\idx point ->
      let 
        x = props.padding.left + (toNumber idx * barSpacing) + barSpacing / 2.0
        y = props.padding.top + chartHeight + 20.0
      in HH.elementNS svgNS (HH.ElemName "text")
          [ HP.attr (HH.AttrName "x") (show x)
          , HP.attr (HH.AttrName "y") (show y)
          , HP.attr (HH.AttrName "text-anchor") "middle"
          , svgCls [ "fill-muted-foreground text-xs" ]
          ]
          [ HH.text point.label ]
    ) config.data

    -- Legend
    legend = Array.mapWithIndex (\idx color ->
      HH.div
        [ cls [ "flex items-center gap-2" ] ]
        [ HH.div
            [ cls [ "w-3 h-3 rounded-sm" ]
            , HP.style ("background-color: " <> color)
            ]
            []
        , HH.span
            [ cls [ "text-xs text-muted-foreground" ] ]
            [ HH.text ("Series " <> show (idx + 1)) ]
        ]
    ) config.colors
  in
    HH.div
      [ cls [ "relative" ] ]
      [ HH.elementNS svgNS (HH.ElemName "svg")
          [ svgCls [ "w-full h-auto" ]
          , HP.attr (HH.AttrName "viewBox") ("0 0 " <> show config.width <> " " <> show config.height)
          , HP.attr (HH.AttrName "preserveAspectRatio") "xMidYMid meet"
          ]
          (bars <> xAxisLabels)
      , HH.div
          [ cls [ "flex flex-wrap gap-4 justify-center mt-4" ] ]
          legend
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // grouped bar chart
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Grouped bar chart configuration
type GroupedBarConfig =
  { data :: Array GroupedDataPoint
  , colors :: Array String
  , width :: Int
  , height :: Int
  }

-- | Grouped bar chart
groupedBarChart :: forall w i. GroupedBarConfig -> HH.HTML w i
groupedBarChart config =
  let
    props = defaultProps
    chartWidth = toNumber config.width - props.padding.left - props.padding.right
    chartHeight = toNumber config.height - props.padding.top - props.padding.bottom
    dataLen = Array.length config.data
    numSeries = fromMaybe 0 (maximum (map (\d -> Array.length d.values) config.data))
    
    -- Calculate max value across all series
    maxVal = fromMaybe 1.0 (maximum (config.data >>= _.values))
    
    groupWidth = if dataLen > 0 
                 then chartWidth / toNumber dataLen * (1.0 - props.barGap)
                 else 0.0
    groupSpacing = chartWidth / toNumber dataLen
    barWidth = if numSeries > 0 then groupWidth / toNumber numSeries * 0.9 else 0.0
    barGapInGroup = if numSeries > 0 then groupWidth / toNumber numSeries * 0.1 else 0.0
    
    getColor idx = fromMaybe "#3b82f6" (Array.index config.colors (idx `mod` Array.length config.colors))
    
    -- Generate grouped bars
    bars = Array.mapWithIndex (\groupIdx point ->
      let
        groupX = props.padding.left + (toNumber groupIdx * groupSpacing) + (groupSpacing - groupWidth) / 2.0
        
        groupBars = Array.mapWithIndex (\barIdx value ->
          let
            x = groupX + (toNumber barIdx * (barWidth + barGapInGroup))
            barHeight = (value / maxVal) * chartHeight
            y = props.padding.top + chartHeight - barHeight
            color = getColor barIdx
          in
            HH.elementNS svgNS (HH.ElemName "rect")
              [ HP.attr (HH.AttrName "x") (show x)
              , HP.attr (HH.AttrName "y") (show y)
              , HP.attr (HH.AttrName "width") (show barWidth)
              , HP.attr (HH.AttrName "height") (show barHeight)
              , HP.attr (HH.AttrName "rx") (show props.barRadius)
              , HP.attr (HH.AttrName "fill") color
              , svgCls [ "hover:opacity-80 transition-opacity" ]
              ]
              [ HH.elementNS svgNS (HH.ElemName "title")
                  []
                  [ HH.text (point.label <> " [" <> show barIdx <> "]: " <> show value) ]
              ]
        ) point.values
      in
        HH.elementNS svgNS (HH.ElemName "g")
          [ svgCls [ "grouped-bar-group" ] ]
          groupBars
    ) config.data

    -- X-axis labels
    xAxisLabels = Array.mapWithIndex (\idx point ->
      let 
        x = props.padding.left + (toNumber idx * groupSpacing) + groupSpacing / 2.0
        y = props.padding.top + chartHeight + 20.0
      in HH.elementNS svgNS (HH.ElemName "text")
          [ HP.attr (HH.AttrName "x") (show x)
          , HP.attr (HH.AttrName "y") (show y)
          , HP.attr (HH.AttrName "text-anchor") "middle"
          , svgCls [ "fill-muted-foreground text-xs" ]
          ]
          [ HH.text point.label ]
    ) config.data

    -- Legend
    legend = Array.mapWithIndex (\idx color ->
      HH.div
        [ cls [ "flex items-center gap-2" ] ]
        [ HH.div
            [ cls [ "w-3 h-3 rounded-sm" ]
            , HP.style ("background-color: " <> color)
            ]
            []
        , HH.span
            [ cls [ "text-xs text-muted-foreground" ] ]
            [ HH.text ("Series " <> show (idx + 1)) ]
        ]
    ) config.colors
  in
    HH.div
      [ cls [ "relative" ] ]
      [ HH.elementNS svgNS (HH.ElemName "svg")
          [ svgCls [ "w-full h-auto" ]
          , HP.attr (HH.AttrName "viewBox") ("0 0 " <> show config.width <> " " <> show config.height)
          , HP.attr (HH.AttrName "preserveAspectRatio") "xMidYMid meet"
          ]
          (bars <> xAxisLabels)
      , HH.div
          [ cls [ "flex flex-wrap gap-4 justify-center mt-4" ] ]
          legend
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Format number for display
formatNumber :: Number -> String
formatNumber n =
  if n >= 1000000.0 then show (n / 1000000.0) <> "M"
  else if n >= 1000.0 then show (n / 1000.0) <> "K"
  else show n
