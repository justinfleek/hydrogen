-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                      // hydrogen // linechart
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Line/Area chart component
-- |
-- | SVG-based line and area charts with smooth curves, tooltips, and animations.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Chart.LineChart as LineChart
-- |
-- | -- Simple line chart
-- | LineChart.lineChart
-- |   { data: [ { x: 0.0, y: 10.0 }
-- |           , { x: 1.0, y: 25.0 }
-- |           , { x: 2.0, y: 15.0 }
-- |           ]
-- |   , width: 400
-- |   , height: 300
-- |   }
-- |
-- | -- Area chart with gradient fill
-- | LineChart.areaChart
-- |   { data: values
-- |   , width: 400
-- |   , height: 300
-- |   , color: "#3b82f6"
-- |   }
-- |
-- | -- Multi-series line chart
-- | LineChart.multiLineChart
-- |   { series: [ { label: "Sales", data: salesData, color: "#3b82f6" }
-- |             , { label: "Revenue", data: revenueData, color: "#10b981" }
-- |             ]
-- |   , width: 400
-- |   , height: 300
-- |   }
-- |
-- | -- With Bezier curves
-- | LineChart.lineChartWithProps
-- |   defaultProps
-- |     { data = myData
-- |     , curveType = Bezier
-- |     , showDots = true
-- |     }
-- | ```
module Hydrogen.Chart.LineChart
  ( -- * Line Chart
    lineChart
  , lineChartWithProps
  , LineChartConfig
  , LineChartProps
  , defaultProps
    -- * Area Chart
  , areaChart
  , AreaChartConfig
    -- * Multi-Series
  , multiLineChart
  , MultiLineConfig
  , Series
    -- * Data Types
  , DataPoint
  , LabeledDataPoint
    -- * Curve Types
  , CurveType(..)
    -- * Prop Builders
  , curveType
  , showDots
  , showGrid
  , showTooltip
  , showLegend
  , showCrosshair
  , showAxisLabels
  , animated
  , strokeColor
  , fillColor
  , strokeWidth
  , dotRadius
  , className
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl, maximum, minimum)
import Data.Int (toNumber)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Number (abs)
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Hydrogen.UI.Core (cls, svgNS, svgCls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // data types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Simple data point with x and y values
type DataPoint =
  { x :: Number
  , y :: Number
  }

-- | Data point with optional label
type LabeledDataPoint =
  { x :: Number
  , y :: Number
  , label :: Maybe String
  }

-- | Series definition for multi-line charts
type Series =
  { label :: String
  , data :: Array DataPoint
  , color :: String
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // curve types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Line interpolation type
data CurveType
  = Linear      -- ^ Straight lines between points
  | Bezier      -- ^ Smooth cubic bezier curves
  | Step        -- ^ Step function (horizontal then vertical)
  | StepBefore  -- ^ Step function (vertical then horizontal)

derive instance eqCurveType :: Eq CurveType

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // config
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Basic line chart configuration
type LineChartConfig =
  { data :: Array DataPoint
  , width :: Int
  , height :: Int
  }

-- | Full line chart properties
type LineChartProps =
  { data :: Array DataPoint
  , width :: Int
  , height :: Int
  , curveType :: CurveType
  , showDots :: Boolean
  , showGrid :: Boolean
  , showTooltip :: Boolean
  , showLegend :: Boolean
  , showCrosshair :: Boolean
  , showAxisLabels :: Boolean
  , animated :: Boolean
  , strokeColor :: String
  , fillColor :: Maybe String
  , strokeWidth :: Number
  , dotRadius :: Number
  , padding :: { top :: Number, right :: Number, bottom :: Number, left :: Number }
  , className :: String
  }

-- | Default line chart properties
defaultProps :: LineChartProps
defaultProps =
  { data: []
  , width: 400
  , height: 300
  , curveType: Bezier
  , showDots: true
  , showGrid: true
  , showTooltip: true
  , showLegend: false
  , showCrosshair: false
  , showAxisLabels: true
  , animated: true
  , strokeColor: "#3b82f6"
  , fillColor: Nothing
  , strokeWidth: 2.0
  , dotRadius: 4.0
  , padding: { top: 20.0, right: 20.0, bottom: 40.0, left: 50.0 }
  , className: ""
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

type LineChartProp = LineChartProps -> LineChartProps

-- | Set curve interpolation type
curveType :: CurveType -> LineChartProp
curveType c props = props { curveType = c }

-- | Show/hide data point dots
showDots :: Boolean -> LineChartProp
showDots v props = props { showDots = v }

-- | Show/hide grid lines
showGrid :: Boolean -> LineChartProp
showGrid v props = props { showGrid = v }

-- | Show/hide tooltips
showTooltip :: Boolean -> LineChartProp
showTooltip v props = props { showTooltip = v }

-- | Show/hide legend
showLegend :: Boolean -> LineChartProp
showLegend v props = props { showLegend = v }

-- | Show/hide crosshair cursor
showCrosshair :: Boolean -> LineChartProp
showCrosshair v props = props { showCrosshair = v }

-- | Show/hide axis labels
showAxisLabels :: Boolean -> LineChartProp
showAxisLabels v props = props { showAxisLabels = v }

-- | Enable/disable animation
animated :: Boolean -> LineChartProp
animated v props = props { animated = v }

-- | Set line stroke color
strokeColor :: String -> LineChartProp
strokeColor c props = props { strokeColor = c }

-- | Set fill color (for area chart effect)
fillColor :: Maybe String -> LineChartProp
fillColor c props = props { fillColor = c }

-- | Set line stroke width
strokeWidth :: Number -> LineChartProp
strokeWidth w props = props { strokeWidth = w }

-- | Set data point dot radius
dotRadius :: Number -> LineChartProp
dotRadius r props = props { dotRadius = r }

-- | Add custom class
className :: String -> LineChartProp
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // line chart
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Simple line chart with basic config
lineChart :: forall w i. LineChartConfig -> HH.HTML w i
lineChart config = lineChartWithProps
  defaultProps
    { data = config.data
    , width = config.width
    , height = config.height
    }

-- | Line chart with full props
lineChartWithProps :: forall w i. LineChartProps -> HH.HTML w i
lineChartWithProps props =
  let
    chartWidth = toNumber props.width - props.padding.left - props.padding.right
    chartHeight = toNumber props.height - props.padding.top - props.padding.bottom
    
    -- Calculate data bounds
    xMin = fromMaybe 0.0 (minimum (map _.x props.data))
    xMax = fromMaybe 1.0 (maximum (map _.x props.data))
    yMin = fromMaybe 0.0 (minimum (map _.y props.data))
    yMax = fromMaybe 1.0 (maximum (map _.y props.data))
    
    xRange = if xMax == xMin then 1.0 else xMax - xMin
    yRange = if yMax == yMin then 1.0 else yMax - yMin
    
    -- Scale data points to chart coordinates
    scalePoint :: DataPoint -> { x :: Number, y :: Number }
    scalePoint p =
      { x: props.padding.left + ((p.x - xMin) / xRange) * chartWidth
      , y: props.padding.top + (1.0 - (p.y - yMin) / yRange) * chartHeight
      }
    
    scaledPoints = map scalePoint props.data
    
    -- Generate path based on curve type
    pathData = generatePath props.curveType scaledPoints
    
    -- Generate fill path if needed
    fillPathData = case props.fillColor of
      Just _ -> generateFillPath scaledPoints chartHeight props.padding.top
      Nothing -> ""
    
    -- Gradient definition for fill
    gradientDef = case props.fillColor of
      Just color ->
        [ HH.elementNS svgNS (HH.ElemName "defs")
            []
            [ HH.elementNS svgNS (HH.ElemName "linearGradient")
                [ HP.attr (HH.AttrName "id") "lineChartGradient"
                , HP.attr (HH.AttrName "x1") "0%"
                , HP.attr (HH.AttrName "y1") "0%"
                , HP.attr (HH.AttrName "x2") "0%"
                , HP.attr (HH.AttrName "y2") "100%"
                ]
                [ HH.elementNS svgNS (HH.ElemName "stop")
                    [ HP.attr (HH.AttrName "offset") "0%"
                    , HP.attr (HH.AttrName "stop-color") color
                    , HP.attr (HH.AttrName "stop-opacity") "0.3"
                    ]
                    []
                , HH.elementNS svgNS (HH.ElemName "stop")
                    [ HP.attr (HH.AttrName "offset") "100%"
                    , HP.attr (HH.AttrName "stop-color") color
                    , HP.attr (HH.AttrName "stop-opacity") "0.05"
                    ]
                    []
                ]
            ]
        ]
      Nothing -> []
    
    -- Fill area
    fillArea = case props.fillColor of
      Just _ ->
        [ HH.elementNS svgNS (HH.ElemName "path")
            [ HP.attr (HH.AttrName "d") fillPathData
            , HP.attr (HH.AttrName "fill") "url(#lineChartGradient)"
            , svgCls [ if props.animated then "animate-fade-in" else "" ]
            ]
            []
        ]
      Nothing -> []
    
    -- Line path
    linePath =
      [ HH.elementNS svgNS (HH.ElemName "path")
          [ HP.attr (HH.AttrName "d") pathData
          , HP.attr (HH.AttrName "fill") "none"
          , HP.attr (HH.AttrName "stroke") props.strokeColor
          , HP.attr (HH.AttrName "stroke-width") (show props.strokeWidth)
          , HP.attr (HH.AttrName "stroke-linecap") "round"
          , HP.attr (HH.AttrName "stroke-linejoin") "round"
          , svgCls [ if props.animated then "animate-draw-line" else "" ]
          ]
          []
      ]
    
    -- Data point dots
    dots = if props.showDots
      then map (\p ->
        HH.elementNS svgNS (HH.ElemName "circle")
          [ HP.attr (HH.AttrName "cx") (show p.x)
          , HP.attr (HH.AttrName "cy") (show p.y)
          , HP.attr (HH.AttrName "r") (show props.dotRadius)
          , HP.attr (HH.AttrName "fill") props.strokeColor
          , svgCls [ "cursor-pointer hover:r-6 transition-all" ]
          ]
          []
      ) scaledPoints
      else []
    
    -- Grid lines
    gridLines = if props.showGrid
      then
        let
          numHLines = 5
          numVLines = 5
          hLineSpacing = chartHeight / toNumber numHLines
          vLineSpacing = chartWidth / toNumber numVLines
          
          hLines = Array.mapWithIndex (\idx _ ->
            let y = props.padding.top + (toNumber idx * hLineSpacing)
            in HH.elementNS svgNS (HH.ElemName "line")
                [ HP.attr (HH.AttrName "x1") (show props.padding.left)
                , HP.attr (HH.AttrName "y1") (show y)
                , HP.attr (HH.AttrName "x2") (show (props.padding.left + chartWidth))
                , HP.attr (HH.AttrName "y2") (show y)
                , svgCls [ "stroke-muted-foreground/20" ]
                , HP.attr (HH.AttrName "stroke-dasharray") "4,4"
                ]
                []
          ) (Array.replicate (numHLines + 1) unit)
          
          vLines = Array.mapWithIndex (\idx _ ->
            let x = props.padding.left + (toNumber idx * vLineSpacing)
            in HH.elementNS svgNS (HH.ElemName "line")
                [ HP.attr (HH.AttrName "x1") (show x)
                , HP.attr (HH.AttrName "y1") (show props.padding.top)
                , HP.attr (HH.AttrName "x2") (show x)
                , HP.attr (HH.AttrName "y2") (show (props.padding.top + chartHeight))
                , svgCls [ "stroke-muted-foreground/20" ]
                , HP.attr (HH.AttrName "stroke-dasharray") "4,4"
                ]
                []
          ) (Array.replicate (numVLines + 1) unit)
        in
          hLines <> vLines
      else []
    
    -- Y-axis labels
    yAxisLabels = if props.showAxisLabels
      then
        let
          numLabels = 5
          labelSpacing = chartHeight / toNumber numLabels
          valueSpacing = yRange / toNumber numLabels
        in
          Array.mapWithIndex (\idx _ ->
            let 
              y = props.padding.top + (toNumber (numLabels - idx) * labelSpacing)
              val = yMin + (toNumber idx * valueSpacing)
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
        let
          numLabels = 5
          labelSpacing = chartWidth / toNumber numLabels
          valueSpacing = xRange / toNumber numLabels
        in
          Array.mapWithIndex (\idx _ ->
            let 
              x = props.padding.left + (toNumber idx * labelSpacing)
              val = xMin + (toNumber idx * valueSpacing)
            in HH.elementNS svgNS (HH.ElemName "text")
                [ HP.attr (HH.AttrName "x") (show x)
                , HP.attr (HH.AttrName "y") (show (props.padding.top + chartHeight + 20.0))
                , HP.attr (HH.AttrName "text-anchor") "middle"
                , svgCls [ "fill-muted-foreground text-xs" ]
                ]
                [ HH.text (formatNumber val) ]
          ) (Array.replicate (numLabels + 1) unit)
      else []
  in
    HH.div
      [ cls [ "relative", props.className ] ]
      [ HH.elementNS svgNS (HH.ElemName "svg")
          [ svgCls [ "w-full h-auto" ]
          , HP.attr (HH.AttrName "viewBox") ("0 0 " <> show props.width <> " " <> show props.height)
          , HP.attr (HH.AttrName "preserveAspectRatio") "xMidYMid meet"
          ]
          (gradientDef <> gridLines <> yAxisLabels <> xAxisLabels <> fillArea <> linePath <> dots)
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // area chart
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Area chart configuration
type AreaChartConfig =
  { data :: Array DataPoint
  , width :: Int
  , height :: Int
  , color :: String
  }

-- | Area chart (line chart with fill)
areaChart :: forall w i. AreaChartConfig -> HH.HTML w i
areaChart config = lineChartWithProps
  defaultProps
    { data = config.data
    , width = config.width
    , height = config.height
    , strokeColor = config.color
    , fillColor = Just config.color
    }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // multi-line chart
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Multi-series line chart configuration
type MultiLineConfig =
  { series :: Array Series
  , width :: Int
  , height :: Int
  }

-- | Multi-series line chart
multiLineChart :: forall w i. MultiLineConfig -> HH.HTML w i
multiLineChart config =
  let
    props = defaultProps
    chartWidth = toNumber config.width - props.padding.left - props.padding.right
    chartHeight = toNumber config.height - props.padding.top - props.padding.bottom
    
    -- Calculate global data bounds across all series
    allPoints = config.series >>= _.data
    xMin = fromMaybe 0.0 (minimum (map _.x allPoints))
    xMax = fromMaybe 1.0 (maximum (map _.x allPoints))
    yMin = fromMaybe 0.0 (minimum (map _.y allPoints))
    yMax = fromMaybe 1.0 (maximum (map _.y allPoints))
    
    xRange = if xMax == xMin then 1.0 else xMax - xMin
    yRange = if yMax == yMin then 1.0 else yMax - yMin
    
    -- Scale function
    scalePoint :: DataPoint -> { x :: Number, y :: Number }
    scalePoint p =
      { x: props.padding.left + ((p.x - xMin) / xRange) * chartWidth
      , y: props.padding.top + (1.0 - (p.y - yMin) / yRange) * chartHeight
      }
    
    -- Generate lines for each series
    seriesLines = map (\s ->
      let
        scaledPoints = map scalePoint s.data
        pathData = generatePath props.curveType scaledPoints
      in
        HH.elementNS svgNS (HH.ElemName "g")
          [ svgCls [ "series-line" ] ]
          [ HH.elementNS svgNS (HH.ElemName "path")
              [ HP.attr (HH.AttrName "d") pathData
              , HP.attr (HH.AttrName "fill") "none"
              , HP.attr (HH.AttrName "stroke") s.color
              , HP.attr (HH.AttrName "stroke-width") (show props.strokeWidth)
              , HP.attr (HH.AttrName "stroke-linecap") "round"
              , HP.attr (HH.AttrName "stroke-linejoin") "round"
              ]
              []
          ]
    ) config.series
    
    -- Grid lines
    gridLines =
      let
        numHLines = 5
        hLineSpacing = chartHeight / toNumber numHLines
      in
        Array.mapWithIndex (\idx _ ->
          let y = props.padding.top + (toNumber idx * hLineSpacing)
          in HH.elementNS svgNS (HH.ElemName "line")
              [ HP.attr (HH.AttrName "x1") (show props.padding.left)
              , HP.attr (HH.AttrName "y1") (show y)
              , HP.attr (HH.AttrName "x2") (show (props.padding.left + chartWidth))
              , HP.attr (HH.AttrName "y2") (show y)
              , svgCls [ "stroke-muted-foreground/20" ]
              , HP.attr (HH.AttrName "stroke-dasharray") "4,4"
              ]
              []
        ) (Array.replicate (numHLines + 1) unit)
    
    -- Legend
    legend = map (\s ->
      HH.div
        [ cls [ "flex items-center gap-2" ] ]
        [ HH.div
            [ cls [ "w-4 h-0.5" ]
            , HP.style ("background-color: " <> s.color)
            ]
            []
        , HH.span
            [ cls [ "text-xs text-muted-foreground" ] ]
            [ HH.text s.label ]
        ]
    ) config.series
  in
    HH.div
      [ cls [ "relative" ] ]
      [ HH.elementNS svgNS (HH.ElemName "svg")
          [ svgCls [ "w-full h-auto" ]
          , HP.attr (HH.AttrName "viewBox") ("0 0 " <> show config.width <> " " <> show config.height)
          , HP.attr (HH.AttrName "preserveAspectRatio") "xMidYMid meet"
          ]
          (gridLines <> seriesLines)
      , HH.div
          [ cls [ "flex flex-wrap gap-4 justify-center mt-4" ] ]
          legend
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // path generation
-- ═══════════════════════════════════════════════════════════════════════════════

type Point = { x :: Number, y :: Number }

-- | Generate SVG path based on curve type
generatePath :: CurveType -> Array Point -> String
generatePath cType points =
  case cType of
    Linear -> generateLinearPath points
    Bezier -> generateBezierPath points
    Step -> generateStepPath points
    StepBefore -> generateStepBeforePath points

-- | Linear interpolation (straight lines)
generateLinearPath :: Array Point -> String
generateLinearPath points =
  case Array.uncons points of
    Nothing -> ""
    Just { head, tail } ->
      "M " <> show head.x <> " " <> show head.y <>
      foldl (\acc p -> acc <> " L " <> show p.x <> " " <> show p.y) "" tail

-- | Cubic bezier smooth curves
generateBezierPath :: Array Point -> String
generateBezierPath points =
  case Array.uncons points of
    Nothing -> ""
    Just { head, tail } ->
      let
        -- Calculate control points for smooth bezier
        getControlPoints :: Point -> Point -> Point -> { c1 :: Point, c2 :: Point }
        getControlPoints p0 p1 p2 =
          let
            tension = 0.3
            d01 = { x: p1.x - p0.x, y: p1.y - p0.y }
            d12 = { x: p2.x - p1.x, y: p2.y - p1.y }
          in
            { c1: { x: p1.x - d12.x * tension, y: p1.y - d12.y * tension }
            , c2: { x: p1.x + d01.x * tension, y: p1.y + d01.y * tension }
            }
        
        -- Build path with cubic bezier curves
        buildCurve :: { path :: String, prev :: Point, prevPrev :: Point } -> Point -> { path :: String, prev :: Point, prevPrev :: Point }
        buildCurve acc curr =
          let
            cp = getControlPoints acc.prevPrev acc.prev curr
          in
            { path: acc.path <> 
                " C " <> show cp.c1.x <> " " <> show cp.c1.y <>
                ", " <> show cp.c2.x <> " " <> show cp.c2.y <>
                ", " <> show curr.x <> " " <> show curr.y
            , prev: curr
            , prevPrev: acc.prev
            }
      in
        case Array.uncons tail of
          Nothing -> "M " <> show head.x <> " " <> show head.y
          Just { head: second, tail: rest } ->
            let
              initial = 
                { path: "M " <> show head.x <> " " <> show head.y <>
                        " L " <> show second.x <> " " <> show second.y
                , prev: second
                , prevPrev: head
                }
              result = foldl buildCurve initial rest
            in
              result.path

-- | Step function (horizontal then vertical)
generateStepPath :: Array Point -> String
generateStepPath points =
  case Array.uncons points of
    Nothing -> ""
    Just { head, tail } ->
      "M " <> show head.x <> " " <> show head.y <>
      foldl (\acc p -> 
        acc <> " H " <> show p.x <> " V " <> show p.y
      ) "" tail

-- | Step before (vertical then horizontal)
generateStepBeforePath :: Array Point -> String
generateStepBeforePath points =
  case Array.uncons points of
    Nothing -> ""
    Just { head, tail } ->
      "M " <> show head.x <> " " <> show head.y <>
      foldl (\acc p -> 
        acc <> " V " <> show p.y <> " H " <> show p.x
      ) "" tail

-- | Generate fill path (closes the area to the bottom)
generateFillPath :: Array Point -> Number -> Number -> String
generateFillPath points chartHeight paddingTop =
  case Array.uncons points of
    Nothing -> ""
    Just { head, tail } ->
      let
        lastPoint = fromMaybe head (Array.last points)
        baseline = paddingTop + chartHeight
        linePath = generateLinearPath points
      in
        linePath <> 
        " L " <> show lastPoint.x <> " " <> show baseline <>
        " L " <> show head.x <> " " <> show baseline <>
        " Z"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Format number for display
formatNumber :: Number -> String
formatNumber n =
  let absN = abs n
  in
    if absN >= 1000000.0 then show (n / 1000000.0) <> "M"
    else if absN >= 1000.0 then show (n / 1000.0) <> "K"
    else show n
