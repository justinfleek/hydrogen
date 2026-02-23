-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                      // hydrogen // areachart
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Stacked Area chart component
-- |
-- | SVG-based stacked area and stream graph charts.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Chart.AreaChart as AreaChart
-- |
-- | -- Stacked area chart
-- | AreaChart.stackedAreaChart
-- |   { series: [ { label: "Desktop", data: desktopData, color: "#3b82f6" }
-- |             , { label: "Mobile", data: mobileData, color: "#10b981" }
-- |             , { label: "Tablet", data: tabletData, color: "#f59e0b" }
-- |             ]
-- |   , width: 400
-- |   , height: 300
-- |   }
-- |
-- | -- Stream graph (centered stacked areas)
-- | AreaChart.streamGraph
-- |   { series: streamData
-- |   , width: 400
-- |   , height: 300
-- |   }
-- |
-- | -- With custom configuration
-- | AreaChart.stackedAreaChartWithProps
-- |   defaultProps
-- |     { series = mySeries
-- |     , showTooltip = true
-- |     , showLegend = true
-- |     , curveType = Bezier
-- |     }
-- | ```
module Hydrogen.Chart.AreaChart
  ( -- * Stacked Area Chart
    stackedAreaChart
  , stackedAreaChartWithProps
  , StackedAreaConfig
  , StackedAreaProps
  , defaultProps
    -- * Stream Graph
  , streamGraph
  , StreamGraphConfig
    -- * Data Types
  , AreaSeries
  , DataPoint
    -- * Curve Types
  , CurveType(..)
    -- * Prop Builders
  , curveType
  , showGrid
  , showTooltip
  , showLegend
  , showAxisLabels
  , animated
  , className
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl, maximum, minimum, sum)
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

-- | Series definition for stacked area charts
type AreaSeries =
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
  | Step        -- ^ Step function

derive instance eqCurveType :: Eq CurveType

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // config
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Stacked area chart configuration
type StackedAreaConfig =
  { series :: Array AreaSeries
  , width :: Int
  , height :: Int
  }

-- | Full stacked area chart properties
type StackedAreaProps =
  { series :: Array AreaSeries
  , width :: Int
  , height :: Int
  , curveType :: CurveType
  , showGrid :: Boolean
  , showTooltip :: Boolean
  , showLegend :: Boolean
  , showAxisLabels :: Boolean
  , animated :: Boolean
  , padding :: { top :: Number, right :: Number, bottom :: Number, left :: Number }
  , className :: String
  }

-- | Default stacked area chart properties
defaultProps :: StackedAreaProps
defaultProps =
  { series: []
  , width: 400
  , height: 300
  , curveType: Bezier
  , showGrid: true
  , showTooltip: true
  , showLegend: true
  , showAxisLabels: true
  , animated: true
  , padding: { top: 20.0, right: 20.0, bottom: 40.0, left: 50.0 }
  , className: ""
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

type StackedAreaProp = StackedAreaProps -> StackedAreaProps

-- | Set curve interpolation type
curveType :: CurveType -> StackedAreaProp
curveType c props = props { curveType = c }

-- | Show/hide grid lines
showGrid :: Boolean -> StackedAreaProp
showGrid v props = props { showGrid = v }

-- | Show/hide tooltips
showTooltip :: Boolean -> StackedAreaProp
showTooltip v props = props { showTooltip = v }

-- | Show/hide legend
showLegend :: Boolean -> StackedAreaProp
showLegend v props = props { showLegend = v }

-- | Show/hide axis labels
showAxisLabels :: Boolean -> StackedAreaProp
showAxisLabels v props = props { showAxisLabels = v }

-- | Enable/disable animation
animated :: Boolean -> StackedAreaProp
animated v props = props { animated = v }

-- | Add custom class
className :: String -> StackedAreaProp
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // stacked area chart
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Simple stacked area chart
stackedAreaChart :: forall w i. StackedAreaConfig -> HH.HTML w i
stackedAreaChart config = stackedAreaChartWithProps
  defaultProps
    { series = config.series
    , width = config.width
    , height = config.height
    }

-- | Stacked area chart with full props
stackedAreaChartWithProps :: forall w i. StackedAreaProps -> HH.HTML w i
stackedAreaChartWithProps props =
  let
    chartWidth = toNumber props.width - props.padding.left - props.padding.right
    chartHeight = toNumber props.height - props.padding.top - props.padding.bottom
    
    -- Get all x values (assuming all series share x values)
    allXValues = case Array.head props.series of
      Just s -> map _.x s.data
      Nothing -> []
    
    numPoints = Array.length allXValues
    
    -- Calculate x range
    xMin = fromMaybe 0.0 (minimum allXValues)
    xMax = fromMaybe 1.0 (maximum allXValues)
    xRange = if xMax == xMin then 1.0 else xMax - xMin
    
    -- Calculate stacked y values
    -- For each x index, compute cumulative y values for stacking
    stackedValues :: Array (Array { x :: Number, y0 :: Number, y1 :: Number })
    stackedValues = 
      let
        -- Get y values at each x index for each series
        getYAtIndex :: Int -> AreaSeries -> Number
        getYAtIndex idx s = fromMaybe 0.0 (map _.y (Array.index s.data idx))
        
        -- Build stacked values series by series
        buildStacks :: { stacks :: Array (Array { x :: Number, y0 :: Number, y1 :: Number }), prevTops :: Array Number } -> AreaSeries -> { stacks :: Array (Array { x :: Number, y0 :: Number, y1 :: Number }), prevTops :: Array Number }
        buildStacks acc series =
          let
            stackPoints = Array.mapWithIndex (\idx x ->
              let
                prevTop = fromMaybe 0.0 (Array.index acc.prevTops idx)
                y = getYAtIndex idx series
              in
                { x, y0: prevTop, y1: prevTop + y }
            ) allXValues
            
            newTops = map _.y1 stackPoints
          in
            { stacks: acc.stacks <> [stackPoints]
            , prevTops: newTops
            }
        
        initialTops = Array.replicate numPoints 0.0
        result = foldl buildStacks { stacks: [], prevTops: initialTops } props.series
      in
        result.stacks
    
    -- Calculate y range
    allY1Values = stackedValues >>= map _.y1
    yMax = fromMaybe 1.0 (maximum allY1Values)
    
    -- Scale point to chart coordinates
    scaleX :: Number -> Number
    scaleX x = props.padding.left + ((x - xMin) / xRange) * chartWidth
    
    scaleY :: Number -> Number
    scaleY y = props.padding.top + (1.0 - y / yMax) * chartHeight
    
    -- Generate gradient definitions
    gradientDefs = Array.mapWithIndex (\idx s ->
      HH.elementNS svgNS (HH.ElemName "linearGradient")
        [ HP.attr (HH.AttrName "id") ("areaGradient" <> show idx)
        , HP.attr (HH.AttrName "x1") "0%"
        , HP.attr (HH.AttrName "y1") "0%"
        , HP.attr (HH.AttrName "x2") "0%"
        , HP.attr (HH.AttrName "y2") "100%"
        ]
        [ HH.elementNS svgNS (HH.ElemName "stop")
            [ HP.attr (HH.AttrName "offset") "0%"
            , HP.attr (HH.AttrName "stop-color") s.color
            , HP.attr (HH.AttrName "stop-opacity") "0.8"
            ]
            []
        , HH.elementNS svgNS (HH.ElemName "stop")
            [ HP.attr (HH.AttrName "offset") "100%"
            , HP.attr (HH.AttrName "stop-color") s.color
            , HP.attr (HH.AttrName "stop-opacity") "0.3"
            ]
            []
        ]
    ) props.series
    
    -- Generate area paths (in reverse order so first series is on top)
    areaPaths = Array.mapWithIndex (\idx stackData ->
      let
        series = fromMaybe { label: "", data: [], color: "#3b82f6" } (Array.index props.series idx)
        
        -- Build path: top line forward, then bottom line backward
        topPoints = map (\p -> { x: scaleX p.x, y: scaleY p.y1 }) stackData
        bottomPoints = Array.reverse (map (\p -> { x: scaleX p.x, y: scaleY p.y0 }) stackData)
        
        pathData = generateAreaPath props.curveType topPoints bottomPoints
      in
        HH.elementNS svgNS (HH.ElemName "path")
          [ HP.attr (HH.AttrName "d") pathData
          , HP.attr (HH.AttrName "fill") ("url(#areaGradient" <> show idx <> ")")
          , HP.attr (HH.AttrName "stroke") series.color
          , HP.attr (HH.AttrName "stroke-width") "1"
          , svgCls [ "hover:opacity-80 transition-opacity" ]
          ]
          [ HH.elementNS svgNS (HH.ElemName "title")
              []
              [ HH.text series.label ]
          ]
    ) stackedValues
    
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
          valueSpacing = yMax / toNumber numLabels
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
        let
          numLabels = min 6 numPoints
          labelIndices = if numPoints <= numLabels 
                         then Array.range 0 (numPoints - 1)
                         else Array.mapWithIndex (\i _ -> (i * (numPoints - 1)) / (numLabels - 1)) (Array.replicate numLabels unit)
        in
          map (\idx ->
            let 
              xVal = fromMaybe 0.0 (Array.index allXValues idx)
              x = scaleX xVal
            in HH.elementNS svgNS (HH.ElemName "text")
                [ HP.attr (HH.AttrName "x") (show x)
                , HP.attr (HH.AttrName "y") (show (props.padding.top + chartHeight + 20.0))
                , HP.attr (HH.AttrName "text-anchor") "middle"
                , svgCls [ "fill-muted-foreground text-xs" ]
                ]
                [ HH.text (formatNumber xVal) ]
          ) labelIndices
      else []
    
    -- Legend
    legend = if props.showLegend
      then map (\s ->
        HH.div
          [ cls [ "flex items-center gap-2" ] ]
          [ HH.div
              [ cls [ "w-4 h-3 rounded-sm" ]
              , HP.style ("background-color: " <> s.color)
              ]
              []
          , HH.span
              [ cls [ "text-xs text-muted-foreground" ] ]
              [ HH.text s.label ]
          ]
      ) props.series
      else []
  in
    HH.div
      [ cls [ "relative", props.className ] ]
      [ HH.elementNS svgNS (HH.ElemName "svg")
          [ svgCls [ "w-full h-auto" ]
          , HP.attr (HH.AttrName "viewBox") ("0 0 " <> show props.width <> " " <> show props.height)
          , HP.attr (HH.AttrName "preserveAspectRatio") "xMidYMid meet"
          ]
          ( [ HH.elementNS svgNS (HH.ElemName "defs") [] gradientDefs ]
            <> gridLines
            <> yAxisLabels
            <> xAxisLabels
            <> Array.reverse areaPaths  -- Reverse so first series renders on top
          )
      , if props.showLegend
          then HH.div
            [ cls [ "flex flex-wrap gap-4 justify-center mt-4" ] ]
            legend
          else HH.text ""
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // stream graph
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Stream graph configuration
type StreamGraphConfig =
  { series :: Array AreaSeries
  , width :: Int
  , height :: Int
  }

-- | Stream graph (centered stacked area)
streamGraph :: forall w i. StreamGraphConfig -> HH.HTML w i
streamGraph config =
  let
    props = defaultProps
      { series = config.series
      , width = config.width
      , height = config.height
      }
    
    chartWidth = toNumber config.width - props.padding.left - props.padding.right
    chartHeight = toNumber config.height - props.padding.top - props.padding.bottom
    
    -- Get all x values
    allXValues = case Array.head config.series of
      Just s -> map _.x s.data
      Nothing -> []
    
    numPoints = Array.length allXValues
    
    -- Calculate x range
    xMin = fromMaybe 0.0 (minimum allXValues)
    xMax = fromMaybe 1.0 (maximum allXValues)
    xRange = if xMax == xMin then 1.0 else xMax - xMin
    
    -- Calculate total at each x index
    getTotalAtIndex :: Int -> Number
    getTotalAtIndex idx = sum (map (\s -> fromMaybe 0.0 (map _.y (Array.index s.data idx))) config.series)
    
    -- Get max total for scaling
    maxTotal = fromMaybe 1.0 (maximum (Array.mapWithIndex (\i _ -> getTotalAtIndex i) allXValues))
    
    -- Build stream centered stacks
    streamStacks :: Array (Array { x :: Number, y0 :: Number, y1 :: Number })
    streamStacks =
      let
        getYAtIndex :: Int -> AreaSeries -> Number
        getYAtIndex idx s = fromMaybe 0.0 (map _.y (Array.index s.data idx))
        
        -- For each x, center the stack around y=0
        buildStream :: { stacks :: Array (Array { x :: Number, y0 :: Number, y1 :: Number }), prevTops :: Array Number } -> AreaSeries -> { stacks :: Array (Array { x :: Number, y0 :: Number, y1 :: Number }), prevTops :: Array Number }
        buildStream acc series =
          let
            stackPoints = Array.mapWithIndex (\idx x ->
              let
                total = getTotalAtIndex idx
                offset = - total / 2.0  -- Center around 0
                prevTop = fromMaybe offset (Array.index acc.prevTops idx)
                y = getYAtIndex idx series
              in
                { x, y0: prevTop, y1: prevTop + y }
            ) allXValues
            
            newTops = map _.y1 stackPoints
          in
            { stacks: acc.stacks <> [stackPoints]
            , prevTops: newTops
            }
        
        initialTops = Array.mapWithIndex (\i _ -> - getTotalAtIndex i / 2.0) allXValues
        result = foldl buildStream { stacks: [], prevTops: initialTops } config.series
      in
        result.stacks
    
    -- Scale functions
    scaleX :: Number -> Number
    scaleX x = props.padding.left + ((x - xMin) / xRange) * chartWidth
    
    scaleY :: Number -> Number
    scaleY y = props.padding.top + chartHeight / 2.0 - (y / maxTotal) * chartHeight
    
    -- Generate gradient definitions
    gradientDefs = Array.mapWithIndex (\idx s ->
      HH.elementNS svgNS (HH.ElemName "linearGradient")
        [ HP.attr (HH.AttrName "id") ("streamGradient" <> show idx)
        , HP.attr (HH.AttrName "x1") "0%"
        , HP.attr (HH.AttrName "y1") "0%"
        , HP.attr (HH.AttrName "x2") "0%"
        , HP.attr (HH.AttrName "y2") "100%"
        ]
        [ HH.elementNS svgNS (HH.ElemName "stop")
            [ HP.attr (HH.AttrName "offset") "0%"
            , HP.attr (HH.AttrName "stop-color") s.color
            , HP.attr (HH.AttrName "stop-opacity") "0.9"
            ]
            []
        , HH.elementNS svgNS (HH.ElemName "stop")
            [ HP.attr (HH.AttrName "offset") "100%"
            , HP.attr (HH.AttrName "stop-color") s.color
            , HP.attr (HH.AttrName "stop-opacity") "0.6"
            ]
            []
        ]
    ) config.series
    
    -- Generate stream paths
    streamPaths = Array.mapWithIndex (\idx stackData ->
      let
        series = fromMaybe { label: "", data: [], color: "#3b82f6" } (Array.index config.series idx)
        
        topPoints = map (\p -> { x: scaleX p.x, y: scaleY p.y1 }) stackData
        bottomPoints = Array.reverse (map (\p -> { x: scaleX p.x, y: scaleY p.y0 }) stackData)
        
        pathData = generateAreaPath Bezier topPoints bottomPoints
      in
        HH.elementNS svgNS (HH.ElemName "path")
          [ HP.attr (HH.AttrName "d") pathData
          , HP.attr (HH.AttrName "fill") ("url(#streamGradient" <> show idx <> ")")
          , HP.attr (HH.AttrName "stroke") series.color
          , HP.attr (HH.AttrName "stroke-width") "0.5"
          , svgCls [ "hover:opacity-80 transition-opacity" ]
          ]
          [ HH.elementNS svgNS (HH.ElemName "title")
              []
              [ HH.text series.label ]
          ]
    ) streamStacks
    
    -- Legend
    legend = map (\s ->
      HH.div
        [ cls [ "flex items-center gap-2" ] ]
        [ HH.div
            [ cls [ "w-4 h-3 rounded-sm" ]
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
          ( [ HH.elementNS svgNS (HH.ElemName "defs") [] gradientDefs ]
            <> Array.reverse streamPaths
          )
      , HH.div
          [ cls [ "flex flex-wrap gap-4 justify-center mt-4" ] ]
          legend
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // path generation
-- ═══════════════════════════════════════════════════════════════════════════════

type Point = { x :: Number, y :: Number }

-- | Generate area path from top and bottom point arrays
generateAreaPath :: CurveType -> Array Point -> Array Point -> String
generateAreaPath cType topPoints bottomPoints =
  let
    topPath = case cType of
      Linear -> generateLinearPath topPoints
      Bezier -> generateBezierPath topPoints
      Step -> generateStepPath topPoints
    
    bottomPath = case cType of
      Linear -> generateLinearContinuePath bottomPoints
      Bezier -> generateBezierContinuePath bottomPoints
      Step -> generateStepContinuePath bottomPoints
  in
    topPath <> bottomPath <> " Z"

-- | Linear path starting with M
generateLinearPath :: Array Point -> String
generateLinearPath points =
  case Array.uncons points of
    Nothing -> ""
    Just { head, tail } ->
      "M " <> show head.x <> " " <> show head.y <>
      foldl (\acc p -> acc <> " L " <> show p.x <> " " <> show p.y) "" tail

-- | Linear path continuing (no M, starts with L)
generateLinearContinuePath :: Array Point -> String
generateLinearContinuePath points =
  foldl (\acc p -> acc <> " L " <> show p.x <> " " <> show p.y) "" points

-- | Bezier path starting with M
generateBezierPath :: Array Point -> String
generateBezierPath points =
  case Array.uncons points of
    Nothing -> ""
    Just { head, tail } ->
      let
        buildCurve :: { path :: String, prev :: Point, prevPrev :: Point } -> Point -> { path :: String, prev :: Point, prevPrev :: Point }
        buildCurve acc curr =
          let
            tension = 0.3
            cp1x = acc.prev.x + (curr.x - acc.prevPrev.x) * tension
            cp1y = acc.prev.y + (curr.y - acc.prevPrev.y) * tension
            cp2x = curr.x - (curr.x - acc.prev.x) * tension
            cp2y = curr.y - (curr.y - acc.prev.y) * tension
          in
            { path: acc.path <> 
                " C " <> show cp1x <> " " <> show cp1y <>
                ", " <> show cp2x <> " " <> show cp2y <>
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

-- | Bezier path continuing (no M)
generateBezierContinuePath :: Array Point -> String
generateBezierContinuePath points =
  case Array.uncons points of
    Nothing -> ""
    Just { head, tail } ->
      let
        buildCurve :: { path :: String, prev :: Point, prevPrev :: Point } -> Point -> { path :: String, prev :: Point, prevPrev :: Point }
        buildCurve acc curr =
          let
            tension = 0.3
            cp1x = acc.prev.x + (curr.x - acc.prevPrev.x) * tension
            cp1y = acc.prev.y + (curr.y - acc.prevPrev.y) * tension
            cp2x = curr.x - (curr.x - acc.prev.x) * tension
            cp2y = curr.y - (curr.y - acc.prev.y) * tension
          in
            { path: acc.path <> 
                " C " <> show cp1x <> " " <> show cp1y <>
                ", " <> show cp2x <> " " <> show cp2y <>
                ", " <> show curr.x <> " " <> show curr.y
            , prev: curr
            , prevPrev: acc.prev
            }
        
        initial = { path: " L " <> show head.x <> " " <> show head.y, prev: head, prevPrev: head }
        result = foldl buildCurve initial tail
      in
        result.path

-- | Step path starting with M
generateStepPath :: Array Point -> String
generateStepPath points =
  case Array.uncons points of
    Nothing -> ""
    Just { head, tail } ->
      "M " <> show head.x <> " " <> show head.y <>
      foldl (\acc p -> acc <> " H " <> show p.x <> " V " <> show p.y) "" tail

-- | Step path continuing (no M)
generateStepContinuePath :: Array Point -> String
generateStepContinuePath points =
  foldl (\acc p -> acc <> " H " <> show p.x <> " V " <> show p.y) "" points

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

-- Note: Using Prelude.min for integer minimum
