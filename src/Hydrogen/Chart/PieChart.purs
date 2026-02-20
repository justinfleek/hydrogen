-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // hydrogen // piechart
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pie/Donut chart component
-- |
-- | SVG-based pie and donut charts with animations and interactivity.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Chart.PieChart as PieChart
-- |
-- | -- Simple pie chart
-- | PieChart.pieChart
-- |   { data: [ { label: "Sales", value: 40.0 }
-- |           , { label: "Marketing", value: 30.0 }
-- |           , { label: "Engineering", value: 30.0 }
-- |           ]
-- |   , size: 200
-- |   }
-- |
-- | -- Donut chart
-- | PieChart.donutChart
-- |   { data: slices
-- |   , size: 200
-- |   , innerRadius: 0.6  -- 60% of radius
-- |   }
-- |
-- | -- With custom colors and labels
-- | PieChart.pieChartWithProps
-- |   defaultProps
-- |     { data = myData
-- |     , colors = ["#3b82f6", "#10b981", "#f59e0b"]
-- |     , showLabels = true
-- |     , labelPosition = Outside
-- |     }
-- |
-- | -- Donut with center content
-- | PieChart.donutWithCenter
-- |   { data: slices
-- |   , size: 200
-- |   , innerRadius: 0.6
-- |   , centerContent: Just $ HH.text "Total: $1,234"
-- |   }
-- | ```
module Hydrogen.Chart.PieChart
  ( -- * Pie Chart
    pieChart
  , pieChartWithProps
  , PieChartConfig
  , PieChartProps
  , defaultProps
    -- * Donut Chart
  , donutChart
  , donutWithCenter
  , DonutConfig
  , DonutWithCenterConfig
    -- * Data Types
  , PieSlice
  , ComputedSlice
    -- * Label Position
  , LabelPosition(..)
    -- * Prop Builders
  , colors
  , showLabels
  , showLegend
  , showTooltip
  , labelPosition
  , innerRadius
  , animated
  , explodeOnClick
  , className
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl, sum)
import Data.Int (toNumber)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Number (cos, sin, pi)
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Hydrogen.UI.Core (cls, svgNS, svgCls)
import Data.Int (round) as Int

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // data types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Pie slice data
type PieSlice =
  { label :: String
  , value :: Number
  }

-- | Computed slice with angles and path
type ComputedSlice =
  { label :: String
  , value :: Number
  , percentage :: Number
  , startAngle :: Number
  , endAngle :: Number
  , color :: String
  , path :: String
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // label position
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Where to position slice labels
data LabelPosition
  = Inside    -- ^ Labels inside slices
  | Outside   -- ^ Labels outside with lines
  | None      -- ^ No labels

derive instance eqLabelPosition :: Eq LabelPosition

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // config
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Basic pie chart configuration
type PieChartConfig =
  { data :: Array PieSlice
  , size :: Int
  }

-- | Full pie chart properties
type PieChartProps =
  { data :: Array PieSlice
  , size :: Int
  , innerRadius :: Number  -- 0 for pie, 0.5-0.8 for donut
  , colors :: Array String
  , showLabels :: Boolean
  , showLegend :: Boolean
  , showTooltip :: Boolean
  , labelPosition :: LabelPosition
  , animated :: Boolean
  , explodeOnClick :: Boolean
  , explodeDistance :: Number
  , strokeWidth :: Number
  , strokeColor :: String
  , className :: String
  }

-- | Default pie chart properties
defaultProps :: PieChartProps
defaultProps =
  { data: []
  , size: 200
  , innerRadius: 0.0
  , colors: ["#3b82f6", "#10b981", "#f59e0b", "#ef4444", "#8b5cf6", "#ec4899", "#06b6d4", "#84cc16"]
  , showLabels: true
  , showLegend: true
  , showTooltip: true
  , labelPosition: Inside
  , animated: true
  , explodeOnClick: false
  , explodeDistance: 10.0
  , strokeWidth: 2.0
  , strokeColor: "white"
  , className: ""
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

type PieChartProp = PieChartProps -> PieChartProps

-- | Set slice colors
colors :: Array String -> PieChartProp
colors cs props = props { colors = cs }

-- | Show/hide labels
showLabels :: Boolean -> PieChartProp
showLabels v props = props { showLabels = v }

-- | Show/hide legend
showLegend :: Boolean -> PieChartProp
showLegend v props = props { showLegend = v }

-- | Show/hide tooltips
showTooltip :: Boolean -> PieChartProp
showTooltip v props = props { showTooltip = v }

-- | Set label position
labelPosition :: LabelPosition -> PieChartProp
labelPosition pos props = props { labelPosition = pos }

-- | Set inner radius (0 = pie, 0.5-0.8 = donut)
innerRadius :: Number -> PieChartProp
innerRadius r props = props { innerRadius = r }

-- | Enable/disable animation
animated :: Boolean -> PieChartProp
animated v props = props { animated = v }

-- | Enable/disable explode on click
explodeOnClick :: Boolean -> PieChartProp
explodeOnClick v props = props { explodeOnClick = v }

-- | Add custom class
className :: String -> PieChartProp
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // pie chart
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Simple pie chart with basic config
pieChart :: forall w i. PieChartConfig -> HH.HTML w i
pieChart config = pieChartWithProps
  defaultProps
    { data = config.data
    , size = config.size
    }

-- | Pie chart with full props
pieChartWithProps :: forall w i. PieChartProps -> HH.HTML w i
pieChartWithProps props =
  let
    size = toNumber props.size
    center = size / 2.0
    radius = center - props.strokeWidth
    innerRad = radius * props.innerRadius
    
    -- Calculate total and compute slices
    total = sum (map _.value props.data)
    
    computeSlices :: Array PieSlice -> Array ComputedSlice
    computeSlices slices =
      let
        result = foldl (\acc slice ->
          let
            percentage = if total == 0.0 then 0.0 else slice.value / total
            angleSpan = percentage * 2.0 * pi
            startAngle = acc.currentAngle
            endAngle = startAngle + angleSpan
            color = getColor acc.idx props.colors
            path = arcPath center center radius innerRad startAngle endAngle
          in
            { idx: acc.idx + 1
            , currentAngle: endAngle
            , slices: acc.slices <>
                [ { label: slice.label
                  , value: slice.value
                  , percentage: percentage * 100.0
                  , startAngle
                  , endAngle
                  , color
                  , path
                  }
                ]
            }
        ) { idx: 0, currentAngle: - pi / 2.0, slices: [] } slices
      in
        result.slices
    
    computedSlices = computeSlices props.data
    
    -- Gradient definitions
    gradientDefs = Array.mapWithIndex (\idx slice ->
      HH.elementNS svgNS (HH.ElemName "radialGradient")
        [ HP.attr (HH.AttrName "id") ("pieGradient" <> show idx)
        , HP.attr (HH.AttrName "cx") "30%"
        , HP.attr (HH.AttrName "cy") "30%"
        ]
        [ HH.elementNS svgNS (HH.ElemName "stop")
            [ HP.attr (HH.AttrName "offset") "0%"
            , HP.attr (HH.AttrName "stop-color") slice.color
            , HP.attr (HH.AttrName "stop-opacity") "1"
            ]
            []
        , HH.elementNS svgNS (HH.ElemName "stop")
            [ HP.attr (HH.AttrName "offset") "100%"
            , HP.attr (HH.AttrName "stop-color") slice.color
            , HP.attr (HH.AttrName "stop-opacity") "0.8"
            ]
            []
        ]
    ) computedSlices
    
    -- Render slices
    sliceElements = Array.mapWithIndex (\idx slice ->
      HH.elementNS svgNS (HH.ElemName "g")
        [ svgCls [ "pie-slice cursor-pointer" ]
        , HP.attr (HH.AttrName "data-index") (show idx)
        ]
        [ HH.elementNS svgNS (HH.ElemName "path")
            [ HP.attr (HH.AttrName "d") slice.path
            , HP.attr (HH.AttrName "fill") slice.color
            , HP.attr (HH.AttrName "stroke") props.strokeColor
            , HP.attr (HH.AttrName "stroke-width") (show props.strokeWidth)
            , svgCls [ "hover:opacity-80 transition-all duration-200" ]
            , HP.attr (HH.AttrName "style") (if props.animated then "transform-origin: center; animation: pieSliceIn 0.5s ease-out " <> show (idx * 100) <> "ms backwards;" else "")
            ]
            [ HH.elementNS svgNS (HH.ElemName "title")
                []
                [ HH.text (slice.label <> ": " <> formatPercentage slice.percentage) ]
            ]
        ]
    ) computedSlices
    
    -- Inside labels
    insideLabels = if props.showLabels && props.labelPosition == Inside
      then map (\slice ->
        let
          midAngle = (slice.startAngle + slice.endAngle) / 2.0
          labelRadius = radius * (if props.innerRadius > 0.0 then (1.0 + props.innerRadius) / 2.0 else 0.6)
          labelX = center + labelRadius * cos midAngle
          labelY = center + labelRadius * sin midAngle
        in
          if slice.percentage >= 5.0  -- Only show label if slice is big enough
            then HH.elementNS svgNS (HH.ElemName "text")
                [ HP.attr (HH.AttrName "x") (show labelX)
                , HP.attr (HH.AttrName "y") (show labelY)
                , HP.attr (HH.AttrName "text-anchor") "middle"
                , HP.attr (HH.AttrName "dominant-baseline") "middle"
                , svgCls [ "fill-white text-xs font-medium pointer-events-none" ]
                ]
                [ HH.text (formatPercentage slice.percentage) ]
            else HH.text ""
      ) computedSlices
      else []
    
    -- Outside labels with leader lines
    outsideLabels = if props.showLabels && props.labelPosition == Outside
      then computedSlices >>= (\slice ->
        let
          midAngle = (slice.startAngle + slice.endAngle) / 2.0
          
          -- Start point on the slice edge
          startX = center + radius * cos midAngle
          startY = center + radius * sin midAngle
          
          -- End point for label
          labelRadius = radius + 30.0
          endX = center + labelRadius * cos midAngle
          endY = center + labelRadius * sin midAngle
          
          -- Text anchor based on position
          textAnchor = if cos midAngle >= 0.0 then "start" else "end"
          textX = if cos midAngle >= 0.0 then endX + 5.0 else endX - 5.0
        in
          [ HH.elementNS svgNS (HH.ElemName "line")
              [ HP.attr (HH.AttrName "x1") (show startX)
              , HP.attr (HH.AttrName "y1") (show startY)
              , HP.attr (HH.AttrName "x2") (show endX)
              , HP.attr (HH.AttrName "y2") (show endY)
              , svgCls [ "stroke-muted-foreground/50" ]
              , HP.attr (HH.AttrName "stroke-width") "1"
              ]
              []
          , HH.elementNS svgNS (HH.ElemName "text")
              [ HP.attr (HH.AttrName "x") (show textX)
              , HP.attr (HH.AttrName "y") (show endY)
              , HP.attr (HH.AttrName "text-anchor") textAnchor
              , HP.attr (HH.AttrName "dominant-baseline") "middle"
              , svgCls [ "fill-foreground text-xs" ]
              ]
              [ HH.text (slice.label <> " " <> formatPercentage slice.percentage) ]
          ]
      )
      else []
    
    -- SVG size with extra space for outside labels
    svgSize = if props.labelPosition == Outside 
              then size + 80.0 
              else size
    offset = if props.labelPosition == Outside then 40.0 else 0.0
    
    -- Legend
    legend = if props.showLegend
      then map (\slice ->
        HH.div
          [ cls [ "flex items-center gap-2" ] ]
          [ HH.div
              [ cls [ "w-3 h-3 rounded-sm flex-shrink-0" ]
              , HP.style ("background-color: " <> slice.color)
              ]
              []
          , HH.span
              [ cls [ "text-xs text-muted-foreground truncate" ] ]
              [ HH.text slice.label ]
          , HH.span
              [ cls [ "text-xs text-muted-foreground ml-auto" ] ]
              [ HH.text (formatPercentage slice.percentage) ]
          ]
      ) computedSlices
      else []
  in
    HH.div
      [ cls [ "flex flex-col items-center gap-4", props.className ] ]
      [ HH.elementNS svgNS (HH.ElemName "svg")
          [ svgCls [ "overflow-visible" ]
          , HP.attr (HH.AttrName "viewBox") ("0 0 " <> show svgSize <> " " <> show svgSize)
          , HP.attr (HH.AttrName "width") (show svgSize)
          , HP.attr (HH.AttrName "height") (show svgSize)
          ]
          ( [ HH.elementNS svgNS (HH.ElemName "defs") [] gradientDefs
            , HH.elementNS svgNS (HH.ElemName "g")
                [ HP.attr (HH.AttrName "transform") ("translate(" <> show offset <> ", " <> show offset <> ")") ]
                (sliceElements <> insideLabels <> outsideLabels)
            ]
          )
      , if props.showLegend
          then HH.div
            [ cls [ "grid grid-cols-2 gap-x-4 gap-y-2 w-full max-w-xs" ] ]
            legend
          else HH.text ""
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // donut chart
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Donut chart configuration
type DonutConfig =
  { data :: Array PieSlice
  , size :: Int
  , innerRadius :: Number
  }

-- | Donut chart (pie with hole)
donutChart :: forall w i. DonutConfig -> HH.HTML w i
donutChart config = pieChartWithProps
  defaultProps
    { data = config.data
    , size = config.size
    , innerRadius = config.innerRadius
    }

-- | Donut with center content configuration
type DonutWithCenterConfig w i =
  { data :: Array PieSlice
  , size :: Int
  , innerRadius :: Number
  , centerContent :: Maybe (HH.HTML w i)
  }

-- | Donut chart with center content
donutWithCenter :: forall w i. DonutWithCenterConfig w i -> HH.HTML w i
donutWithCenter config =
  let
    size = toNumber config.size
    center = size / 2.0
    innerRad = center * config.innerRadius - 10.0
    
    centerElement = case config.centerContent of
      Just content ->
        HH.div
          [ cls [ "absolute inset-0 flex items-center justify-center pointer-events-none" ]
          ]
          [ HH.div
              [ cls [ "text-center" ]
              , HP.style ("max-width: " <> show (innerRad * 2.0 * 0.8) <> "px")
              ]
              [ content ]
          ]
      Nothing -> HH.text ""
  in
    HH.div
      [ cls [ "relative inline-block" ] ]
      [ pieChartWithProps
          defaultProps
            { data = config.data
            , size = config.size
            , innerRadius = config.innerRadius
            , showLegend = false
            }
      , centerElement
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // arc generation
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Generate SVG arc path
arcPath :: Number -> Number -> Number -> Number -> Number -> Number -> String
arcPath cx cy outerR innerR startAngle endAngle =
  let
    -- Handle full circle case
    fullCircle = endAngle - startAngle >= 2.0 * pi - 0.0001
    
    -- Adjust end angle slightly for full circles to avoid rendering issues
    actualEndAngle = if fullCircle then endAngle - 0.0001 else endAngle
    
    -- Outer arc points
    x1 = cx + outerR * cos startAngle
    y1 = cy + outerR * sin startAngle
    x2 = cx + outerR * cos actualEndAngle
    y2 = cy + outerR * sin actualEndAngle
    
    -- Inner arc points (for donut)
    x3 = cx + innerR * cos actualEndAngle
    y3 = cy + innerR * sin actualEndAngle
    x4 = cx + innerR * cos startAngle
    y4 = cy + innerR * sin startAngle
    
    -- Large arc flag
    largeArc = if actualEndAngle - startAngle > pi then "1" else "0"
  in
    if innerR <= 0.0
      -- Pie slice (no inner radius)
      then "M " <> show cx <> " " <> show cy <>
           " L " <> show x1 <> " " <> show y1 <>
           " A " <> show outerR <> " " <> show outerR <> " 0 " <> largeArc <> " 1 " <> show x2 <> " " <> show y2 <>
           " Z"
      -- Donut slice (with inner radius)
      else "M " <> show x1 <> " " <> show y1 <>
           " A " <> show outerR <> " " <> show outerR <> " 0 " <> largeArc <> " 1 " <> show x2 <> " " <> show y2 <>
           " L " <> show x3 <> " " <> show y3 <>
           " A " <> show innerR <> " " <> show innerR <> " 0 " <> largeArc <> " 0 " <> show x4 <> " " <> show y4 <>
           " Z"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get color from palette
getColor :: Int -> Array String -> String
getColor idx palette = 
  fromMaybe "#3b82f6" (Array.index palette (idx `mod` Array.length palette))

-- | Format percentage for display
formatPercentage :: Number -> String
formatPercentage p = show (roundTo1Decimal p) <> "%"

-- | Round to 1 decimal place
roundTo1Decimal :: Number -> Number
roundTo1Decimal n = 
  let scaled = n * 10.0
      rounded = Int.round scaled
  in toNumber rounded / 10.0
