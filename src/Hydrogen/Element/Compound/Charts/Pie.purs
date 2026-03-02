-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // element // compound // charts // pie
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pie Chart — Circular chart showing proportions.

module Hydrogen.Element.Compound.Charts.Pie
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
  ) where

import Prelude
  ( map
  , show
  , negate
  , ($)
  , (<>)
  , (+)
  , (-)
  , (*)
  , (/)
  , (>)
  )

import Data.Array as Array
import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just), fromMaybe)
import Hydrogen.Math.Core as Math
import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // pie chart
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pie slice data
type PieSlice =
  { value :: Number
  , label :: String
  , color :: String
  }

-- | Pie chart properties
type PieChartProps =
  { size :: Number
  , innerRadius :: Number  -- 0 for pie, > 0 for donut
  , showLabels :: Boolean
  , showLegend :: Boolean
  , className :: String
  }

-- | Property modifier
type PieChartProp = PieChartProps -> PieChartProps

-- | Default pie chart properties
defaultPieProps :: PieChartProps
defaultPieProps =
  { size: 200.0
  , innerRadius: 0.0
  , showLabels: true
  , showLegend: true
  , className: ""
  }

-- | Set chart size
pieSize :: Number -> PieChartProp
pieSize s props = props { size = s }

-- | Set inner radius (for donut effect)
pieInnerRadius :: Number -> PieChartProp
pieInnerRadius r props = props { innerRadius = r }

-- | Show/hide slice labels
pieShowLabels :: Boolean -> PieChartProp
pieShowLabels b props = props { showLabels = b }

-- | Show/hide legend
pieShowLegend :: Boolean -> PieChartProp
pieShowLegend b props = props { showLegend = b }

-- | Pie chart component
pieChart :: forall msg. Array PieChartProp -> Array PieSlice -> E.Element msg
pieChart propMods slices =
  let
    props = foldl (\p f -> f p) defaultPieProps propMods
  in
    renderPieChart props slices

-- | Donut chart (pie with hole)
donutChart :: forall msg. Array PieChartProp -> Array PieSlice -> E.Element msg
donutChart propMods slices =
  let
    baseProps = foldl (\p f -> f p) defaultPieProps propMods
    props = baseProps { innerRadius = baseProps.size * 0.3 }
  in
    renderPieChart props slices

-- | Render pie/donut chart
renderPieChart :: forall msg. PieChartProps -> Array PieSlice -> E.Element msg
renderPieChart props slices =
  let
    total = foldl (\acc s -> acc + s.value) 0.0 slices
    cx = props.size / 2.0
    cy = props.size / 2.0
    radius = props.size / 2.0 - 10.0
    innerR = props.innerRadius
    slicePaths = generatePieSlices slices total cx cy radius innerR
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "align-items" "center"
      , E.style "gap" "24px"
      ]
      [ E.svg_
          [ E.attr "width" (show props.size)
          , E.attr "height" (show props.size)
          , E.attr "viewBox" ("0 0 " <> show props.size <> " " <> show props.size)
          ]
          slicePaths
      , if props.showLegend then pieLegend slices else E.text ""
      ]

-- | Generate pie slice SVG paths
generatePieSlices :: forall msg. Array PieSlice -> Number -> Number -> Number -> Number -> Number -> Array (E.Element msg)
generatePieSlices slices total cx cy radius innerR =
  let
    go :: Number -> Array PieSlice -> Array (E.Element msg)
    go _ [] = []
    go startAngle arr = case Array.head arr of
      Nothing -> []
      Just slice ->
        let
          sliceAngle = (slice.value / total) * Math.tau
          endAngle = startAngle + sliceAngle
          path = pieSlicePath cx cy radius innerR startAngle endAngle slice.color
          rest = fromMaybe [] (Array.tail arr)
        in
          Array.cons path (go endAngle rest)
  in
    go (negate (Math.pi / 2.0)) slices

-- | Generate SVG path for a pie slice
pieSlicePath :: forall msg. Number -> Number -> Number -> Number -> Number -> Number -> String -> E.Element msg
pieSlicePath cx cy radius innerR startAngle endAngle color =
  let
    x1 = cx + radius * Math.cos startAngle
    y1 = cy + radius * Math.sin startAngle
    x2 = cx + radius * Math.cos endAngle
    y2 = cy + radius * Math.sin endAngle
    largeArc = if endAngle - startAngle > Math.pi then "1" else "0"
    
    d = if innerR > 0.0
      then
        let
          ix1 = cx + innerR * Math.cos startAngle
          iy1 = cy + innerR * Math.sin startAngle
          ix2 = cx + innerR * Math.cos endAngle
          iy2 = cy + innerR * Math.sin endAngle
        in
          "M " <> show ix1 <> " " <> show iy1 <>
          " L " <> show x1 <> " " <> show y1 <>
          " A " <> show radius <> " " <> show radius <> " 0 " <> largeArc <> " 1 " <> show x2 <> " " <> show y2 <>
          " L " <> show ix2 <> " " <> show iy2 <>
          " A " <> show innerR <> " " <> show innerR <> " 0 " <> largeArc <> " 0 " <> show ix1 <> " " <> show iy1 <>
          " Z"
      else
        "M " <> show cx <> " " <> show cy <>
        " L " <> show x1 <> " " <> show y1 <>
        " A " <> show radius <> " " <> show radius <> " 0 " <> largeArc <> " 1 " <> show x2 <> " " <> show y2 <>
        " Z"
  in
    E.path_
      [ E.attr "d" d
      , E.attr "fill" color
      , E.style "transition" "opacity 0.2s ease"
      ]

-- | Pie chart legend
pieLegend :: forall msg. Array PieSlice -> E.Element msg
pieLegend slices =
  E.div_
    [ E.style "display" "flex"
    , E.style "flex-direction" "column"
    , E.style "gap" "8px"
    ]
    (map legendItem slices)

-- | Legend item
legendItem :: forall msg. PieSlice -> E.Element msg
legendItem slice =
  E.div_
    [ E.style "display" "flex"
    , E.style "align-items" "center"
    , E.style "gap" "8px"
    ]
    [ E.span_
        [ E.style "width" "12px"
        , E.style "height" "12px"
        , E.style "border-radius" "2px"
        , E.style "background-color" slice.color
        ]
        []
    , E.span_
        [ E.style "font-size" "14px"
        , E.style "color" "#6b7280"
        ]
        [ E.text (slice.label <> " (" <> show slice.value <> ")") ]
    ]
