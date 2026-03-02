-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // element // compound // charts // gauge
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Gauge Chart — Semi-circular progress/value indicator.

module Hydrogen.Element.Compound.Charts.Gauge
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
  ) where

import Prelude
  ( show
  , ($)
  , (<>)
  , (>)
  , (+)
  , (-)
  , (*)
  , (/)
  )

import Data.Array (foldl)
import Hydrogen.Math.Core as Math
import Hydrogen.Render.Element as E
import Hydrogen.Element.Compound.Charts.Types (min, max)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // gauge chart
-- ═════════════════════════════════════════════════════════════════════════════

-- | Gauge data
type GaugeData =
  { value :: Number
  , label :: String
  }

-- | Gauge chart properties
type GaugeChartProps =
  { size :: Number
  , minValue :: Number
  , maxValue :: Number
  , thickness :: Number
  , showValue :: Boolean
  , color :: String
  , backgroundColor :: String
  , className :: String
  }

-- | Property modifier
type GaugeChartProp = GaugeChartProps -> GaugeChartProps

-- | Default gauge properties
defaultGaugeProps :: GaugeChartProps
defaultGaugeProps =
  { size: 200.0
  , minValue: 0.0
  , maxValue: 100.0
  , thickness: 20.0
  , showValue: true
  , color: "#3b82f6"
  , backgroundColor: "#e5e7eb"
  , className: ""
  }

-- | Set gauge size
gaugeSize :: Number -> GaugeChartProp
gaugeSize s props = props { size = s }

-- | Set minimum value
gaugeMin :: Number -> GaugeChartProp
gaugeMin m props = props { minValue = m }

-- | Set maximum value
gaugeMax :: Number -> GaugeChartProp
gaugeMax m props = props { maxValue = m }

-- | Set arc thickness
gaugeThickness :: Number -> GaugeChartProp
gaugeThickness t props = props { thickness = t }

-- | Show/hide value display
gaugeShowValue :: Boolean -> GaugeChartProp
gaugeShowValue b props = props { showValue = b }

-- | Set gauge color
gaugeColor :: String -> GaugeChartProp
gaugeColor c props = props { color = c }

-- | Gauge chart component
gaugeChart :: forall msg. Array GaugeChartProp -> GaugeData -> E.Element msg
gaugeChart propMods gaugeData =
  let
    props = foldl (\p f -> f p) defaultGaugeProps propMods
    cx = props.size / 2.0
    cy = props.size / 2.0
    radius = props.size / 2.0 - props.thickness / 2.0 - 10.0
    
    normalizedValue = (gaugeData.value - props.minValue) / (props.maxValue - props.minValue)
    clampedValue = max 0.0 (min 1.0 normalizedValue)
    
    startAngle = Math.pi
    endAngle = 0.0
    valueAngle = startAngle - clampedValue * Math.pi
    
    bgPath = arcPath cx cy radius startAngle endAngle props.thickness
    valuePath = arcPath cx cy radius startAngle valueAngle props.thickness
  in
    E.svg_
      [ E.attr "width" (show props.size)
      , E.attr "height" (show (props.size / 2.0 + 20.0))
      , E.attr "viewBox" ("0 0 " <> show props.size <> " " <> show (props.size / 2.0 + 20.0))
      ]
      [ E.path_
          [ E.attr "d" bgPath
          , E.attr "fill" "none"
          , E.attr "stroke" props.backgroundColor
          , E.attr "stroke-width" (show props.thickness)
          , E.attr "stroke-linecap" "round"
          ]
      , E.path_
          [ E.attr "d" valuePath
          , E.attr "fill" "none"
          , E.attr "stroke" props.color
          , E.attr "stroke-width" (show props.thickness)
          , E.attr "stroke-linecap" "round"
          ]
      , if props.showValue
          then E.text_
            [ E.attr "x" (show cx)
            , E.attr "y" (show (cy + 10.0))
            , E.attr "text-anchor" "middle"
            , E.style "font-size" "24px"
            , E.style "font-weight" "bold"
            , E.style "fill" "#1f2937"
            ]
            [ E.text (show gaugeData.value) ]
          else E.text ""
      , E.text_
          [ E.attr "x" (show cx)
          , E.attr "y" (show (cy + 35.0))
          , E.attr "text-anchor" "middle"
          , E.style "font-size" "14px"
          , E.style "fill" "#6b7280"
          ]
          [ E.text gaugeData.label ]
      ]

-- | Generate arc path
arcPath :: Number -> Number -> Number -> Number -> Number -> Number -> String
arcPath cx cy radius startAngle endAngle thickness =
  let
    x1 = cx + radius * Math.cos startAngle
    y1 = cy + radius * Math.sin startAngle
    x2 = cx + radius * Math.cos endAngle
    y2 = cy + radius * Math.sin endAngle
    largeArc = if Math.abs (endAngle - startAngle) > Math.pi then "1" else "0"
    sweep = if endAngle > startAngle then "1" else "0"
  in
    "M " <> show x1 <> " " <> show y1 <>
    " A " <> show radius <> " " <> show radius <> " 0 " <> largeArc <> " " <> sweep <> " " <> show x2 <> " " <> show y2
