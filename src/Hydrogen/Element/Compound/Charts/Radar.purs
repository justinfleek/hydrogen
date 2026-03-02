-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // element // compound // charts // radar
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Radar Chart — Multi-axis comparison chart (spider chart).

module Hydrogen.Element.Compound.Charts.Radar
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
  ) where

import Prelude
  ( map
  , show
  , negate
  , ($)
  , (<>)
  , (<)
  , (>)
  , (+)
  , (-)
  , (*)
  , (/)
  )

import Data.Array as Array
import Data.Array (foldl, length)
import Data.Int as Int
import Hydrogen.Math.Core as Math
import Hydrogen.Render.Element as E
import Hydrogen.Element.Compound.Charts.Types (max)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // radar chart
-- ═════════════════════════════════════════════════════════════════════════════

-- | Radar series data
type RadarSeries =
  { values :: Array Number
  , color :: String
  , label :: String
  }

-- | Radar chart data
type RadarData =
  { axes :: Array String
  , series :: Array RadarSeries
  }

-- | Radar chart properties
type RadarChartProps =
  { size :: Number
  , showGrid :: Boolean
  , showLabels :: Boolean
  , fillOpacity :: Number
  , gridLevels :: Int
  , className :: String
  }

-- | Property modifier
type RadarChartProp = RadarChartProps -> RadarChartProps

-- | Default radar chart properties
defaultRadarProps :: RadarChartProps
defaultRadarProps =
  { size: 300.0
  , showGrid: true
  , showLabels: true
  , fillOpacity: 0.3
  , gridLevels: 5
  , className: ""
  }

-- | Set chart size
radarSize :: Number -> RadarChartProp
radarSize s props = props { size = s }

-- | Show/hide grid
radarShowGrid :: Boolean -> RadarChartProp
radarShowGrid b props = props { showGrid = b }

-- | Show/hide axis labels
radarShowLabels :: Boolean -> RadarChartProp
radarShowLabels b props = props { showLabels = b }

-- | Set fill opacity
radarFillOpacity :: Number -> RadarChartProp
radarFillOpacity o props = props { fillOpacity = o }

-- | Radar chart component
radarChart :: forall msg. Array RadarChartProp -> RadarData -> E.Element msg
radarChart propMods radarData =
  let
    props = foldl (\p f -> f p) defaultRadarProps propMods
    cx = props.size / 2.0
    cy = props.size / 2.0
    radius = props.size / 2.0 - 40.0
    axisCount = length radarData.axes
    angleStep = Math.tau / Int.toNumber axisCount
    
    gridCircles = if props.showGrid
      then map (\level -> gridCircle cx cy (radius * Int.toNumber level / Int.toNumber props.gridLevels)) 
               (Array.range 1 props.gridLevels)
      else []
    
    axisLines = Array.mapWithIndex (\i _ ->
      let angle = negate (Math.pi / 2.0) + Int.toNumber i * angleStep
      in axisLine cx cy radius angle
    ) radarData.axes
    
    axisLabels = if props.showLabels
      then Array.mapWithIndex (\i label ->
        let angle = negate (Math.pi / 2.0) + Int.toNumber i * angleStep
        in axisLabel cx cy (radius + 20.0) angle label
      ) radarData.axes
      else []
    
    dataPolygons = map (\series -> 
      radarPolygon cx cy radius angleStep series.values series.color props.fillOpacity
    ) radarData.series
  in
    E.svg_
      [ E.attr "width" (show props.size)
      , E.attr "height" (show props.size)
      , E.attr "viewBox" ("0 0 " <> show props.size <> " " <> show props.size)
      ]
      (gridCircles <> axisLines <> dataPolygons <> axisLabels)

-- | Grid circle
gridCircle :: forall msg. Number -> Number -> Number -> E.Element msg
gridCircle cx cy r =
  E.circle_
    [ E.attr "cx" (show cx)
    , E.attr "cy" (show cy)
    , E.attr "r" (show r)
    , E.attr "fill" "none"
    , E.attr "stroke" "#e5e7eb"
    , E.attr "stroke-width" "1"
    ]

-- | Axis line
axisLine :: forall msg. Number -> Number -> Number -> Number -> E.Element msg
axisLine cx cy radius angle =
  let
    x2 = cx + radius * Math.cos angle
    y2 = cy + radius * Math.sin angle
  in
    E.line_
      [ E.attr "x1" (show cx)
      , E.attr "y1" (show cy)
      , E.attr "x2" (show x2)
      , E.attr "y2" (show y2)
      , E.attr "stroke" "#d1d5db"
      , E.attr "stroke-width" "1"
      ]

-- | Axis label
axisLabel :: forall msg. Number -> Number -> Number -> Number -> String -> E.Element msg
axisLabel cx cy radius angle label =
  let
    x = cx + radius * Math.cos angle
    y = cy + radius * Math.sin angle
    anchor = if Math.cos angle < negate 0.01 then "end"
             else if Math.cos angle > 0.01 then "start"
             else "middle"
  in
    E.text_
      [ E.attr "x" (show x)
      , E.attr "y" (show y)
      , E.attr "text-anchor" anchor
      , E.attr "dominant-baseline" "middle"
      , E.style "font-size" "12px"
      , E.style "fill" "#6b7280"
      ]
      [ E.text label ]

-- | Radar data polygon
radarPolygon :: forall msg. Number -> Number -> Number -> Number -> Array Number -> String -> Number -> E.Element msg
radarPolygon cx cy radius angleStep values color opacity =
  let
    maxValue = foldl max 0.0 values
    normalizedValues = map (\v -> if maxValue > 0.0 then v / maxValue else 0.0) values
    
    points = Array.mapWithIndex (\i v ->
      let 
        angle = negate (Math.pi / 2.0) + Int.toNumber i * angleStep
        r = radius * v
        x = cx + r * Math.cos angle
        y = cy + r * Math.sin angle
      in show x <> "," <> show y
    ) normalizedValues
    
    pointsStr = Array.intercalate " " points
  in
    E.g_ []
      [ E.polygon_
          [ E.attr "points" pointsStr
          , E.attr "fill" color
          , E.attr "fill-opacity" (show opacity)
          , E.attr "stroke" color
          , E.attr "stroke-width" "2"
          ]
      ]
