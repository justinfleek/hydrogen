-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // element // compound // charts // scatter
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Scatter Plot — X/Y coordinate point visualization.

module Hydrogen.Element.Compound.Charts.Scatter
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
  ) where

import Prelude
  ( map
  , show
  , ($)
  , (<>)
  , (+)
  , (-)
  , (*)
  , (/)
  )

import Data.Array as Array
import Data.Array (foldl)
import Data.Int as Int
import Data.Maybe (Maybe, fromMaybe)
import Hydrogen.Render.Element as E
import Hydrogen.Element.Compound.Charts.Types (min, max)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // scatter plot
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scatter point data
type ScatterPoint =
  { x :: Number
  , y :: Number
  , label :: Maybe String
  , color :: Maybe String
  , size :: Maybe Number
  }

-- | Scatter plot properties
type ScatterPlotProps =
  { width :: Number
  , height :: Number
  , showGrid :: Boolean
  , showAxes :: Boolean
  , pointSize :: Number
  , defaultColor :: String
  , className :: String
  }

-- | Property modifier
type ScatterPlotProp = ScatterPlotProps -> ScatterPlotProps

-- | Default scatter plot properties
defaultScatterProps :: ScatterPlotProps
defaultScatterProps =
  { width: 400.0
  , height: 300.0
  , showGrid: true
  , showAxes: true
  , pointSize: 6.0
  , defaultColor: "#3b82f6"
  , className: ""
  }

-- | Set width
scatterWidth :: Number -> ScatterPlotProp
scatterWidth w props = props { width = w }

-- | Set height
scatterHeight :: Number -> ScatterPlotProp
scatterHeight h props = props { height = h }

-- | Show/hide grid
scatterShowGrid :: Boolean -> ScatterPlotProp
scatterShowGrid b props = props { showGrid = b }

-- | Show/hide axes
scatterShowAxes :: Boolean -> ScatterPlotProp
scatterShowAxes b props = props { showAxes = b }

-- | Set point size
scatterPointSize :: Number -> ScatterPlotProp
scatterPointSize s props = props { pointSize = s }

-- | Scatter plot component
scatterPlot :: forall msg. Array ScatterPlotProp -> Array ScatterPoint -> E.Element msg
scatterPlot propMods points =
  let
    props = foldl (\p f -> f p) defaultScatterProps propMods
    padding = 40.0
    plotWidth = props.width - padding * 2.0
    plotHeight = props.height - padding * 2.0
    
    xMin = foldl (\acc p -> min acc p.x) 0.0 points
    xMax = foldl (\acc p -> max acc p.x) 100.0 points
    yMin = foldl (\acc p -> min acc p.y) 0.0 points
    yMax = foldl (\acc p -> max acc p.y) 100.0 points
    
    scaleX x = padding + (x - xMin) / (xMax - xMin) * plotWidth
    scaleY y = props.height - padding - (y - yMin) / (yMax - yMin) * plotHeight
    
    gridLines = if props.showGrid then scatterGrid props padding plotWidth plotHeight else []
    axes = if props.showAxes then scatterAxes props padding plotWidth plotHeight else []
    
    pointElements = map (\p ->
      E.circle_
        [ E.attr "cx" (show (scaleX p.x))
        , E.attr "cy" (show (scaleY p.y))
        , E.attr "r" (show (fromMaybe props.pointSize p.size))
        , E.attr "fill" (fromMaybe props.defaultColor p.color)
        ]
    ) points
  in
    E.svg_
      [ E.attr "width" (show props.width)
      , E.attr "height" (show props.height)
      , E.attr "viewBox" ("0 0 " <> show props.width <> " " <> show props.height)
      ]
      (gridLines <> axes <> pointElements)

-- | Scatter plot grid
scatterGrid :: forall msg. ScatterPlotProps -> Number -> Number -> Number -> Array (E.Element msg)
scatterGrid props padding plotWidth plotHeight =
  let
    vLines = map (\i ->
      let x = padding + plotWidth * Int.toNumber i / 5.0
      in E.line_
        [ E.attr "x1" (show x)
        , E.attr "y1" (show padding)
        , E.attr "x2" (show x)
        , E.attr "y2" (show (props.height - padding))
        , E.attr "stroke" "#e5e7eb"
        , E.attr "stroke-width" "1"
        ]
    ) (Array.range 0 5)
    
    hLines = map (\i ->
      let y = padding + plotHeight * Int.toNumber i / 5.0
      in E.line_
        [ E.attr "x1" (show padding)
        , E.attr "y1" (show y)
        , E.attr "x2" (show (props.width - padding))
        , E.attr "y2" (show y)
        , E.attr "stroke" "#e5e7eb"
        , E.attr "stroke-width" "1"
        ]
    ) (Array.range 0 5)
  in
    vLines <> hLines

-- | Scatter plot axes
scatterAxes :: forall msg. ScatterPlotProps -> Number -> Number -> Number -> Array (E.Element msg)
scatterAxes props padding plotWidth plotHeight =
  [ E.line_
      [ E.attr "x1" (show padding)
      , E.attr "y1" (show (props.height - padding))
      , E.attr "x2" (show (props.width - padding))
      , E.attr "y2" (show (props.height - padding))
      , E.attr "stroke" "#374151"
      , E.attr "stroke-width" "2"
      ]
  , E.line_
      [ E.attr "x1" (show padding)
      , E.attr "y1" (show padding)
      , E.attr "x2" (show padding)
      , E.attr "y2" (show (props.height - padding))
      , E.attr "stroke" "#374151"
      , E.attr "stroke-width" "2"
      ]
  ]
