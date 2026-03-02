-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                     // hydrogen // element // compound // charts // sparkline
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Sparkline — Compact inline chart for showing trends.

module Hydrogen.Element.Compound.Charts.Sparkline
  ( sparkline
  , SparklineProps
  , SparklineProp
  , defaultSparklineProps
  , sparklineWidth
  , sparklineHeight
  , sparklineColor
  , sparklineShowArea
  , sparklineShowDots
  ) where

import Prelude
  ( map
  , show
  , ($)
  , (<>)
  , (>)
  , (+)
  , (-)
  , (*)
  , (/)
  , (==)
  )

import Data.Array as Array
import Data.Array (foldl, length)
import Data.Int as Int
import Data.Maybe (Maybe(Just), fromMaybe)
import Hydrogen.Render.Element as E
import Hydrogen.Element.Compound.Charts.Types (min, max)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // sparkline
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sparkline properties
type SparklineProps =
  { width :: Number
  , height :: Number
  , color :: String
  , showArea :: Boolean
  , showDots :: Boolean
  , className :: String
  }

-- | Property modifier
type SparklineProp = SparklineProps -> SparklineProps

-- | Default sparkline properties
defaultSparklineProps :: SparklineProps
defaultSparklineProps =
  { width: 120.0
  , height: 30.0
  , color: "#3b82f6"
  , showArea: false
  , showDots: false
  , className: ""
  }

-- | Set width
sparklineWidth :: Number -> SparklineProp
sparklineWidth w props = props { width = w }

-- | Set height
sparklineHeight :: Number -> SparklineProp
sparklineHeight h props = props { height = h }

-- | Set line color
sparklineColor :: String -> SparklineProp
sparklineColor c props = props { color = c }

-- | Show/hide fill area
sparklineShowArea :: Boolean -> SparklineProp
sparklineShowArea b props = props { showArea = b }

-- | Show/hide data point dots
sparklineShowDots :: Boolean -> SparklineProp
sparklineShowDots b props = props { showDots = b }

-- | Sparkline component
sparkline :: forall msg. Array SparklineProp -> Array Number -> E.Element msg
sparkline propMods values =
  let
    props = foldl (\p f -> f p) defaultSparklineProps propMods
    padding = 4.0
    plotWidth = props.width - padding * 2.0
    plotHeight = props.height - padding * 2.0
    
    minVal = foldl min 0.0 values
    maxVal = foldl max 1.0 values
    range = if maxVal == minVal then 1.0 else maxVal - minVal
    
    pointCount = length values
    stepX = if pointCount > 1 then plotWidth / Int.toNumber (pointCount - 1) else 0.0
    
    points = Array.mapWithIndex (\i v ->
      let
        x = padding + Int.toNumber i * stepX
        y = padding + plotHeight - (v - minVal) / range * plotHeight
      in { x, y }
    ) values
    
    linePath = case Array.head points of
      Just first ->
        "M " <> show first.x <> " " <> show first.y <>
        foldl (\acc p -> acc <> " L " <> show p.x <> " " <> show p.y) "" 
              (fromMaybe [] (Array.tail points))
      _ -> ""
    
    areaPath = case Array.head points of
      Just first ->
        linePath <>
        " L " <> show (padding + plotWidth) <> " " <> show (padding + plotHeight) <>
        " L " <> show padding <> " " <> show (padding + plotHeight) <>
        " Z"
      _ -> ""
    
    dots = if props.showDots
      then map (\p ->
        E.circle_
          [ E.attr "cx" (show p.x)
          , E.attr "cy" (show p.y)
          , E.attr "r" "2"
          , E.attr "fill" props.color
          ]
      ) points
      else []
  in
    E.svg_
      [ E.attr "width" (show props.width)
      , E.attr "height" (show props.height)
      , E.attr "viewBox" ("0 0 " <> show props.width <> " " <> show props.height)
      ]
      ( (if props.showArea
          then [ E.path_
                   [ E.attr "d" areaPath
                   , E.attr "fill" props.color
                   , E.attr "fill-opacity" "0.2"
                   ]
               ]
          else [])
      <> [ E.path_
             [ E.attr "d" linePath
             , E.attr "fill" "none"
             , E.attr "stroke" props.color
             , E.attr "stroke-width" "2"
             , E.attr "stroke-linecap" "round"
             , E.attr "stroke-linejoin" "round"
             ]
         ]
      <> dots
      )
