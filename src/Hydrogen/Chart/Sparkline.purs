-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                      // hydrogen // sparkline
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Sparkline charts
-- |
-- | Inline mini-charts for displaying trends.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Chart.Sparkline as Sparkline
-- |
-- | -- Line sparkline
-- | Sparkline.sparkline 
-- |   { data: [10.0, 25.0, 15.0, 30.0, 20.0]
-- |   , width: 100
-- |   , height: 24
-- |   }
-- |
-- | -- With custom color
-- | Sparkline.sparklineWithProps
-- |   { data: values
-- |   , width: 100
-- |   , height: 24
-- |   , strokeColor: "text-primary"
-- |   , fillColor: Just "text-primary/20"
-- |   }
-- | ```
module Hydrogen.Chart.Sparkline
  ( -- * Sparkline
    sparkline
  , sparklineWithProps
  , SparklineConfig
  , SparklineProps
  , defaultProps
    -- * Variants
  , sparklineBar
  , sparklineDot
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl, maximum, minimum)
import Data.Int (toNumber)
import Data.Maybe (Maybe(Nothing, Just), fromMaybe)
import Data.String as String
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Hydrogen.UI.Core (svgNS, svgCls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // config
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Basic sparkline configuration
type SparklineConfig =
  { data :: Array Number
  , width :: Int
  , height :: Int
  }

-- | Full sparkline properties
type SparklineProps =
  { data :: Array Number
  , width :: Int
  , height :: Int
  , strokeColor :: String
  , strokeWidth :: Number
  , fillColor :: Maybe String
  , className :: String
  }

-- | Default sparkline properties
defaultProps :: SparklineProps
defaultProps =
  { data: []
  , width: 100
  , height: 24
  , strokeColor: "stroke-current"
  , strokeWidth: 1.5
  , fillColor: Nothing
  , className: ""
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // line sparkline
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Simple sparkline with basic config
sparkline :: forall w i. SparklineConfig -> HH.HTML w i
sparkline config = sparklineWithProps
  defaultProps
    { data = config.data
    , width = config.width
    , height = config.height
    }

-- | Sparkline with full props
sparklineWithProps :: forall w i. SparklineProps -> HH.HTML w i
sparklineWithProps props =
  let
    points = normalizeData props.data props.width props.height
    pathData = pointsToPath points
    fillPathData = pointsToFillPath points props.height
  in
    HH.elementNS svgNS (HH.ElemName "svg")
      [ svgCls [ props.className ]
      , HP.attr (HH.AttrName "viewBox") ("0 0 " <> show props.width <> " " <> show props.height)
      , HP.attr (HH.AttrName "width") (show props.width)
      , HP.attr (HH.AttrName "height") (show props.height)
      , HP.attr (HH.AttrName "preserveAspectRatio") "none"
      ]
      ( ( case props.fillColor of
            Just fill ->
              [ HH.elementNS svgNS (HH.ElemName "path")
                  [ HP.attr (HH.AttrName "d") fillPathData
                  , svgCls [ "fill-current", fill ]
                  ]
                  []
              ]
            Nothing -> []
        ) <>
        [ HH.elementNS svgNS (HH.ElemName "path")
            [ HP.attr (HH.AttrName "d") pathData
            , HP.attr (HH.AttrName "fill") "none"
            , svgCls [ props.strokeColor ]
            , HP.attr (HH.AttrName "stroke-width") (show props.strokeWidth)
            , HP.attr (HH.AttrName "stroke-linecap") "round"
            , HP.attr (HH.AttrName "stroke-linejoin") "round"
            ]
            []
        ]
      )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // bar sparkline
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Bar sparkline
sparklineBar :: forall w i. SparklineConfig -> HH.HTML w i
sparklineBar config =
  let
    minVal = fromMaybe 0.0 (minimum config.data)
    maxVal = fromMaybe 1.0 (maximum config.data)
    range = if maxVal == minVal then 1.0 else maxVal - minVal
    barWidth = toNumber config.width / toNumber (Array.length config.data)
    gap = barWidth * 0.2
    
    bars = Array.mapWithIndex (\i val ->
      let
        normalizedHeight = ((val - minVal) / range) * toNumber config.height
        x = toNumber i * barWidth + gap / 2.0
        y = toNumber config.height - normalizedHeight
      in
        HH.elementNS svgNS (HH.ElemName "rect")
          [ HP.attr (HH.AttrName "x") (show x)
          , HP.attr (HH.AttrName "y") (show y)
          , HP.attr (HH.AttrName "width") (show (barWidth - gap))
          , HP.attr (HH.AttrName "height") (show normalizedHeight)
          , HP.attr (HH.AttrName "rx") "1"
          , svgCls [ "fill-current" ]
          ]
          []
    ) config.data
  in
    HH.elementNS svgNS (HH.ElemName "svg")
      [ HP.attr (HH.AttrName "viewBox") ("0 0 " <> show config.width <> " " <> show config.height)
      , HP.attr (HH.AttrName "width") (show config.width)
      , HP.attr (HH.AttrName "height") (show config.height)
      ]
      bars

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // dot sparkline
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Dot sparkline
sparklineDot :: forall w i. SparklineConfig -> HH.HTML w i
sparklineDot config =
  let
    points = normalizeData config.data config.width config.height
    dots = map (\p ->
      HH.elementNS svgNS (HH.ElemName "circle")
        [ HP.attr (HH.AttrName "cx") (show p.x)
        , HP.attr (HH.AttrName "cy") (show p.y)
        , HP.attr (HH.AttrName "r") "2"
        , svgCls [ "fill-current" ]
        ]
        []
    ) points
  in
    HH.elementNS svgNS (HH.ElemName "svg")
      [ HP.attr (HH.AttrName "viewBox") ("0 0 " <> show config.width <> " " <> show config.height)
      , HP.attr (HH.AttrName "width") (show config.width)
      , HP.attr (HH.AttrName "height") (show config.height)
      ]
      dots

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

type Point = { x :: Number, y :: Number }

normalizeData :: Array Number -> Int -> Int -> Array Point
normalizeData data' width height =
  let
    len = Array.length data'
    minVal = fromMaybe 0.0 (minimum data')
    maxVal = fromMaybe 1.0 (maximum data')
    range = if maxVal == minVal then 1.0 else maxVal - minVal
    padding = 2.0
  in
    Array.mapWithIndex (\i val ->
      { x: if len <= 1 then toNumber width / 2.0 
           else padding + (toNumber i / toNumber (len - 1)) * (toNumber width - padding * 2.0)
      , y: padding + (1.0 - (val - minVal) / range) * (toNumber height - padding * 2.0)
      }
    ) data'

pointsToPath :: Array Point -> String
pointsToPath points =
  case Array.uncons points of
    Nothing -> ""
    Just { head, tail } ->
      "M " <> show head.x <> " " <> show head.y <>
      foldl (\acc p -> acc <> " L " <> show p.x <> " " <> show p.y) "" tail

pointsToFillPath :: Array Point -> Int -> String
pointsToFillPath points height =
  case Array.uncons points of
    Nothing -> ""
    Just { head, tail } ->
      let
        lastPoint = fromMaybe head (Array.last points)
        linePath = pointsToPath points
      in
        linePath <> 
        " L " <> show lastPoint.x <> " " <> show height <>
        " L " <> show head.x <> " " <> show height <>
        " Z"
