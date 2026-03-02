-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // element // compound // charts // heatmap
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Heatmap — Color-coded matrix visualization.

module Hydrogen.Element.Compound.Charts.Heatmap
  ( heatmap
  , HeatmapProps
  , HeatmapProp
  , HeatmapData
  , HeatmapCell
  , defaultHeatmapProps
  , heatmapCellSize
  , heatmapGap
  , heatmapShowLabels
  , heatmapColorScale
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
import Data.Array (foldl, length)
import Data.Int as Int
import Hydrogen.Render.Element as E
import Hydrogen.Element.Compound.Charts.Types 
  ( ColorScale(Sequential)
  , valueToColor
  , min
  , max
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // heatmap
-- ═════════════════════════════════════════════════════════════════════════════

-- | Heatmap cell
type HeatmapCell =
  { row :: Int
  , col :: Int
  , value :: Number
  }

-- | Heatmap data
type HeatmapData =
  { cells :: Array HeatmapCell
  , rowLabels :: Array String
  , colLabels :: Array String
  }

-- | Heatmap properties
type HeatmapProps =
  { cellSize :: Number
  , gap :: Number
  , showLabels :: Boolean
  , colorScale :: ColorScale
  , className :: String
  }

-- | Property modifier
type HeatmapProp = HeatmapProps -> HeatmapProps

-- | Default heatmap properties
defaultHeatmapProps :: HeatmapProps
defaultHeatmapProps =
  { cellSize: 40.0
  , gap: 2.0
  , showLabels: true
  , colorScale: Sequential
  , className: ""
  }

-- | Set cell size
heatmapCellSize :: Number -> HeatmapProp
heatmapCellSize s props = props { cellSize = s }

-- | Set gap between cells
heatmapGap :: Number -> HeatmapProp
heatmapGap g props = props { gap = g }

-- | Show/hide labels
heatmapShowLabels :: Boolean -> HeatmapProp
heatmapShowLabels b props = props { showLabels = b }

-- | Set color scale
heatmapColorScale :: ColorScale -> HeatmapProp
heatmapColorScale s props = props { colorScale = s }

-- | Heatmap component
heatmap :: forall msg. Array HeatmapProp -> HeatmapData -> E.Element msg
heatmap propMods heatmapData =
  let
    props = foldl (\p f -> f p) defaultHeatmapProps propMods
    
    minVal = foldl (\acc c -> min acc c.value) 0.0 heatmapData.cells
    maxVal = foldl (\acc c -> max acc c.value) 1.0 heatmapData.cells
    
    rows = length heatmapData.rowLabels
    cols = length heatmapData.colLabels
    labelOffset = if props.showLabels then 60.0 else 0.0
    width = labelOffset + Int.toNumber cols * (props.cellSize + props.gap)
    height = labelOffset + Int.toNumber rows * (props.cellSize + props.gap)
    
    cellElements = map (\cell ->
      let
        x = labelOffset + Int.toNumber cell.col * (props.cellSize + props.gap)
        y = labelOffset + Int.toNumber cell.row * (props.cellSize + props.gap)
        normalizedValue = (cell.value - minVal) / (maxVal - minVal)
        color = valueToColor props.colorScale normalizedValue
      in
        E.rect_
          [ E.attr "x" (show x)
          , E.attr "y" (show y)
          , E.attr "width" (show props.cellSize)
          , E.attr "height" (show props.cellSize)
          , E.attr "fill" color
          , E.attr "rx" "4"
          ]
    ) heatmapData.cells
    
    rowLabelElements = if props.showLabels
      then Array.mapWithIndex (\i label ->
        E.text_
          [ E.attr "x" (show (labelOffset - 8.0))
          , E.attr "y" (show (labelOffset + Int.toNumber i * (props.cellSize + props.gap) + props.cellSize / 2.0))
          , E.attr "text-anchor" "end"
          , E.attr "dominant-baseline" "middle"
          , E.style "font-size" "12px"
          , E.style "fill" "#6b7280"
          ]
          [ E.text label ]
      ) heatmapData.rowLabels
      else []
    
    colLabelElements = if props.showLabels
      then Array.mapWithIndex (\i label ->
        E.text_
          [ E.attr "x" (show (labelOffset + Int.toNumber i * (props.cellSize + props.gap) + props.cellSize / 2.0))
          , E.attr "y" (show (labelOffset - 8.0))
          , E.attr "text-anchor" "middle"
          , E.style "font-size" "12px"
          , E.style "fill" "#6b7280"
          ]
          [ E.text label ]
      ) heatmapData.colLabels
      else []
  in
    E.svg_
      [ E.attr "width" (show width)
      , E.attr "height" (show height)
      , E.attr "viewBox" ("0 0 " <> show width <> " " <> show height)
      ]
      (cellElements <> rowLabelElements <> colLabelElements)
