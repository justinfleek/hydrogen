-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // chart3d // surface
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | 3D Surface Chart renderer.
-- |
-- | Renders isometric 3D surface/mesh charts using SVG. Displays height data
-- | as a 3D mesh with color mapping based on value.

module Hydrogen.Element.Compound.Widget.Chart3D.Surface
  ( chart3DSurface
  ) where

import Prelude
  ( class Show
  , show
  , (==)
  , (<>)
  , (+)
  , (-)
  , (*)
  , (/)
  , negate
  )

import Data.Array (foldl, index)
import Data.Int (toNumber)
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Hydrogen.Element.Compound.Widget.Chart3D.Projection (isoProject)
import Hydrogen.Element.Compound.Widget.Chart3D.Types (SurfaceConfig, SurfaceData)
import Hydrogen.Element.Compound.Widget.Chart3D.Util (arrayMax, arrayMin, generateIndices, interpolateColor)
import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // 3d surface chart
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a 3D surface/mesh chart.
-- |
-- | Displays height data as a 3D mesh with color mapping based on value.
-- | Uses isometric projection for 3D effect.
chart3DSurface :: forall msg. SurfaceConfig -> SurfaceData -> E.Element msg
chart3DSurface cfg surfaceData =
  let
    viewBox = "0 0 " <> show cfg.width <> " " <> show cfg.height
    
    -- Calculate data range
    minVal = arrayMin surfaceData.values
    maxVal = arrayMax surfaceData.values
    dataRange = if maxVal - minVal == 0.0 then 1.0 else maxVal - minVal
    
    -- Scale height to configured max
    scaleHeight :: Number -> Number
    scaleHeight v = ((v - minVal) / dataRange) * cfg.maxHeight
    
    -- Calculate centering offset
    gridWidth = toNumber (surfaceData.cols - 1) * cfg.cellSize
    gridDepth = toNumber (surfaceData.rows - 1) * cfg.cellSize
    
    containerCls = "rounded-lg border bg-card text-card-foreground p-4" <>
                   " " <> cfg.className
  in
    E.div_
      [ E.class_ containerCls ]
      [ -- Title
        renderSurfaceTitle cfg.title cfg.subtitle
      
      -- SVG chart
      , E.svg_
          [ E.attr "viewBox" viewBox
          , E.class_ "w-full h-full"
          , E.attr "preserveAspectRatio" "xMidYMid meet"
          ]
          [ E.g_
              [ E.attr "transform" ("translate(" <> show (cfg.width / 2.0) <> "," <> show (cfg.height / 2.0 + 50.0) <> ")") ]
              [ renderSurfaceMesh cfg surfaceData scaleHeight minVal dataRange gridWidth gridDepth ]
          ]
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // title render
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render title and subtitle for surface chart.
renderSurfaceTitle :: forall msg. Maybe String -> Maybe String -> E.Element msg
renderSurfaceTitle maybeTitle maybeSubtitle =
  case maybeTitle of
    Nothing -> E.text ""
    Just title ->
      E.div_
        [ E.class_ "mb-4" ]
        [ E.h3_
            [ E.class_ "text-lg font-semibold" ]
            [ E.text title ]
        , case maybeSubtitle of
            Nothing -> E.text ""
            Just subtitle ->
              E.p_
                [ E.class_ "text-sm text-muted-foreground" ]
                [ E.text subtitle ]
        ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // mesh render
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render the surface mesh as quadrilaterals.
renderSurfaceMesh :: forall msg. 
  SurfaceConfig -> 
  SurfaceData -> 
  (Number -> Number) -> 
  Number -> 
  Number -> 
  Number -> 
  Number -> 
  E.Element msg
renderSurfaceMesh cfg surfaceData scaleHeight minVal dataRange gridWidth gridDepth =
  let
    offsetX = negate gridWidth / 2.0
    offsetZ = negate gridDepth / 2.0
    
    -- Generate all cells (render back to front for proper layering)
    cells = generateSurfaceCells cfg surfaceData scaleHeight minVal dataRange offsetX offsetZ
  in
    E.g_
      [ E.class_ "surface-mesh" ]
      cells

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // cell render
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate all surface cells as SVG elements.
generateSurfaceCells :: forall msg. 
  SurfaceConfig -> 
  SurfaceData -> 
  (Number -> Number) -> 
  Number -> 
  Number -> 
  Number -> 
  Number -> 
  Array (E.Element msg)
generateSurfaceCells cfg surfaceData scaleHeight minVal dataRange offsetX offsetZ =
  let
    rows = surfaceData.rows
    cols = surfaceData.cols
    
    -- Get value at grid position
    getValue :: Int -> Int -> Number
    getValue row col = 
      let idx = row * cols + col
      in fromMaybe 0.0 (index surfaceData.values idx)
    
    -- Generate cells row by row (back to front)
    rowIndices = generateIndices (rows - 1)
    colIndices = generateIndices (cols - 1)
  in
    foldl (\acc rowIdx ->
      acc <> foldl (\acc2 colIdx ->
        let
          -- Four corners of the cell
          x0 = offsetX + toNumber colIdx * cfg.cellSize
          z0 = offsetZ + toNumber rowIdx * cfg.cellSize
          x1 = x0 + cfg.cellSize
          z1 = z0 + cfg.cellSize
          
          -- Height values at corners
          h00 = scaleHeight (getValue rowIdx colIdx)
          h10 = scaleHeight (getValue rowIdx (colIdx + 1))
          h01 = scaleHeight (getValue (rowIdx + 1) colIdx)
          h11 = scaleHeight (getValue (rowIdx + 1) (colIdx + 1))
          
          -- Average value for coloring
          avgValue = (getValue rowIdx colIdx + getValue rowIdx (colIdx + 1) + 
                     getValue (rowIdx + 1) colIdx + getValue (rowIdx + 1) (colIdx + 1)) / 4.0
          
          -- Color based on value
          colorT = (avgValue - minVal) / dataRange
          cellColor = interpolateColor cfg.colorMin cfg.colorMax colorT
          
          -- Project corners to 2D
          p00 = isoProject x0 h00 z0
          p10 = isoProject x1 h10 z0
          p11 = isoProject x1 h11 z1
          p01 = isoProject x0 h01 z1
          
          -- Path for quadrilateral
          pathD = "M " <> show p00.x <> " " <> show p00.y <>
                  " L " <> show p10.x <> " " <> show p10.y <>
                  " L " <> show p11.x <> " " <> show p11.y <>
                  " L " <> show p01.x <> " " <> show p01.y <> " Z"
        in
          acc2 <> [ E.path_
            [ E.attr "d" pathD
            , E.attr "fill" cellColor
            , E.attr "stroke" (if cfg.showGrid then "currentColor" else "none")
            , E.attr "stroke-opacity" "0.1"
            , E.attr "stroke-width" "0.5"
            ]
          ]
      ) [] colIndices
    ) [] rowIndices
