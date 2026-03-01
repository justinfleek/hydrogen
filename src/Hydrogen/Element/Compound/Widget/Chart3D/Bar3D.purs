-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                             // hydrogen // chart3d // bar3d
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | 3D Bar Chart renderer.
-- |
-- | Renders isometric 3D bar charts using SVG. Each bar has three visible
-- | faces (front, side, top) with gradient shading to simulate lighting.

module Hydrogen.Element.Compound.Widget.Chart3D.Bar3D
  ( chart3DBar
  ) where

import Prelude
  ( class Show
  , show
  , (<>)
  , (>)
  , (+)
  , (-)
  , (*)
  , (/)
  , negate
  )

import Data.Array (length, mapWithIndex)
import Data.Int (toNumber)
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Hydrogen.Element.Compound.Widget.Chart3D.Projection (isoProject)
import Hydrogen.Element.Compound.Widget.Chart3D.Types (Bar3DConfig, Bar3DData)
import Hydrogen.Element.Compound.Widget.Chart3D.Util (formatBarValue, getBar3DColor, getMaxBarValue)
import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // 3d bar chart
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render an isometric 3D bar chart.
-- |
-- | Each bar has three visible faces:
-- | - Front face (facing viewer)
-- | - Side face (right side)
-- | - Top face (top surface)
-- |
-- | Gradients simulate lighting for 3D effect.
chart3DBar :: forall msg. Bar3DConfig -> Array Bar3DData -> E.Element msg
chart3DBar cfg bars =
  let
    viewBox = "0 0 " <> show cfg.width <> " " <> show cfg.height
    floorY = cfg.height - 80.0
    
    -- Calculate max value for scaling
    maxVal = getMaxBarValue bars
    
    -- Calculate starting X position to center bars
    numBars = length bars
    totalWidth = toNumber numBars * cfg.barSpacing
    startX = negate (totalWidth - cfg.barSpacing) / 2.0
    
    containerCls = "rounded-lg border bg-card text-card-foreground p-4" <>
                   " " <> cfg.className
  in
    E.div_
      [ E.class_ containerCls ]
      [ -- Title
        renderBar3DTitle cfg.title cfg.subtitle
      
      -- SVG chart
      , E.svg_
          [ E.attr "viewBox" viewBox
          , E.class_ "w-full h-full"
          , E.attr "preserveAspectRatio" "xMidYMid meet"
          ]
          [ -- Gradient definitions
            renderBar3DGradients bars
          
          -- Chart group (translated to center)
          , E.g_
              [ E.attr "transform" ("translate(" <> show (cfg.width / 2.0) <> "," <> show floorY <> ")") ]
              [ -- Floor
                renderBar3DFloor cfg numBars
              
              -- Bars
              , E.g_
                  [ E.class_ "chart-3d-bars" ]
                  (mapWithIndex 
                    (renderBar3DBar cfg startX maxVal) 
                    bars)
              
              -- Labels
              , if cfg.showLabels
                  then renderBar3DLabels cfg startX bars
                  else E.text ""
              ]
          ]
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // title render
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render title and subtitle.
renderBar3DTitle :: forall msg. Maybe String -> Maybe String -> E.Element msg
renderBar3DTitle maybeTitle maybeSubtitle =
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
--                                                            // gradient render
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render gradient definitions for bar faces.
renderBar3DGradients :: forall msg. Array Bar3DData -> E.Element msg
renderBar3DGradients bars =
  E.defs_
    []
    (mapWithIndex (\idx bar ->
      let
        color = fromMaybe (getBar3DColor idx) bar.color
        colorLight = color <> "dd"  -- Lighter shade
        colorDark = color <> "99"   -- Darker shade
      in
        E.g_
          []
          [ -- Top gradient (brightest)
            E.element "linearGradient"
              [ E.attr "id" ("bar3d-top-" <> show idx)
              , E.attr "x1" "0%"
              , E.attr "y1" "0%"
              , E.attr "x2" "100%"
              , E.attr "y2" "100%"
              ]
              [ E.element "stop"
                  [ E.attr "offset" "0%"
                  , E.attr "stop-color" colorLight
                  ]
                  []
              , E.element "stop"
                  [ E.attr "offset" "100%"
                  , E.attr "stop-color" color
                  ]
                  []
              ]
          
          -- Front gradient
          , E.element "linearGradient"
              [ E.attr "id" ("bar3d-front-" <> show idx)
              , E.attr "x1" "0%"
              , E.attr "y1" "0%"
              , E.attr "x2" "0%"
              , E.attr "y2" "100%"
              ]
              [ E.element "stop"
                  [ E.attr "offset" "0%"
                  , E.attr "stop-color" color
                  ]
                  []
              , E.element "stop"
                  [ E.attr "offset" "100%"
                  , E.attr "stop-color" colorDark
                  ]
                  []
              ]
          
          -- Side gradient (darkest)
          , E.element "linearGradient"
              [ E.attr "id" ("bar3d-side-" <> show idx)
              , E.attr "x1" "0%"
              , E.attr "y1" "0%"
              , E.attr "x2" "100%"
              , E.attr "y2" "100%"
              ]
              [ E.element "stop"
                  [ E.attr "offset" "0%"
                  , E.attr "stop-color" colorDark
                  ]
                  []
              , E.element "stop"
                  [ E.attr "offset" "100%"
                  , E.attr "stop-color" (color <> "66")
                  ]
                  []
              ]
          ]
    ) bars)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // floor render
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render the isometric floor grid.
renderBar3DFloor :: forall msg. Bar3DConfig -> Int -> E.Element msg
renderBar3DFloor cfg numBars =
  let
    halfWidth = (toNumber numBars * cfg.barSpacing) / 2.0 + 40.0
    halfDepth = 60.0
    
    -- Four corners of floor in 3D space
    p1 = isoProject (negate halfWidth) 0.0 (negate halfDepth)
    p2 = isoProject halfWidth 0.0 (negate halfDepth)
    p3 = isoProject halfWidth 0.0 halfDepth
    p4 = isoProject (negate halfWidth) 0.0 halfDepth
    
    pathD = "M " <> show p1.x <> " " <> show p1.y <>
            " L " <> show p2.x <> " " <> show p2.y <>
            " L " <> show p3.x <> " " <> show p3.y <>
            " L " <> show p4.x <> " " <> show p4.y <> " Z"
  in
    E.path_
      [ E.attr "d" pathD
      , E.attr "fill" "currentColor"
      , E.attr "fill-opacity" "0.05"
      , E.attr "stroke" "currentColor"
      , E.attr "stroke-opacity" "0.1"
      , E.attr "stroke-width" "1"
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // bar render
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a single 3D bar with three faces.
renderBar3DBar :: forall msg. Bar3DConfig -> Number -> Number -> Int -> Bar3DData -> E.Element msg
renderBar3DBar cfg startX maxVal idx bar =
  let
    x = startX + toNumber idx * cfg.barSpacing
    h = if maxVal > 0.0 
        then (bar.value / maxVal) * cfg.maxBarHeight 
        else 0.0
    hw = cfg.barWidth / 2.0  -- half width
    hd = cfg.barDepth / 2.0  -- half depth
    
    base = isoProject x 0.0 0.0
    
    -- Front face vertices
    f1 = isoProject (x - hw) 0.0 hd
    f2 = isoProject (x + hw) 0.0 hd
    f3 = isoProject (x + hw) h hd
    f4 = isoProject (x - hw) h hd
    frontPath = "M " <> show f1.x <> " " <> show f1.y <>
                " L " <> show f2.x <> " " <> show f2.y <>
                " L " <> show f3.x <> " " <> show f3.y <>
                " L " <> show f4.x <> " " <> show f4.y <> " Z"
    
    -- Side face vertices
    s1 = isoProject (x + hw) 0.0 hd
    s2 = isoProject (x + hw) 0.0 (negate hd)
    s3 = isoProject (x + hw) h (negate hd)
    s4 = isoProject (x + hw) h hd
    sidePath = "M " <> show s1.x <> " " <> show s1.y <>
               " L " <> show s2.x <> " " <> show s2.y <>
               " L " <> show s3.x <> " " <> show s3.y <>
               " L " <> show s4.x <> " " <> show s4.y <> " Z"
    
    -- Top face vertices
    t1 = isoProject (x - hw) h hd
    t2 = isoProject (x + hw) h hd
    t3 = isoProject (x + hw) h (negate hd)
    t4 = isoProject (x - hw) h (negate hd)
    topPath = "M " <> show t1.x <> " " <> show t1.y <>
              " L " <> show t2.x <> " " <> show t2.y <>
              " L " <> show t3.x <> " " <> show t3.y <>
              " L " <> show t4.x <> " " <> show t4.y <> " Z"
    
    topCenter = isoProject x h 0.0
  in
    E.g_
      [ E.class_ "chart-3d-bar" ]
      [ -- Shadow ellipse
        E.element "ellipse"
          [ E.attr "cx" (show base.x)
          , E.attr "cy" (show (base.y + 5.0))
          , E.attr "rx" (show (cfg.barWidth * 0.6))
          , E.attr "ry" (show (cfg.barDepth * 0.4))
          , E.attr "fill" "currentColor"
          , E.attr "fill-opacity" "0.1"
          ]
          []
      
      -- Side face (render first, behind others)
      , E.path_
          [ E.attr "d" sidePath
          , E.attr "fill" ("url(#bar3d-side-" <> show idx <> ")")
          ]
      
      -- Front face
      , E.path_
          [ E.attr "d" frontPath
          , E.attr "fill" ("url(#bar3d-front-" <> show idx <> ")")
          ]
      
      -- Top face (render last, on top)
      , E.path_
          [ E.attr "d" topPath
          , E.attr "fill" ("url(#bar3d-top-" <> show idx <> ")")
          ]
      
      -- Value label
      , if cfg.showValues
          then E.text_
            [ E.attr "x" (show topCenter.x)
            , E.attr "y" (show (topCenter.y - 10.0))
            , E.attr "text-anchor" "middle"
            , E.attr "font-size" "11"
            , E.attr "fill" "currentColor"
            , E.attr "font-weight" "600"
            ]
            [ E.text (formatBarValue bar.value) ]
          else E.text ""
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // labels render
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render labels below bars.
renderBar3DLabels :: forall msg. Bar3DConfig -> Number -> Array Bar3DData -> E.Element msg
renderBar3DLabels cfg startX bars =
  E.g_
    [ E.class_ "chart-3d-labels" ]
    (mapWithIndex (\idx bar ->
      let
        x = startX + toNumber idx * cfg.barSpacing
        base = isoProject x 0.0 0.0
      in
        E.text_
          [ E.attr "x" (show base.x)
          , E.attr "y" (show (base.y + 25.0))
          , E.attr "text-anchor" "middle"
          , E.attr "font-size" "12"
          , E.attr "fill" "currentColor"
          , E.attr "fill-opacity" "0.7"
          ]
          [ E.text bar.label ]
    ) bars)
