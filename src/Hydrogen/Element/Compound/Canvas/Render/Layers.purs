-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--              // hydrogen // element // compound // canvas // render // layers
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas Render Layers — Main canvas rendering and layer composition.
-- |
-- | ## Purpose
-- |
-- | Provides the main canvas render function and layer composition:
-- | - Main canvas render (composes all layers)
-- | - Background layer
-- | - Grid layer
-- | - Objects layer
-- | - Guides layer
-- | - Selection layer
-- | - Rulers layer
-- |
-- | ## Render Structure
-- |
-- | ```
-- | .canvas-container
-- |   .canvas-background
-- |   .canvas-grid-layer
-- |   .canvas-objects-layer
-- |   .canvas-guides-layer
-- |   .canvas-selection-layer
-- |   .canvas-rulers
-- | ```
-- |
-- | ## Dependencies
-- |
-- | - Canvas.State (CanvasState)
-- | - Canvas.Types (GridConfig, Guide)
-- | - Canvas.Selection (SelectionFrame, computeSelectionFrame)
-- | - Render.Types (RenderConfig, CanvasMsg)
-- | - Render.Helpers (sortByZIndex, viewportTransform)
-- | - Render submodules (Objects, Selection, Grid, Guides, Rulers)

module Hydrogen.Element.Compound.Canvas.Render.Layers
  ( -- * Main Render Function
    canvas
  , canvasWithConfig
  
  -- * Layer Render Functions
  , renderBackground
  , renderGrid
  , renderObjects
  , renderGuides
  , renderSelection
  , renderRulers
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , (<>)
  , ($)
  , map
  )

import Data.Array (filter)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Tuple (Tuple(Tuple))

import Hydrogen.Render.Element as E
import Hydrogen.Element.Compound.Canvas.Types as Types
import Hydrogen.Element.Compound.Canvas.State as State
import Hydrogen.Element.Compound.Canvas.Selection as Selection

import Hydrogen.Element.Compound.Canvas.Render.Types 
  ( CanvasMsg
  , RenderConfig
  , defaultRenderConfig
  )
import Hydrogen.Element.Compound.Canvas.Render.Helpers 
  ( sortByZIndex
  , viewportTransform
  )
import Hydrogen.Element.Compound.Canvas.Render.Objects (renderObjectWithCompositing)
import Hydrogen.Element.Compound.Canvas.Render.Selection as SelRender
import Hydrogen.Element.Compound.Canvas.Render.Grid (renderGridLines)
import Hydrogen.Element.Compound.Canvas.Render.Guides (renderGuide)
import Hydrogen.Element.Compound.Canvas.Render.Rulers 
  ( renderHorizontalRuler
  , renderVerticalRuler
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // main render function
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render the canvas with default configuration.
canvas :: State.CanvasState -> E.Element CanvasMsg
canvas = canvasWithConfig defaultRenderConfig

-- | Render the canvas with custom configuration.
canvasWithConfig :: RenderConfig -> State.CanvasState -> E.Element CanvasMsg
canvasWithConfig config state =
  E.div_
    ([ E.class_ "canvas-container" ] <> E.styles 
        [ Tuple "position" "relative"
        , Tuple "overflow" "hidden"
        , Tuple "width" "100%"
        , Tuple "height" "100%"
        ])
    [ renderBackground state
    , renderGrid config state
    , renderObjects config state
    , renderGuides config state
    , renderSelection config state
    , renderRulersIfEnabled config state
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // layer render functions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render canvas background.
renderBackground :: State.CanvasState -> E.Element CanvasMsg
renderBackground state =
  let canvasConfig = State.getConfig state
  in E.div_
    ([ E.class_ "canvas-background" ] <> E.styles
        [ Tuple "position" "absolute"
        , Tuple "top" "0"
        , Tuple "left" "0"
        , Tuple "width" "100%"
        , Tuple "height" "100%"
        , Tuple "background-color" canvasConfig.backgroundColor
        ])
    []

-- | Render grid layer.
renderGrid :: RenderConfig -> State.CanvasState -> E.Element CanvasMsg
renderGrid config state =
  let gridConfig = State.getGridConfig state
  in if Types.gridVisible gridConfig
     then E.div_
       ([ E.class_ "canvas-grid-layer" ] <> E.styles
           [ Tuple "position" "absolute"
           , Tuple "top" "0"
           , Tuple "left" "0"
           , Tuple "width" "100%"
           , Tuple "height" "100%"
           , Tuple "pointer-events" "none"
           , Tuple "opacity" (show config.gridOpacity)
           ])
       [ renderGridLines gridConfig state ]
     else E.empty

-- | Render objects layer.
renderObjects :: RenderConfig -> State.CanvasState -> E.Element CanvasMsg
renderObjects config state =
  let 
    objects = State.getObjects state
    sortedObjects = sortByZIndex objects
    viewport = State.getViewport state
  in E.div_
    ([ E.class_ "canvas-objects-layer" ] <> E.styles
        [ Tuple "position" "absolute"
        , Tuple "top" "0"
        , Tuple "left" "0"
        , Tuple "width" "100%"
        , Tuple "height" "100%"
        , Tuple "transform" (viewportTransform viewport)
        , Tuple "transform-origin" "0 0"
        ])
    (map (renderObjectWithCompositing config) sortedObjects)

-- | Render guides layer.
renderGuides :: RenderConfig -> State.CanvasState -> E.Element CanvasMsg
renderGuides config state =
  let guides = State.getGuides state
  in E.div_
    ([ E.class_ "canvas-guides-layer" ] <> E.styles
        [ Tuple "position" "absolute"
        , Tuple "top" "0"
        , Tuple "left" "0"
        , Tuple "width" "100%"
        , Tuple "height" "100%"
        , Tuple "pointer-events" "none"
        ])
    (map (renderGuide config) guides)

-- | Render selection layer (frame, handles, marquee).
renderSelection :: RenderConfig -> State.CanvasState -> E.Element CanvasMsg
renderSelection config state =
  let 
    selection = State.getSelection state
    objects = State.getObjects state
    selectedObjects = filter (\o -> Types.isSelected (Types.objectId o) selection) objects
    frame = Selection.computeSelectionFrame config.handleSize selectedObjects
  in E.div_
    ([ E.class_ "canvas-selection-layer" ] <> E.styles
        [ Tuple "position" "absolute"
        , Tuple "top" "0"
        , Tuple "left" "0"
        , Tuple "width" "100%"
        , Tuple "height" "100%"
        , Tuple "pointer-events" "none"
        ])
    (case frame of
      Nothing -> []
      Just f -> 
        [ SelRender.renderSelectionFrame config f
        , SelRender.renderSelectionHandles config f
        ])

-- | Render rulers if enabled.
renderRulersIfEnabled :: RenderConfig -> State.CanvasState -> E.Element CanvasMsg
renderRulersIfEnabled config state =
  if config.showRulers
    then renderRulers config state
    else E.empty

-- | Render rulers.
renderRulers :: RenderConfig -> State.CanvasState -> E.Element CanvasMsg
renderRulers config state =
  E.div_
    [ E.class_ "canvas-rulers"
    ]
    [ renderHorizontalRuler config state
    , renderVerticalRuler config state
    ]
