-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--            // hydrogen // element // compound // canvas // render // selection
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas Render Selection — Selection visualization rendering.
-- |
-- | ## Purpose
-- |
-- | Renders selection UI elements:
-- | - Selection frame (bounding box outline)
-- | - Selection handles (resize/rotate controls)
-- | - Marquee rectangle (drag selection)
-- | - Lasso path (freeform selection)
-- |
-- | ## Dependencies
-- |
-- | - Canvas.Selection (SelectionFrame, handles, marquee, lasso)
-- | - Schema.Gestural.Selection (rect accessors)
-- | - Render.Types (RenderConfig, CanvasMsg)
-- | - Render.Helpers (handleCursor)

module Hydrogen.Element.Compound.Canvas.Render.Selection
  ( -- * Selection Rendering
    renderSelectionFrame
  , renderSelectionHandles
  , renderMarquee
  , renderLasso
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , (<>)
  , (<)
  , (/)
  , (-) 
  , map
  )

import Data.Array (length)
import Data.Tuple (Tuple(Tuple))

import Hydrogen.Render.Element as E
import Hydrogen.Element.Compound.Canvas.Selection as Selection
import Hydrogen.Schema.Gestural.Selection as GSelection
import Hydrogen.Element.Compound.Canvas.Render.Types (CanvasMsg, RenderConfig)
import Hydrogen.Element.Compound.Canvas.Render.Helpers (handleCursor, lassoToPath)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // selection rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render selection frame (bounding box outline).
renderSelectionFrame :: RenderConfig -> Selection.SelectionFrame -> E.Element CanvasMsg
renderSelectionFrame config frame =
  let bounds = Selection.frameBounds frame
  in E.div_
    ([ E.class_ "selection-frame" ] <> E.styles
        [ Tuple "position" "absolute"
        , Tuple "left" (show bounds.x <> "px")
        , Tuple "top" (show bounds.y <> "px")
        , Tuple "width" (show bounds.width <> "px")
        , Tuple "height" (show bounds.height <> "px")
        , Tuple "border" (show config.selectionWidth <> "px solid " <> config.selectionColor)
        , Tuple "pointer-events" "none"
        ])
    []

-- | Render selection handles.
renderSelectionHandles :: RenderConfig -> Selection.SelectionFrame -> E.Element CanvasMsg
renderSelectionHandles config frame =
  let handles = Selection.frameHandles frame
  in E.div_
    [ E.class_ "selection-handles" ]
    (map (renderHandle config) handles)

-- | Render a single handle.
renderHandle :: RenderConfig -> Selection.SelectionHandle -> E.Element CanvasMsg
renderHandle config handle =
  let 
    pos = Selection.handlePosition handle
    size = Selection.handleSize handle
    halfSize = size / 2.0
  in E.div_
    ([ E.class_ ("selection-handle handle-" <> show (Selection.handleType handle)) ] <> E.styles
        [ Tuple "position" "absolute"
        , Tuple "left" (show (pos.x - halfSize) <> "px")
        , Tuple "top" (show (pos.y - halfSize) <> "px")
        , Tuple "width" (show size <> "px")
        , Tuple "height" (show size <> "px")
        , Tuple "background-color" "#ffffff"
        , Tuple "border" ("1px solid " <> config.selectionColor)
        , Tuple "cursor" (handleCursor (Selection.handleType handle))
        ])
    []

-- | Render marquee selection rectangle.
renderMarquee :: RenderConfig -> Selection.MarqueeState -> E.Element CanvasMsg
renderMarquee config marquee =
  if Selection.marqueeActive marquee
    then 
      let rect = Selection.marqueeRect marquee
      in E.div_
        ([ E.class_ "selection-marquee" ] <> E.styles
            [ Tuple "position" "absolute"
            , Tuple "left" (show (GSelection.rectX rect) <> "px")
            , Tuple "top" (show (GSelection.rectY rect) <> "px")
            , Tuple "width" (show (GSelection.rectWidth rect) <> "px")
            , Tuple "height" (show (GSelection.rectHeight rect) <> "px")
            , Tuple "border" ("1px dashed " <> config.marqueeColor)
            , Tuple "background-color" config.marqueeColor
            , Tuple "opacity" (show config.marqueeOpacity)
            , Tuple "pointer-events" "none"
            ])
        []
    else E.empty

-- | Render lasso selection path.
renderLasso :: RenderConfig -> Selection.LassoPath -> E.Element CanvasMsg
renderLasso config lasso =
  let points = Selection.lassoPoints lasso
  in if length points < 2
     then E.empty
     else E.svg_
       ([ E.class_ "selection-lasso" ] <> E.styles
           [ Tuple "position" "absolute"
           , Tuple "top" "0"
           , Tuple "left" "0"
           , Tuple "width" "100%"
           , Tuple "height" "100%"
           , Tuple "pointer-events" "none"
           ])
       [ E.path_
           [ E.attr "d" (lassoToPath points)
           , E.attr "fill" config.marqueeColor
           , E.attr "fill-opacity" (show config.marqueeOpacity)
           , E.attr "stroke" config.marqueeColor
           , E.attr "stroke-width" "1"
           , E.attr "stroke-dasharray" "4 2"
           ]
       ]
