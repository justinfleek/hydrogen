-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--              // hydrogen // element // compound // canvas // render // rulers
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas Render Rulers — Ruler rendering.
-- |
-- | ## Purpose
-- |
-- | Renders measurement rulers for canvas:
-- | - Horizontal ruler (top edge)
-- | - Vertical ruler (left edge)
-- |
-- | Rulers provide visual measurement reference.
-- |
-- | ## Dependencies
-- |
-- | - Canvas.State (CanvasState)
-- | - Render.Types (RenderConfig, CanvasMsg)

module Hydrogen.Element.Compound.Canvas.Render.Rulers
  ( -- * Ruler Rendering
    renderHorizontalRuler
  , renderVerticalRuler
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , (<>)
  )

import Data.Tuple (Tuple(Tuple))

import Hydrogen.Render.Element as E
import Hydrogen.Element.Compound.Canvas.State as State
import Hydrogen.Element.Compound.Canvas.Render.Types (CanvasMsg, RenderConfig)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // ruler rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render horizontal ruler.
renderHorizontalRuler :: RenderConfig -> State.CanvasState -> E.Element CanvasMsg
renderHorizontalRuler config _state =
  E.div_
    ([ E.class_ "ruler ruler-horizontal" ] <> E.styles
        [ Tuple "position" "absolute"
        , Tuple "top" "0"
        , Tuple "left" (show config.rulerSize <> "px")
        , Tuple "right" "0"
        , Tuple "height" (show config.rulerSize <> "px")
        , Tuple "background-color" "#2a2a2a"
        , Tuple "border-bottom" "1px solid #404040"
        ])
    []

-- | Render vertical ruler.
renderVerticalRuler :: RenderConfig -> State.CanvasState -> E.Element CanvasMsg
renderVerticalRuler config _state =
  E.div_
    ([ E.class_ "ruler ruler-vertical" ] <> E.styles
        [ Tuple "position" "absolute"
        , Tuple "top" (show config.rulerSize <> "px")
        , Tuple "left" "0"
        , Tuple "bottom" "0"
        , Tuple "width" (show config.rulerSize <> "px")
        , Tuple "background-color" "#2a2a2a"
        , Tuple "border-right" "1px solid #404040"
        ])
    []
