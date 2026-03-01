-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--              // hydrogen // element // compound // canvas // render // objects
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas Render Objects — Object rendering functions.
-- |
-- | ## Purpose
-- |
-- | Renders individual canvas objects with proper compositing:
-- | - Basic object rendering
-- | - Full compositing (blend mode, opacity, visibility)
-- |
-- | ## Compositing Order
-- |
-- | Objects are rendered with:
-- | 1. Position and bounds
-- | 2. Blend mode (CSS mix-blend-mode)
-- | 3. Opacity
-- | 4. Visibility
-- |
-- | ## Dependencies
-- |
-- | - Canvas.Types (CanvasObject)
-- | - Render.Types (RenderConfig, CanvasMsg)
-- | - Render.Helpers (blendModeToCSS, showObjectId)

module Hydrogen.Element.Compound.Canvas.Render.Objects
  ( -- * Object Rendering
    renderObject
  , renderObjectWithCompositing
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , (<>)
  , ($)
  )

import Data.Tuple (Tuple(Tuple))

import Hydrogen.Render.Element as E
import Hydrogen.Element.Compound.Canvas.Types as Types
import Hydrogen.Element.Compound.Canvas.Render.Types (CanvasMsg, RenderConfig)
import Hydrogen.Element.Compound.Canvas.Render.Helpers (blendModeToCSS, showObjectId)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // object rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a single object.
renderObject :: Types.CanvasObject -> E.Element CanvasMsg
renderObject obj =
  let bounds = Types.objectBounds obj
  in E.div_
    ([ E.class_ "canvas-object"
     , E.attr "data-object-id" $ showObjectId $ Types.objectId obj
     ] <> E.styles
        [ Tuple "position" "absolute"
        , Tuple "left" (show bounds.x <> "px")
        , Tuple "top" (show bounds.y <> "px")
        , Tuple "width" (show bounds.width <> "px")
        , Tuple "height" (show bounds.height <> "px")
        ])
    []

-- | Render object with full compositing.
renderObjectWithCompositing :: RenderConfig -> Types.CanvasObject -> E.Element CanvasMsg
renderObjectWithCompositing _config obj =
  let 
    bounds = Types.objectBounds obj
    blendMode = Types.objectBlendMode obj
    opacity = Types.objectOpacity obj
    visible = Types.objectVisible obj
  in E.div_
    ([ E.class_ "canvas-object"
     , E.attr "data-object-id" $ showObjectId $ Types.objectId obj
     ] <> E.styles
        [ Tuple "position" "absolute"
        , Tuple "left" (show bounds.x <> "px")
        , Tuple "top" (show bounds.y <> "px")
        , Tuple "width" (show bounds.width <> "px")
        , Tuple "height" (show bounds.height <> "px")
        , Tuple "mix-blend-mode" (blendModeToCSS blendMode)
        , Tuple "opacity" (show opacity)
        , Tuple "visibility" (if visible then "visible" else "hidden")
        ])
    []
