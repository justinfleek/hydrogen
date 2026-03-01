-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--              // hydrogen // element // compound // canvas // render // guides
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas Render Guides — Guide line rendering.
-- |
-- | ## Purpose
-- |
-- | Renders alignment guides for canvas:
-- | - Horizontal guides
-- | - Vertical guides
-- |
-- | Guides extend across the full canvas dimension.
-- |
-- | ## Dependencies
-- |
-- | - Canvas.Types (Guide, GuideOrientation)
-- | - Render.Types (RenderConfig, CanvasMsg)

module Hydrogen.Element.Compound.Canvas.Render.Guides
  ( -- * Guide Rendering
    renderGuide
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , (==)
  , (<>)
  )

import Data.Tuple (Tuple(Tuple))

import Hydrogen.Render.Element as E
import Hydrogen.Element.Compound.Canvas.Types as Types
import Hydrogen.Element.Compound.Canvas.Render.Types (CanvasMsg, RenderConfig)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // guide rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a single guide.
renderGuide :: RenderConfig -> Types.Guide -> E.Element CanvasMsg
renderGuide config guide =
  let 
    pos = Types.guidePosition guide
    isHorizontal = case guide of
      Types.Guide g -> g.orientation == Types.GuideHorizontal
    guideStyles = if isHorizontal
      then
        [ Tuple "position" "absolute"
        , Tuple "left" "0"
        , Tuple "top" (show pos <> "px")
        , Tuple "width" "100%"
        , Tuple "height" "1px"
        , Tuple "background-color" config.guideColor
        ]
      else
        [ Tuple "position" "absolute"
        , Tuple "left" (show pos <> "px")
        , Tuple "top" "0"
        , Tuple "width" "1px"
        , Tuple "height" "100%"
        , Tuple "background-color" config.guideColor
        ]
  in E.div_
    ([ E.class_ (if isHorizontal then "guide guide-horizontal" else "guide guide-vertical") ] <> E.styles guideStyles)
    []
