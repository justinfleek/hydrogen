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
  )

import Hydrogen.Render.Element as E
import Hydrogen.Element.Compound.Canvas.Types as Types
import Hydrogen.Element.Compound.Canvas.Render.Types (CanvasMsg, RenderConfig)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // guide rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a single guide.
-- |
-- | Guide positioning data is stored in the element's data attributes.
-- | The runtime interprets these Schema atoms to render the guide.
renderGuide :: RenderConfig -> Types.Guide -> E.Element CanvasMsg
renderGuide config guide =
  let 
    isHorizontal = case guide of
      Types.Guide g -> g.orientation == Types.GuideHorizontal
  in E.div_
    [ E.class_ (if isHorizontal then "guide guide-horizontal" else "guide guide-vertical")
    , E.dataAttr "guide-position" (show (Types.guidePosition guide))
    , E.dataAttr "guide-orientation" (if isHorizontal then "horizontal" else "vertical")
    , E.dataAttr "guide-color" config.guideColor
    ]
    []
