-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                // hydrogen // element // compound // canvas // render // grid
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas Render Grid — Grid visualization rendering.
-- |
-- | ## Purpose
-- |
-- | Renders grid overlays for canvas alignment:
-- | - Line grid (horizontal and vertical lines)
-- | - Dot grid (dot pattern)
-- |
-- | Uses SVG patterns for efficient rendering at any scale.
-- |
-- | ## Dependencies
-- |
-- | - Canvas.Types (GridConfig)
-- | - Canvas.State (CanvasState)
-- | - Render.Types (CanvasMsg)

module Hydrogen.Element.Compound.Canvas.Render.Grid
  ( -- * Grid Rendering
    renderGridLines
  , renderGridDots
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
import Hydrogen.Element.Compound.Canvas.Types as Types
import Hydrogen.Element.Compound.Canvas.State as State
import Hydrogen.Element.Compound.Canvas.Render.Types (CanvasMsg)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // grid rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render grid as lines.
renderGridLines :: Types.GridConfig -> State.CanvasState -> E.Element CanvasMsg
renderGridLines gridConfig _state =
  E.svg_
    ([ E.class_ "canvas-grid-lines" ] <> E.styles
        [ Tuple "width" "100%"
        , Tuple "height" "100%"
        ])
    [ E.defs_
        []
        [ E.svgElement "pattern"
            [ E.attr "id" "grid-pattern"
            , E.attr "width" (show gridConfig.size)
            , E.attr "height" (show gridConfig.size)
            , E.attr "patternUnits" "userSpaceOnUse"
            ]
            [ E.line_
                [ E.attr "x1" "0"
                , E.attr "y1" "0"
                , E.attr "x2" (show gridConfig.size)
                , E.attr "y2" "0"
                , E.attr "stroke" gridConfig.minorColor
                , E.attr "stroke-width" (show gridConfig.minorWidth)
                ]
            , E.line_
                [ E.attr "x1" "0"
                , E.attr "y1" "0"
                , E.attr "x2" "0"
                , E.attr "y2" (show gridConfig.size)
                , E.attr "stroke" gridConfig.minorColor
                , E.attr "stroke-width" (show gridConfig.minorWidth)
                ]
            ]
        ]
    , E.rect_
        [ E.attr "width" "100%"
        , E.attr "height" "100%"
        , E.attr "fill" "url(#grid-pattern)"
        ]
    ]

-- | Render grid as dots.
renderGridDots :: Types.GridConfig -> State.CanvasState -> E.Element CanvasMsg
renderGridDots gridConfig _state =
  E.svg_
    ([ E.class_ "canvas-grid-dots" ] <> E.styles
        [ Tuple "width" "100%"
        , Tuple "height" "100%"
        ])
    [ E.defs_
        []
        [ E.svgElement "pattern"
            [ E.attr "id" "dot-pattern"
            , E.attr "width" (show gridConfig.size)
            , E.attr "height" (show gridConfig.size)
            , E.attr "patternUnits" "userSpaceOnUse"
            ]
            [ E.circle_
                [ E.attr "cx" "0"
                , E.attr "cy" "0"
                , E.attr "r" "1"
                , E.attr "fill" gridConfig.minorColor
                ]
            ]
        ]
    , E.rect_
        [ E.attr "width" "100%"
        , E.attr "height" "100%"
        , E.attr "fill" "url(#dot-pattern)"
        ]
    ]
