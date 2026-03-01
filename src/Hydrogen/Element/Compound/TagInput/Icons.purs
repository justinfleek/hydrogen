-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // element // tag-input // icons
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TagInput Icons — SVG icons used by TagInput component.

module Hydrogen.Element.Compound.TagInput.Icons
  ( removeIcon
  ) where

import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // icons
-- ═════════════════════════════════════════════════════════════════════════════

-- | Small X icon for remove button
removeIcon :: forall msg. E.Element msg
removeIcon =
  E.svg_
    [ E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    , E.attr "stroke-linecap" "round"
    , E.attr "stroke-linejoin" "round"
    , E.style "width" "12px"
    , E.style "height" "12px"
    ]
    [ E.line_
        [ E.attr "x1" "18"
        , E.attr "y1" "6"
        , E.attr "x2" "6"
        , E.attr "y2" "18"
        ]
    , E.line_
        [ E.attr "x1" "6"
        , E.attr "y1" "6"
        , E.attr "x2" "18"
        , E.attr "y2" "18"
        ]
    ]
