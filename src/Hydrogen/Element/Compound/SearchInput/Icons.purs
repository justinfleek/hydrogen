-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // element // search-input // icons
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | SearchInput Icons — SVG icons for the search input component.
-- |
-- | Pure Element representations of Feather-style icons.
-- | Each icon accepts a size string and renders as an SVG element.

module Hydrogen.Element.Compound.SearchInput.Icons
  ( -- * Icons
    searchIcon
  , clearIcon
  , arrowRightIcon
  , spinnerIcon
  ) where

import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // icons
-- ═════════════════════════════════════════════════════════════════════════════

-- | Search (magnifying glass) icon
searchIcon :: forall msg. String -> E.Element msg
searchIcon size =
  E.svg_
    [ E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    , E.attr "stroke-linecap" "round"
    , E.attr "stroke-linejoin" "round"
    , E.style "width" size
    , E.style "height" size
    ]
    [ E.circle_
        [ E.attr "cx" "11"
        , E.attr "cy" "11"
        , E.attr "r" "8"
        ]
    , E.line_
        [ E.attr "x1" "21"
        , E.attr "y1" "21"
        , E.attr "x2" "16.65"
        , E.attr "y2" "16.65"
        ]
    ]

-- | Clear (X) icon
clearIcon :: forall msg. String -> E.Element msg
clearIcon size =
  E.svg_
    [ E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    , E.attr "stroke-linecap" "round"
    , E.attr "stroke-linejoin" "round"
    , E.style "width" size
    , E.style "height" size
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

-- | Arrow right icon
arrowRightIcon :: forall msg. String -> E.Element msg
arrowRightIcon size =
  E.svg_
    [ E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    , E.attr "stroke-linecap" "round"
    , E.attr "stroke-linejoin" "round"
    , E.style "width" size
    , E.style "height" size
    ]
    [ E.line_
        [ E.attr "x1" "5"
        , E.attr "y1" "12"
        , E.attr "x2" "19"
        , E.attr "y2" "12"
        ]
    , E.polyline_
        [ E.attr "points" "12 5 19 12 12 19" ]
    ]

-- | Loading spinner icon
spinnerIcon :: forall msg. String -> E.Element msg
spinnerIcon size =
  E.svg_
    [ E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "fill" "none"
    , E.attr "viewBox" "0 0 24 24"
    , E.style "width" size
    , E.style "height" size
    , E.style "animation" "spin 1s linear infinite"
    ]
    [ E.circle_
        [ E.attr "cx" "12"
        , E.attr "cy" "12"
        , E.attr "r" "10"
        , E.attr "stroke" "currentColor"
        , E.attr "stroke-width" "4"
        , E.style "opacity" "0.25"
        ]
    , E.path_
        [ E.attr "fill" "currentColor"
        , E.attr "d" "M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4zm2 5.291A7.962 7.962 0 014 12H0c0 3.042 1.135 5.824 3 7.938l3-2.647z"
        , E.style "opacity" "0.75"
        ]
    ]
