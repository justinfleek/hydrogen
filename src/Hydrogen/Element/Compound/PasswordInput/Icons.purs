-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // element // password-input //
--                                                                        icons
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | SVG icons for password visibility toggle.
-- |
-- | Eye icon: password hidden (click to show)
-- | Eye-off icon: password visible (click to hide)

module Hydrogen.Element.Compound.PasswordInput.Icons
  ( eyeIcon
  , eyeOffIcon
  ) where

import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // icons
-- ═════════════════════════════════════════════════════════════════════════════

-- | Eye icon (password hidden - click to show)
eyeIcon :: forall msg. String -> E.Element msg
eyeIcon size =
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
    [ E.path_
        [ E.attr "d" "M1 12s4-8 11-8 11 8 11 8-4 8-11 8-11-8-11-8z" ]
    , E.circle_
        [ E.attr "cx" "12"
        , E.attr "cy" "12"
        , E.attr "r" "3"
        ]
    ]

-- | Eye-off icon (password visible - click to hide)
eyeOffIcon :: forall msg. String -> E.Element msg
eyeOffIcon size =
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
    [ E.path_
        [ E.attr "d" "M17.94 17.94A10.07 10.07 0 0 1 12 20c-7 0-11-8-11-8a18.45 18.45 0 0 1 5.06-5.94M9.9 4.24A9.12 9.12 0 0 1 12 4c7 0 11 8 11 8a18.5 18.5 0 0 1-2.16 3.19m-6.72-1.07a3 3 0 1 1-4.24-4.24" ]
    , E.line_
        [ E.attr "x1" "1"
        , E.attr "y1" "1"
        , E.attr "x2" "23"
        , E.attr "y2" "23"
        ]
    ]
