-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                    // hydrogen // element // compound // video-conference // icons
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Video Conference Icons — SVG icons for video conferencing UI.

module Hydrogen.Element.Compound.VideoConference.Icons
  ( micOnIcon
  , micOffIcon
  , cameraOnIcon
  , cameraOffIcon
  , screenShareIcon
  , hangUpIcon
  , handIcon
  , chatIcon
  , muteIcon
  , handRaisedIcon
  ) where

import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // icons
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mute icon (microphone on)
micOnIcon :: forall msg. E.Element msg
micOnIcon =
  E.svg_
    [ E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    , E.style "width" "20px"
    , E.style "height" "20px"
    ]
    [ E.path_
        [ E.attr "d" "M12 1a3 3 0 0 0-3 3v8a3 3 0 0 0 6 0V4a3 3 0 0 0-3-3z" ]
    , E.path_
        [ E.attr "d" "M19 10v2a7 7 0 0 1-14 0v-2" ]
    , E.path_
        [ E.attr "d" "M12 19v4" ]
    , E.path_
        [ E.attr "d" "M8 23h8" ]
    ]

-- | Mute off icon (microphone muted)
micOffIcon :: forall msg. E.Element msg
micOffIcon =
  E.svg_
    [ E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    , E.style "width" "20px"
    , E.style "height" "20px"
    ]
    [ E.path_
        [ E.attr "d" "M1 1l22 22" ]
    , E.path_
        [ E.attr "d" "M9 9v3a3 3 0 0 0 5.12 2.12M15 9.34V4a3 3 0 0 0-5.94-.6" ]
    , E.path_
        [ E.attr "d" "M17 16.95A7 7 0 0 1 5 12v-2m14 0v2a7 7 0 0 1-.11 1.23" ]
    , E.path_
        [ E.attr "d" "M12 19v4" ]
    , E.path_
        [ E.attr "d" "M8 23h8" ]
    ]

-- | Camera on icon
cameraOnIcon :: forall msg. E.Element msg
cameraOnIcon =
  E.svg_
    [ E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    , E.style "width" "20px"
    , E.style "height" "20px"
    ]
    [ E.path_
        [ E.attr "d" "M23 7l-7 5 7 5V7z" ]
    , E.rect_
        [ E.attr "x" "1"
        , E.attr "y" "5"
        , E.attr "width" "15"
        , E.attr "height" "14"
        , E.attr "rx" "2"
        , E.attr "ry" "2"
        ]
    ]

-- | Camera off icon
cameraOffIcon :: forall msg. E.Element msg
cameraOffIcon =
  E.svg_
    [ E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    , E.style "width" "20px"
    , E.style "height" "20px"
    ]
    [ E.path_
        [ E.attr "d" "M1 1l22 22" ]
    , E.path_
        [ E.attr "d" "M21 21H3a2 2 0 0 1-2-2V8a2 2 0 0 1 2-2h3m3-3h6l2 3h4a2 2 0 0 1 2 2v9.34m-7.72-2.06a4 4 0 1 1-5.56-5.56" ]
    ]

-- | Screen share icon
screenShareIcon :: forall msg. E.Element msg
screenShareIcon =
  E.svg_
    [ E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    , E.style "width" "20px"
    , E.style "height" "20px"
    ]
    [ E.rect_
        [ E.attr "x" "2"
        , E.attr "y" "3"
        , E.attr "width" "20"
        , E.attr "height" "14"
        , E.attr "rx" "2"
        , E.attr "ry" "2"
        ]
    , E.path_
        [ E.attr "d" "M8 21h8" ]
    , E.path_
        [ E.attr "d" "M12 17v4" ]
    ]

-- | Hang up icon
hangUpIcon :: forall msg. E.Element msg
hangUpIcon =
  E.svg_
    [ E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    , E.style "width" "20px"
    , E.style "height" "20px"
    ]
    [ E.path_
        [ E.attr "d" "M22 16.92v3a2 2 0 0 1-2.18 2 19.79 19.79 0 0 1-8.63-3.07 19.5 19.5 0 0 1-6-6 19.79 19.79 0 0 1-3.07-8.67A2 2 0 0 1 4.11 2h3a2 2 0 0 1 2 1.72 12.84 12.84 0 0 0 .7 2.81 2 2 0 0 1-.45 2.11L8.09 9.91a16 16 0 0 0 6 6l1.27-1.27a2 2 0 0 1 2.11-.45 12.84 12.84 0 0 0 2.81.7A2 2 0 0 1 22 16.92z" ]
    , E.path_
        [ E.attr "d" "M14.05 2a9 9 0 0 1 8 7.94" ]
    , E.path_
        [ E.attr "d" "M14.05 6A5 5 0 0 1 18 10" ]
    ]

-- | Hand icon
handIcon :: forall msg. E.Element msg
handIcon =
  E.svg_
    [ E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    , E.style "width" "20px"
    , E.style "height" "20px"
    ]
    [ E.path_
        [ E.attr "d" "M18 11V6a2 2 0 0 0-2-2v0a2 2 0 0 0-2 2v0" ]
    , E.path_
        [ E.attr "d" "M14 10V4a2 2 0 0 0-2-2v0a2 2 0 0 0-2 2v2" ]
    , E.path_
        [ E.attr "d" "M10 10.5V6a2 2 0 0 0-2-2v0a2 2 0 0 0-2 2v8" ]
    , E.path_
        [ E.attr "d" "M18 8a2 2 0 1 1 4 0v6a8 8 0 0 1-8 8h-2c-2.8 0-4.5-.86-5.99-2.34l-3.6-3.6a2 2 0 0 1 2.83-2.82L7 15" ]
    ]

-- | Chat icon
chatIcon :: forall msg. E.Element msg
chatIcon =
  E.svg_
    [ E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    , E.style "width" "20px"
    , E.style "height" "20px"
    ]
    [ E.path_
        [ E.attr "d" "M21 15a2 2 0 0 1-2 2H7l-4 4V5a2 2 0 0 1 2-2h14a2 2 0 0 1 2 2z" ]
    ]

-- | Mute icon (small)
muteIcon :: forall msg. E.Element msg
muteIcon =
  E.svg_
    [ E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "currentColor"
    , E.style "width" "14px"
    , E.style "height" "14px"
    , E.style "color" "#ef4444"
    ]
    [ E.path_
        [ E.attr "d" "M1 1l22 22M9 9v3a3 3 0 0 0 5.12 2.12" ]
    ]

-- | Hand raised icon (small)
handRaisedIcon :: forall msg. E.Element msg
handRaisedIcon =
  E.span_
    [ E.style "font-size" "14px" ]
    [ E.text "✋" ]
