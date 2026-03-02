-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                // hydrogen // element // compound // video-conference // controls
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Video Controls — Mute, camera, screen share, and call control buttons.

module Hydrogen.Element.Compound.VideoConference.Controls
  ( videoControls
  , VideoControlsConfig
  , controlButton
  ) where

import Prelude
  ( not
  , (<>)
  )

import Data.Maybe (Maybe(Nothing, Just))
import Hydrogen.Render.Element as E
import Hydrogen.Element.Compound.VideoConference.Icons 
  ( micOnIcon
  , micOffIcon
  , cameraOnIcon
  , cameraOffIcon
  , screenShareIcon
  , hangUpIcon
  , handIcon
  , chatIcon
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // video controls
-- ═════════════════════════════════════════════════════════════════════════════

-- | Video controls configuration
type VideoControlsConfig msg =
  { onMute :: msg
  , onCamera :: msg
  , onScreenShare :: msg
  , onHangUp :: msg
  , onRaiseHand :: Maybe msg
  , onChat :: Maybe msg
  , onMore :: Maybe msg
  , isMuted :: Boolean
  , isCameraOff :: Boolean
  , isScreenSharing :: Boolean
  , isHandRaised :: Boolean
  }

-- | Video controls bar
-- |
-- | Standard video call control bar with mute, camera, screen share, and hang up.
videoControls :: forall msg. VideoControlsConfig msg -> E.Element msg
videoControls config =
  E.div_
    [ E.style "display" "flex"
    , E.style "align-items" "center"
    , E.style "justify-content" "center"
    , E.style "gap" "12px"
    , E.style "padding" "16px 24px"
    , E.style "background-color" "#1a1a1a"
    , E.style "border-radius" "12px"
    ]
    [ -- Mute button
      controlButton
        { icon: if config.isMuted then micOffIcon else micOnIcon
        , label: if config.isMuted then "Unmute" else "Mute"
        , isActive: not config.isMuted
        , isDanger: false
        , onClick: config.onMute
        }
    
    -- Camera button
    , controlButton
        { icon: if config.isCameraOff then cameraOffIcon else cameraOnIcon
        , label: if config.isCameraOff then "Start Video" else "Stop Video"
        , isActive: not config.isCameraOff
        , isDanger: false
        , onClick: config.onCamera
        }
    
    -- Screen share button
    , controlButton
        { icon: screenShareIcon
        , label: if config.isScreenSharing then "Stop Sharing" else "Share Screen"
        , isActive: config.isScreenSharing
        , isDanger: false
        , onClick: config.onScreenShare
        }
    
    -- Hand raise (optional)
    , case config.onRaiseHand of
        Just handler -> controlButton
          { icon: handIcon
          , label: if config.isHandRaised then "Lower Hand" else "Raise Hand"
          , isActive: config.isHandRaised
          , isDanger: false
          , onClick: handler
          }
        Nothing -> E.text ""
    
    -- Chat (optional)
    , case config.onChat of
        Just handler -> controlButton
          { icon: chatIcon
          , label: "Chat"
          , isActive: false
          , isDanger: false
          , onClick: handler
          }
        Nothing -> E.text ""
    
    -- Hang up button
    , controlButton
        { icon: hangUpIcon
        , label: "Leave"
        , isActive: false
        , isDanger: true
        , onClick: config.onHangUp
        }
    ]

-- | Individual control button
controlButton :: forall msg.
  { icon :: E.Element msg
  , label :: String
  , isActive :: Boolean
  , isDanger :: Boolean
  , onClick :: msg
  } -> E.Element msg
controlButton config =
  let
    bgColor = 
      if config.isDanger then "#ef4444"
      else if config.isActive then "#3b82f6"
      else "#404040"
  in
    E.button_
      [ E.onClick config.onClick
      , E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "align-items" "center"
      , E.style "gap" "4px"
      , E.style "padding" "12px 16px"
      , E.style "background-color" bgColor
      , E.style "border" "none"
      , E.style "border-radius" "8px"
      , E.style "color" "white"
      , E.style "cursor" "pointer"
      , E.style "transition" "background-color 0.2s ease"
      , E.attr "title" config.label
      ]
      [ config.icon
      , E.span_
          [ E.style "font-size" "11px"
          , E.style "font-weight" "500"
          ]
          [ E.text config.label ]
      ]
