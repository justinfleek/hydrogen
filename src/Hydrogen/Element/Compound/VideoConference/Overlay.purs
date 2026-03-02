-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                 // hydrogen // element // compound // video-conference // overlay
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Participant Overlay — Name badge, mute status, and indicators.

module Hydrogen.Element.Compound.VideoConference.Overlay
  ( participantOverlay
  , ParticipantOverlayProps
  , ParticipantOverlayProp
  , defaultOverlayProps
  , overlayPosition
  ) where

import Prelude
  ( (<>)
  )

import Data.Array (foldl)
import Hydrogen.Render.Element as E
import Hydrogen.Element.Compound.VideoConference.Types 
  ( Participant
  , OverlayPosition(BottomLeft, BottomRight, TopLeft, TopRight)
  )
import Hydrogen.Element.Compound.VideoConference.Icons (muteIcon, handRaisedIcon)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // participant overlay
-- ═════════════════════════════════════════════════════════════════════════════

-- | Overlay properties
type ParticipantOverlayProps =
  { position :: OverlayPosition
  , showName :: Boolean
  , showMuteStatus :: Boolean
  , className :: String
  }

-- | Property modifier
type ParticipantOverlayProp = ParticipantOverlayProps -> ParticipantOverlayProps

-- | Default overlay properties
defaultOverlayProps :: ParticipantOverlayProps
defaultOverlayProps =
  { position: BottomLeft
  , showName: true
  , showMuteStatus: true
  , className: ""
  }

-- | Set overlay position
overlayPosition :: OverlayPosition -> ParticipantOverlayProp
overlayPosition pos props = props { position = pos }

-- | Participant overlay
-- |
-- | Shows participant name, mute status, and speaking indicator.
participantOverlay :: forall msg. Array ParticipantOverlayProp -> Participant -> E.Element msg
participantOverlay propMods participant =
  let
    props = foldl (\p f -> f p) defaultOverlayProps propMods
    
    posStyles = case props.position of
      BottomLeft -> [ E.style "bottom" "8px", E.style "left" "8px" ]
      BottomRight -> [ E.style "bottom" "8px", E.style "right" "8px" ]
      TopLeft -> [ E.style "top" "8px", E.style "left" "8px" ]
      TopRight -> [ E.style "top" "8px", E.style "right" "8px" ]
    
    baseStyles =
      [ E.style "position" "absolute"
      , E.style "display" "flex"
      , E.style "align-items" "center"
      , E.style "gap" "6px"
      , E.style "padding" "4px 8px"
      , E.style "background-color" "rgba(0, 0, 0, 0.6)"
      , E.style "border-radius" "4px"
      , E.style "color" "white"
      , E.style "font-size" "13px"
      ]
  in
    E.div_ (baseStyles <> posStyles)
      [ if participant.isMuted then muteIcon else E.text ""
      , if props.showName then E.text participant.name else E.text ""
      , if participant.isHost then hostBadge else E.text ""
      , if participant.isHandRaised then handRaisedIcon else E.text ""
      ]

-- | Host badge
hostBadge :: forall msg. E.Element msg
hostBadge =
  E.span_
    [ E.style "background-color" "#6366f1"
    , E.style "padding" "2px 6px"
    , E.style "border-radius" "3px"
    , E.style "font-size" "10px"
    , E.style "font-weight" "500"
    ]
    [ E.text "Host" ]
