-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                    // hydrogen // element // compound // video-conference // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Video Conference Types — Shared types for video conferencing components.

module Hydrogen.Element.Compound.VideoConference.Types
  ( -- * Participant
    Participant
  , defaultParticipant
  
  -- * Connection Quality
  , ConnectionQuality(Excellent, Good, Fair, Poor, Disconnected)
  
  -- * Control Button
  , ControlButton(ControlMute, ControlCamera, ControlScreenShare, ControlHangUp, ControlRaiseHand, ControlChat, ControlMore)
  
  -- * Overlay Position
  , OverlayPosition(BottomLeft, BottomRight, TopLeft, TopRight)
  
  -- * PiP Position
  , PipPosition(PipTopLeft, PipTopRight, PipBottomLeft, PipBottomRight)
  
  -- * Utilities
  , getInitials
  ) where

import Prelude
  ( class Eq
  , class Ord
  )

import Data.Maybe (Maybe(Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // participant
-- ═════════════════════════════════════════════════════════════════════════════

-- | Participant data for video tiles
type Participant =
  { id :: String
  , name :: String
  , avatarUrl :: Maybe String
  , isMuted :: Boolean
  , isCameraOff :: Boolean
  , isSpeaking :: Boolean
  , isHandRaised :: Boolean
  , isHost :: Boolean
  , isScreenSharing :: Boolean
  }

-- | Default participant
defaultParticipant :: Participant
defaultParticipant =
  { id: ""
  , name: "Unknown"
  , avatarUrl: Nothing
  , isMuted: false
  , isCameraOff: false
  , isSpeaking: false
  , isHandRaised: false
  , isHost: false
  , isScreenSharing: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // connection quality
-- ═════════════════════════════════════════════════════════════════════════════

-- | Connection quality levels
data ConnectionQuality
  = Excellent
  | Good
  | Fair
  | Poor
  | Disconnected

derive instance eqConnectionQuality :: Eq ConnectionQuality
derive instance ordConnectionQuality :: Ord ConnectionQuality

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // control buttons
-- ═════════════════════════════════════════════════════════════════════════════

-- | Control button types
data ControlButton
  = ControlMute
  | ControlCamera
  | ControlScreenShare
  | ControlHangUp
  | ControlRaiseHand
  | ControlChat
  | ControlMore

derive instance eqControlButton :: Eq ControlButton

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // overlay position
-- ═════════════════════════════════════════════════════════════════════════════

-- | Overlay position
data OverlayPosition
  = BottomLeft
  | BottomRight
  | TopLeft
  | TopRight

derive instance eqOverlayPosition :: Eq OverlayPosition
derive instance ordOverlayPosition :: Ord OverlayPosition

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // pip position
-- ═════════════════════════════════════════════════════════════════════════════

-- | PiP position
data PipPosition
  = PipTopLeft
  | PipTopRight
  | PipBottomLeft
  | PipBottomRight

derive instance eqPipPosition :: Eq PipPosition
derive instance ordPipPosition :: Ord PipPosition

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get initials from name
getInitials :: String -> String
getInitials name = case name of
  "" -> "?"
  _ -> name  -- Simplified - would use String.take 2 in full implementation
