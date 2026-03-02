-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // element // compound // video-conference
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Video Conference Components — Video calling UI primitives.
-- |
-- | ## Components
-- |
-- | - **VideoGrid**: Responsive grid of participant videos
-- | - **VideoTile**: Individual participant video container
-- | - **VideoControls**: Mute/unmute, camera, screen share, hang up
-- | - **ParticipantOverlay**: Name badge, speaking indicator, mute status
-- | - **PictureInPicture**: Floating self-view
-- | - **ScreenShare**: Screen sharing display with presenter info
-- | - **CallTimer**: Call duration display
-- | - **ConnectionIndicator**: Network quality indicator
-- | - **HandRaise**: Hand raise button and indicator
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.VideoConference as VC
-- |
-- | -- Video grid with participants
-- | VC.videoGrid [ VC.gridColumns 3 ]
-- |   [ VC.videoTile [ VC.tileActive true ] participant1
-- |   , VC.videoTile [] participant2
-- |   , VC.videoTile [ VC.tileMuted true ] participant3
-- |   ]
-- |
-- | -- Controls bar
-- | VC.videoControls
-- |   { onMute: ToggleMute
-- |   , onCamera: ToggleCamera
-- |   , onScreenShare: ToggleScreenShare
-- |   , onHangUp: HangUp
-- |   , isMuted: state.muted
-- |   , isCameraOff: state.cameraOff
-- |   , isScreenSharing: state.screenSharing
-- |   }
-- | ```

module Hydrogen.Element.Compound.VideoConference
  ( -- * Re-exports
    module Hydrogen.Element.Compound.VideoConference.Types
  , module Hydrogen.Element.Compound.VideoConference.Grid
  , module Hydrogen.Element.Compound.VideoConference.Tile
  , module Hydrogen.Element.Compound.VideoConference.Overlay
  , module Hydrogen.Element.Compound.VideoConference.Controls
  , module Hydrogen.Element.Compound.VideoConference.Pip
  , module Hydrogen.Element.Compound.VideoConference.Indicators
  ) where

import Hydrogen.Element.Compound.VideoConference.Types
  ( Participant
  , defaultParticipant
  , ConnectionQuality(Excellent, Good, Fair, Poor, Disconnected)
  , ControlButton(ControlMute, ControlCamera, ControlScreenShare, ControlHangUp, ControlRaiseHand, ControlChat, ControlMore)
  , OverlayPosition(BottomLeft, BottomRight, TopLeft, TopRight)
  , PipPosition(PipTopLeft, PipTopRight, PipBottomLeft, PipBottomRight)
  , getInitials
  )

import Hydrogen.Element.Compound.VideoConference.Grid
  ( videoGrid
  , VideoGridProps
  , VideoGridProp
  , defaultGridProps
  , gridColumns
  , gridGap
  , gridAspectRatio
  )

import Hydrogen.Element.Compound.VideoConference.Tile
  ( videoTile
  , VideoTileProps
  , VideoTileProp
  , defaultTileProps
  , tileActive
  , tileMuted
  , tileCameraOff
  , tileScreenShare
  , tilePinned
  , tileSpotlight
  )

import Hydrogen.Element.Compound.VideoConference.Overlay
  ( participantOverlay
  , ParticipantOverlayProps
  , ParticipantOverlayProp
  , defaultOverlayProps
  , overlayPosition
  )

import Hydrogen.Element.Compound.VideoConference.Controls
  ( videoControls
  , VideoControlsConfig
  , controlButton
  )

import Hydrogen.Element.Compound.VideoConference.Pip
  ( pictureInPicture
  , PipProps
  , PipProp
  , defaultPipProps
  , pipPosition
  , pipSize
  )

import Hydrogen.Element.Compound.VideoConference.Indicators
  ( screenShareView
  , ScreenShareProps
  , ScreenShareProp
  , defaultScreenShareProps
  , sharePresenterName
  , callTimer
  , CallTimerProps
  , connectionIndicator
  , handRaiseButton
  , handRaiseIndicator
  )
