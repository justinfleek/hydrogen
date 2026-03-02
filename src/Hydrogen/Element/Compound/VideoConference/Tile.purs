-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                    // hydrogen // element // compound // video-conference // tile
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Video Tile — Individual participant video container.

module Hydrogen.Element.Compound.VideoConference.Tile
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
  ) where

import Prelude
  ( (<>)
  )

import Data.Array (foldl)
import Hydrogen.Render.Element as E
import Hydrogen.Element.Compound.VideoConference.Types (Participant, getInitials)
import Hydrogen.Element.Compound.VideoConference.Overlay (participantOverlay)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // video tile
-- ═════════════════════════════════════════════════════════════════════════════

-- | Video tile properties
type VideoTileProps =
  { isActive :: Boolean       -- Currently speaking
  , isMuted :: Boolean
  , isCameraOff :: Boolean
  , isScreenShare :: Boolean
  , isPinned :: Boolean
  , isSpotlight :: Boolean
  , className :: String
  }

-- | Property modifier
type VideoTileProp = VideoTileProps -> VideoTileProps

-- | Default tile properties
defaultTileProps :: VideoTileProps
defaultTileProps =
  { isActive: false
  , isMuted: false
  , isCameraOff: false
  , isScreenShare: false
  , isPinned: false
  , isSpotlight: false
  , className: ""
  }

-- | Set active (speaking) state
tileActive :: Boolean -> VideoTileProp
tileActive a props = props { isActive = a }

-- | Set muted state
tileMuted :: Boolean -> VideoTileProp
tileMuted m props = props { isMuted = m }

-- | Set camera off state
tileCameraOff :: Boolean -> VideoTileProp
tileCameraOff c props = props { isCameraOff = c }

-- | Set screen share state
tileScreenShare :: Boolean -> VideoTileProp
tileScreenShare s props = props { isScreenShare = s }

-- | Set pinned state
tilePinned :: Boolean -> VideoTileProp
tilePinned p props = props { isPinned = p }

-- | Set spotlight state
tileSpotlight :: Boolean -> VideoTileProp
tileSpotlight s props = props { isSpotlight = s }

-- | Video tile container
-- |
-- | Individual participant video with overlay for name, mute status, etc.
videoTile :: forall msg. Array VideoTileProp -> Participant -> E.Element msg
videoTile propMods participant =
  let
    props = foldl (\p f -> f p) defaultTileProps propMods
    
    -- Border color based on state
    borderColor = 
      if props.isActive then "#22c55e"  -- Green for speaking
      else if props.isPinned then "#3b82f6"  -- Blue for pinned
      else "transparent"
    
    tileStyles =
      [ E.style "position" "relative"
      , E.style "aspect-ratio" "16/9"
      , E.style "background-color" "#2d2d2d"
      , E.style "border-radius" "8px"
      , E.style "overflow" "hidden"
      , E.style "border" ("2px solid " <> borderColor)
      , E.style "transition" "border-color 0.2s ease"
      ]
    
    -- Video or avatar placeholder
    videoContent = 
      if props.isCameraOff
        then avatarPlaceholder participant
        else videoPlaceholder
    
    -- Overlay with name and status
    overlay = participantOverlay [] participant
  in
    E.div_ tileStyles
      [ videoContent
      , overlay
      , if props.isPinned then pinnedBadge else E.text ""
      ]

-- | Avatar placeholder when camera is off
avatarPlaceholder :: forall msg. Participant -> E.Element msg
avatarPlaceholder participant =
  E.div_
    [ E.style "display" "flex"
    , E.style "align-items" "center"
    , E.style "justify-content" "center"
    , E.style "width" "100%"
    , E.style "height" "100%"
    , E.style "background-color" "#3d3d3d"
    ]
    [ E.div_
        [ E.style "width" "80px"
        , E.style "height" "80px"
        , E.style "border-radius" "50%"
        , E.style "background-color" "#6366f1"
        , E.style "display" "flex"
        , E.style "align-items" "center"
        , E.style "justify-content" "center"
        , E.style "font-size" "32px"
        , E.style "font-weight" "600"
        , E.style "color" "white"
        ]
        [ E.text (getInitials participant.name) ]
    ]

-- | Video placeholder (simulates video element)
videoPlaceholder :: forall msg. E.Element msg
videoPlaceholder =
  E.div_
    [ E.style "width" "100%"
    , E.style "height" "100%"
    , E.style "background" "linear-gradient(135deg, #1e293b 0%, #0f172a 100%)"
    ]
    []

-- | Pinned badge
pinnedBadge :: forall msg. E.Element msg
pinnedBadge =
  E.div_
    [ E.style "position" "absolute"
    , E.style "top" "8px"
    , E.style "right" "8px"
    , E.style "background-color" "#3b82f6"
    , E.style "color" "white"
    , E.style "padding" "4px 8px"
    , E.style "border-radius" "4px"
    , E.style "font-size" "12px"
    , E.style "font-weight" "500"
    ]
    [ E.text "Pinned" ]
