-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--             // hydrogen // element // compound // video-conference // indicators
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Video Conference Indicators — Call timer, connection quality, hand raise.

module Hydrogen.Element.Compound.VideoConference.Indicators
  ( -- * Screen Share
    screenShareView
  , ScreenShareProps
  , ScreenShareProp
  , defaultScreenShareProps
  , sharePresenterName
  
  -- * Call Timer
  , callTimer
  , CallTimerProps
  
  -- * Connection Indicator
  , connectionIndicator
  
  -- * Hand Raise
  , handRaiseButton
  , handRaiseIndicator
  ) where

import Prelude
  ( show
  , (<>)
  , (<)
  )

import Data.Array (foldl)
import Hydrogen.Render.Element as E
import Hydrogen.Element.Compound.VideoConference.Types (ConnectionQuality(Excellent, Good, Fair, Poor, Disconnected))
import Hydrogen.Element.Compound.VideoConference.Icons (screenShareIcon, handIcon)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // screen share
-- ═════════════════════════════════════════════════════════════════════════════

-- | Screen share properties
type ScreenShareProps =
  { presenterName :: String
  , className :: String
  }

-- | Property modifier
type ScreenShareProp = ScreenShareProps -> ScreenShareProps

-- | Default screen share properties
defaultScreenShareProps :: ScreenShareProps
defaultScreenShareProps =
  { presenterName: ""
  , className: ""
  }

-- | Set presenter name
sharePresenterName :: String -> ScreenShareProp
sharePresenterName name props = props { presenterName = name }

-- | Screen share view
-- |
-- | Full-screen display for shared screen with presenter info.
screenShareView :: forall msg. Array ScreenShareProp -> E.Element msg -> E.Element msg
screenShareView propMods content =
  let
    props = foldl (\p f -> f p) defaultScreenShareProps propMods
  in
    E.div_
      [ E.style "position" "relative"
      , E.style "width" "100%"
      , E.style "height" "100%"
      , E.style "background-color" "#000"
      ]
      [ content
      , E.div_
          [ E.style "position" "absolute"
          , E.style "top" "16px"
          , E.style "left" "16px"
          , E.style "display" "flex"
          , E.style "align-items" "center"
          , E.style "gap" "8px"
          , E.style "padding" "8px 12px"
          , E.style "background-color" "rgba(0, 0, 0, 0.7)"
          , E.style "border-radius" "6px"
          , E.style "color" "white"
          ]
          [ screenShareIcon
          , E.span_ [] [ E.text (props.presenterName <> " is presenting") ]
          ]
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // call timer
-- ═════════════════════════════════════════════════════════════════════════════

-- | Call timer properties
type CallTimerProps =
  { hours :: Int
  , minutes :: Int
  , seconds :: Int
  }

-- | Call timer display
-- |
-- | Shows elapsed call duration.
callTimer :: forall msg. CallTimerProps -> E.Element msg
callTimer props =
  let
    pad n = if n < 10 then "0" <> show n else show n
    
    timeStr = 
      if props.hours > 0
        then pad props.hours <> ":" <> pad props.minutes <> ":" <> pad props.seconds
        else pad props.minutes <> ":" <> pad props.seconds
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "align-items" "center"
      , E.style "gap" "6px"
      , E.style "padding" "6px 12px"
      , E.style "background-color" "rgba(0, 0, 0, 0.5)"
      , E.style "border-radius" "4px"
      , E.style "color" "white"
      , E.style "font-size" "14px"
      , E.style "font-variant-numeric" "tabular-nums"
      ]
      [ recordingDot
      , E.text timeStr
      ]

-- | Recording dot indicator
recordingDot :: forall msg. E.Element msg
recordingDot =
  E.span_
    [ E.style "width" "8px"
    , E.style "height" "8px"
    , E.style "border-radius" "50%"
    , E.style "background-color" "#ef4444"
    ]
    []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // connection indicator
-- ═════════════════════════════════════════════════════════════════════════════

-- | Connection indicator
-- |
-- | Shows network quality as colored bars.
connectionIndicator :: forall msg. ConnectionQuality -> E.Element msg
connectionIndicator quality =
  let
    barColor level = case quality of
      Excellent -> if level < 5 then "#22c55e" else "#404040"
      Good -> if level < 4 then "#22c55e" else "#404040"
      Fair -> if level < 3 then "#eab308" else "#404040"
      Poor -> if level < 2 then "#ef4444" else "#404040"
      Disconnected -> "#404040"
    
    bar level height =
      E.div_
        [ E.style "width" "4px"
        , E.style "height" (show height <> "px")
        , E.style "background-color" (barColor level)
        , E.style "border-radius" "1px"
        ]
        []
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "align-items" "flex-end"
      , E.style "gap" "2px"
      , E.style "padding" "4px"
      ]
      [ bar 1 6
      , bar 2 10
      , bar 3 14
      , bar 4 18
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // hand raise
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hand raise button
-- |
-- | Button to raise/lower hand during a call.
handRaiseButton :: forall msg. { onClick :: msg, isRaised :: Boolean } -> E.Element msg
handRaiseButton config =
  E.button_
    [ E.onClick config.onClick
    , E.style "display" "flex"
    , E.style "align-items" "center"
    , E.style "gap" "6px"
    , E.style "padding" "8px 16px"
    , E.style "background-color" (if config.isRaised then "#eab308" else "#404040")
    , E.style "border" "none"
    , E.style "border-radius" "6px"
    , E.style "color" (if config.isRaised then "#1a1a1a" else "white")
    , E.style "font-size" "14px"
    , E.style "cursor" "pointer"
    ]
    [ handIcon
    , E.text (if config.isRaised then "Lower Hand" else "Raise Hand")
    ]

-- | Hand raised indicator
-- |
-- | Shows when a participant has their hand raised.
handRaiseIndicator :: forall msg. String -> E.Element msg
handRaiseIndicator participantName =
  E.div_
    [ E.style "display" "flex"
    , E.style "align-items" "center"
    , E.style "gap" "8px"
    , E.style "padding" "8px 12px"
    , E.style "background-color" "#fef3c7"
    , E.style "border-radius" "6px"
    , E.style "color" "#92400e"
    , E.style "font-size" "14px"
    ]
    [ handIcon
    , E.text (participantName <> " raised their hand")
    ]
