-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                      // hydrogen // component // motion // timeline // playhead
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Playhead indicator for Animation Timeline
-- |
-- | A vertical line indicating the current frame position in the timeline,
-- | with a draggable head for seeking.
-- |
-- | ## Features
-- |
-- | - Vertical line spanning timeline height
-- | - Draggable head at top
-- | - Frame/timecode display in head
-- | - Keyboard nudge support (left/right arrows)
-- | - Snap to frame boundaries
-- |
-- | ## Visual Structure
-- |
-- | ```
-- |    ┌──────┐  <- Draggable head with frame display
-- |    │ 0:30 │
-- |    └──┬───┘
-- |       │     <- Vertical line
-- |       │
-- |       │
-- |       ▼
-- | ```
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Motion.Timeline.Playhead as Playhead
-- |
-- | HH.slot _playhead unit Playhead.component
-- |   { currentFrame: Frames 100.0
-- |   , frameRate: fps24
-- |   , displayMode: TimeRuler.TimecodeMode
-- |   , height: 400.0
-- |   , pixelsPerFrame: 10.0
-- |   , scrollOffset: 0.0
-- |   }
-- |   HandlePlayheadOutput
-- | ```
module Hydrogen.Component.Motion.Timeline.Playhead
  ( -- * Component
    component
  
  -- * Types
  , Query(..)
  , Input
  , Output(..)
  , Slot
  
  -- * Slot Type
  , _playhead
  ) where

import Prelude

import Data.Int (round)
import Data.Maybe (Maybe(Just))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.Component.Motion.Timeline.TimeRuler (TimeDisplayMode(FramesMode, TimecodeMode, SecondsMode))
import Hydrogen.Schema.Dimension.Temporal (FrameRate, Frames(Frames))
import Hydrogen.Schema.Dimension.Temporal (unwrapFrames, unwrapFps) as Temporal
import Hydrogen.Schema.Motion.Timecode as TC
import Hydrogen.UI.Core (cls)
import Type.Proxy (Proxy(Proxy))
import Web.UIEvent.KeyboardEvent (KeyboardEvent)
import Web.UIEvent.KeyboardEvent (key) as KeyboardEvent
import Web.UIEvent.MouseEvent (MouseEvent)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Component input
type Input =
  { currentFrame :: Frames
  , frameRate :: FrameRate
  , displayMode :: TimeDisplayMode
  , height :: Number
  , pixelsPerFrame :: Number
  , scrollOffset :: Number
  }

-- | Component queries
data Query a
  = SetCurrentFrame Frames a
  | NudgeFrame Int a  -- Positive for forward, negative for backward

-- | Component output
data Output
  = DragStart
  | Dragging Frames
  | DragEnd
  | NudgeRequested Int  -- Request to nudge N frames

-- | Internal state
type State =
  { currentFrame :: Frames
  , frameRate :: FrameRate
  , displayMode :: TimeDisplayMode
  , height :: Number
  , pixelsPerFrame :: Number
  , scrollOffset :: Number
  , isDragging :: Boolean
  , showTooltip :: Boolean
  }

-- | Internal actions
data Action
  = Receive Input
  | HandleMouseDown MouseEvent
  | HandleMouseUp MouseEvent
  | HandleMouseEnter
  | HandleMouseLeave
  | HandleKeyDown KeyboardEvent

-- | Slot type helper
type Slot = H.Slot Query Output Unit

-- | Slot proxy
_playhead :: Proxy "playhead"
_playhead = Proxy

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // component
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Playhead component
component :: forall m. MonadAff m => H.Component Query Input Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval H.defaultEval
      { handleAction = handleAction
      , handleQuery = handleQuery
      , receive = Just <<< Receive
      }
  }

-- | Initial state from input
initialState :: Input -> State
initialState input =
  { currentFrame: input.currentFrame
  , frameRate: input.frameRate
  , displayMode: input.displayMode
  , height: input.height
  , pixelsPerFrame: input.pixelsPerFrame
  , scrollOffset: input.scrollOffset
  , isDragging: false
  , showTooltip: false
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // render
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render the playhead
render :: forall m. State -> H.ComponentHTML Action () m
render state =
  let
    xPos = Temporal.unwrapFrames state.currentFrame * state.pixelsPerFrame - state.scrollOffset
    frameLabel = formatFrameDisplay state
  in
    HH.div
      [ cls [ "absolute top-0 z-20 pointer-events-none" ]
      , HP.attr (HH.AttrName "style") ("left: " <> show xPos <> "px; height: " <> show state.height <> "px;")
      , HP.attr (HH.AttrName "data-component") "playhead"
      ]
      [ -- Draggable head
        renderPlayheadHead state frameLabel
      -- Vertical line
      , renderPlayheadLine state
      ]

-- | Render the draggable head
renderPlayheadHead :: forall m. State -> String -> H.ComponentHTML Action () m
renderPlayheadHead state label =
  let
    headClasses =
      "pointer-events-auto cursor-grab absolute -top-1 left-1/2 transform -translate-x-1/2 " <>
      "px-2 py-0.5 rounded-b text-xs font-mono whitespace-nowrap " <>
      "bg-primary text-primary-foreground shadow-md " <>
      (if state.isDragging then "cursor-grabbing ring-2 ring-primary/50" else "")
  in
    HH.div
      [ cls [ headClasses ]
      , HE.onMouseDown HandleMouseDown
      , HE.onMouseUp HandleMouseUp
      , HE.onMouseEnter (\_ -> HandleMouseEnter)
      , HE.onMouseLeave (\_ -> HandleMouseLeave)
      , HP.tabIndex 0
      , ARIA.role "slider"
      , ARIA.valueNow (show $ round $ Temporal.unwrapFrames state.currentFrame)
      , ARIA.label "Playhead position"
      ]
      [ HH.text label
      -- Caret pointing down
      , HH.div
          [ cls [ "absolute -bottom-1 left-1/2 transform -translate-x-1/2 w-0 h-0" ]
          , HP.attr (HH.AttrName "style") 
              "border-left: 4px solid transparent; border-right: 4px solid transparent; border-top: 4px solid hsl(var(--primary));"
          ]
          []
      ]

-- | Render the vertical line
renderPlayheadLine :: forall m. State -> H.ComponentHTML Action () m
renderPlayheadLine state =
  HH.div
    [ cls [ "absolute top-6 left-1/2 transform -translate-x-1/2 w-px bg-primary" ]
    , HP.attr (HH.AttrName "style") ("height: " <> show (state.height - 24.0) <> "px;")
    ]
    []

-- | Format frame for display
formatFrameDisplay :: State -> String
formatFrameDisplay state =
  case state.displayMode of
    FramesMode -> show (round $ Temporal.unwrapFrames state.currentFrame)
    TimecodeMode ->
      let
        tc = TC.fromFrames state.currentFrame state.frameRate false
      in
        TC.formatCompact tc
    SecondsMode ->
      let
        secs = Temporal.unwrapFrames state.currentFrame / Temporal.unwrapFps state.frameRate
      in
        formatSeconds secs

-- | Format seconds with 2 decimal places
formatSeconds :: Number -> String
formatSeconds n =
  let
    whole = round n
    frac = round ((n - toNumber whole) * 100.0)
  in
    show whole <> "." <> (if frac < 10 then "0" else "") <> show frac <> "s"
  where
    toNumber :: Int -> Number
    toNumber i = toNumberImpl i

foreign import toNumberImpl :: Int -> Number

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // handle action
-- ═══════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Receive input -> do
    H.modify_ \s -> s
      { currentFrame = input.currentFrame
      , frameRate = input.frameRate
      , displayMode = input.displayMode
      , height = input.height
      , pixelsPerFrame = input.pixelsPerFrame
      , scrollOffset = input.scrollOffset
      }
  
  HandleMouseDown _ -> do
    H.modify_ _ { isDragging = true }
    H.raise DragStart
  
  HandleMouseUp _ -> do
    state <- H.get
    when state.isDragging do
      H.modify_ _ { isDragging = false }
      H.raise DragEnd
  
  HandleMouseEnter -> do
    H.modify_ _ { showTooltip = true }
  
  HandleMouseLeave -> do
    H.modify_ _ { showTooltip = false }
  
  HandleKeyDown event -> do
    case KeyboardEvent.key event of
      "ArrowLeft" -> H.raise (NudgeRequested (-1))
      "ArrowRight" -> H.raise (NudgeRequested 1)
      "Home" -> H.raise (NudgeRequested (-999999))  -- Jump to start
      "End" -> H.raise (NudgeRequested 999999)      -- Jump to end
      _ -> pure unit

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // handle query
-- ═══════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action () Output m (Maybe a)
handleQuery = case _ of
  SetCurrentFrame frame' reply -> do
    H.modify_ _ { currentFrame = frame' }
    pure (Just reply)
  
  NudgeFrame n reply -> do
    state <- H.get
    let
      Frames f = state.currentFrame
      newFrame = max 0.0 (f + toNumber n)
    H.modify_ _ { currentFrame = Frames newFrame }
    pure (Just reply)
    where
      toNumber :: Int -> Number
      toNumber = toNumberImpl
