-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // component // motion // timeline // ruler
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Frame/Timecode Ruler for Animation Timeline
-- |
-- | Displays time markers along the top of the timeline. Supports multiple
-- | display modes (frames, timecode, seconds) and adapts tick density to
-- | the current zoom level.
-- |
-- | ## Features
-- |
-- | - Frame numbers at major tick intervals
-- | - Minor ticks for visual rhythm
-- | - Click to seek to frame
-- | - Drag to scrub through timeline
-- | - Adapts to zoom level
-- | - Multiple display modes
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Motion.Timeline.TimeRuler as TimeRuler
-- |
-- | HH.slot _timeRuler unit TimeRuler.component
-- |   { frameRate: fps24
-- |   , duration: Frames 2880.0
-- |   , currentFrame: Frames 100.0
-- |   , zoomLevel: Zoom.zoom100
-- |   , displayMode: TimeRuler.Frames
-- |   , scrollOffset: 0.0
-- |   }
-- |   HandleTimeRulerOutput
-- | ```
module Hydrogen.Component.Motion.Timeline.TimeRuler
  ( -- * Component
    component
  
  -- * Types
  , Query(SetCurrentFrame, SetZoomLevel, SetDisplayMode, Refresh)
  , Input
  , Output(Seek, ScrubStart, ScrubEnd)
  , TimeDisplayMode(FramesMode, TimecodeMode, SecondsMode)
  , Slot
  
  -- * Slot Type
  , _timeRuler
  ) where

import Prelude

import Data.Array (mapMaybe, range)
import Data.Int (floor, round)
import Data.Int (toNumber) as Int
import Data.Maybe (Maybe(Nothing, Just))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.Schema.Dimension.Temporal (FrameRate, Frames(Frames))
import Hydrogen.Schema.Dimension.Temporal (unwrapFrames, unwrapFps) as Temporal
import Hydrogen.Schema.Motion.Timecode as TC
import Hydrogen.Schema.Motion.ZoomLevel (ZoomLevel)
import Hydrogen.Schema.Motion.ZoomLevel as Zoom
import Hydrogen.UI.Core (cls)
import Type.Proxy (Proxy(Proxy))
import Web.Event.Event (Event)
import Web.UIEvent.MouseEvent (MouseEvent)
import Web.UIEvent.MouseEvent (toEvent) as MouseEvent

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Extract clientX from a mouse event
foreign import getClientX :: Event -> Number

-- | Get the bounding client rect left position of the target element
foreign import getTargetLeft :: Event -> Number

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Time display mode
data TimeDisplayMode
  = FramesMode       -- Display raw frame numbers
  | TimecodeMode     -- Display SMPTE timecode (HH:MM:SS:FF)
  | SecondsMode      -- Display seconds with decimals

derive instance eqTimeDisplayMode :: Eq TimeDisplayMode

instance showTimeDisplayMode :: Show TimeDisplayMode where
  show FramesMode = "frames"
  show TimecodeMode = "timecode"
  show SecondsMode = "seconds"

-- | Component input
type Input =
  { frameRate :: FrameRate
  , duration :: Frames
  , currentFrame :: Frames
  , zoomLevel :: ZoomLevel
  , displayMode :: TimeDisplayMode
  , scrollOffset :: Number
  }

-- | Component queries
data Query a
  = SetCurrentFrame Frames a
  | SetZoomLevel ZoomLevel a
  | SetDisplayMode TimeDisplayMode a
  | Refresh a

-- | Component output
data Output
  = Seek Frames           -- User clicked/dragged to seek
  | ScrubStart            -- User started scrubbing
  | ScrubEnd              -- User ended scrubbing

-- | Internal state
type State =
  { frameRate :: FrameRate
  , duration :: Frames
  , currentFrame :: Frames
  , zoomLevel :: ZoomLevel
  , displayMode :: TimeDisplayMode
  , scrollOffset :: Number
  , isScrubbing :: Boolean
  , rulerWidth :: Number
  }

-- | Internal actions
data Action
  = Initialize
  | Receive Input
  | HandleClick MouseEvent
  | HandleMouseDown MouseEvent
  | HandleMouseMove MouseEvent
  | HandleMouseUp MouseEvent
  | HandleMouseLeave MouseEvent

-- | Slot type helper
type Slot = H.Slot Query Output Unit

-- | Slot proxy
_timeRuler :: Proxy "timeRuler"
_timeRuler = Proxy

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // component
-- ═══════════════════════════════════════════════════════════════════════════════

-- | TimeRuler component
component :: forall m. MonadAff m => H.Component Query Input Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval H.defaultEval
      { handleAction = handleAction
      , handleQuery = handleQuery
      , receive = Just <<< Receive
      , initialize = Just Initialize
      }
  }

-- | Initial state from input
initialState :: Input -> State
initialState input =
  { frameRate: input.frameRate
  , duration: input.duration
  , currentFrame: input.currentFrame
  , zoomLevel: input.zoomLevel
  , displayMode: input.displayMode
  , scrollOffset: input.scrollOffset
  , isScrubbing: false
  , rulerWidth: 800.0  -- Default, will be measured
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // render
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Base pixels per frame at 100% zoom
basePixelsPerFrame :: Number
basePixelsPerFrame = 10.0

-- | Render the ruler
render :: forall m. State -> H.ComponentHTML Action () m
render state =
  let
    ppf = Zoom.pixelsPerFrame state.zoomLevel basePixelsPerFrame
    totalWidth = Temporal.unwrapFrames state.duration * ppf
    ticks = generateTicks state
  in
    HH.div
      [ cls [ "relative h-8 bg-muted/50 border-b border-border select-none cursor-pointer overflow-hidden" ]
      , HP.attr (HH.AttrName "data-component") "time-ruler"
      , HE.onMouseDown HandleMouseDown
      , HE.onMouseMove HandleMouseMove
      , HE.onMouseUp HandleMouseUp
      , HE.onMouseLeave HandleMouseLeave
      , HE.onClick HandleClick
      , ARIA.role "slider"
      , ARIA.valueMin "0"
      , ARIA.valueMax (show $ round $ Temporal.unwrapFrames state.duration)
      , ARIA.valueNow (show $ round $ Temporal.unwrapFrames state.currentFrame)
      , ARIA.label "Timeline position"
      ]
      [ -- Scrollable tick container
        HH.div
          [ cls [ "absolute top-0 left-0 h-full" ]
          , HP.attr (HH.AttrName "style") ("width: " <> show totalWidth <> "px; transform: translateX(" <> show (negate state.scrollOffset) <> "px);")
          ]
          (map (renderTick state ppf) ticks)
      , -- Current frame indicator at top
        renderCurrentFrameIndicator state
      ]

-- | Tick mark data
type TickMark =
  { frame :: Int
  , isMajor :: Boolean
  , label :: Maybe String
  }

-- | Generate tick marks based on zoom level
generateTicks :: State -> Array TickMark
generateTicks state =
  let
    totalFrames' = round $ Temporal.unwrapFrames state.duration
    fps = round $ Temporal.unwrapFps state.frameRate
    zoom = Zoom.toNumber state.zoomLevel
    
    -- Calculate tick intervals based on zoom
    -- At low zoom, show fewer ticks; at high zoom, show more
    { major: majorInterval, minor: minorInterval } = calculateTickIntervals fps zoom
    
    -- Generate all frame positions
    allFrames = range 0 totalFrames'
    
    -- Filter to only tick positions
    tickFrames = mapMaybe (filterToTick majorInterval minorInterval) allFrames
  in
    map (makeTickMark state majorInterval) tickFrames

-- | Calculate tick intervals based on frame rate and zoom
calculateTickIntervals :: Int -> Number -> { major :: Int, minor :: Int }
calculateTickIntervals fps zoom
  | zoom < 0.1 = { major: fps * 60, minor: fps * 10 }     -- Minutes, 10 seconds
  | zoom < 0.25 = { major: fps * 10, minor: fps }          -- 10 seconds, seconds
  | zoom < 0.5 = { major: fps, minor: fps / 2 }            -- Seconds, half-seconds
  | zoom < 1.0 = { major: fps, minor: fps / 4 }            -- Seconds, quarter-seconds
  | zoom < 2.0 = { major: fps / 2, minor: 5 }              -- Half-seconds, 5 frames
  | zoom < 4.0 = { major: 10, minor: 1 }                   -- 10 frames, 1 frame
  | otherwise = { major: 5, minor: 1 }                     -- 5 frames, every frame

-- | Filter frame number to tick position
filterToTick :: Int -> Int -> Int -> Maybe Int
filterToTick major minor f
  | major > 0 && f `mod` minor == 0 = Just f
  | major == 0 = Nothing
  | otherwise = Nothing

-- | Create tick mark data
makeTickMark :: State -> Int -> Int -> TickMark
makeTickMark state majorInterval f =
  let
    isMajor' = majorInterval > 0 && f `mod` majorInterval == 0
    label' = 
      if isMajor' 
        then Just (formatFrameLabel state f)
        else Nothing
  in
    { frame: f
    , isMajor: isMajor'
    , label: label'
    }

-- | Format frame number for display
formatFrameLabel :: State -> Int -> String
formatFrameLabel state f =
  case state.displayMode of
    FramesMode -> show f
    TimecodeMode -> 
      let
        tc = TC.fromFrames (Frames (Int.toNumber f)) state.frameRate false
      in
        TC.formatCompact tc
    SecondsMode ->
      let
        secs = Int.toNumber f / Temporal.unwrapFps state.frameRate
      in
        formatSeconds secs

-- | Format seconds with 2 decimal places
formatSeconds :: Number -> String
formatSeconds n =
  let
    whole = floor n
    frac = round ((n - Int.toNumber whole) * 100.0)
  in
    show whole <> "." <> (if frac < 10 then "0" else "") <> show frac <> "s"

-- | Render a single tick mark
renderTick :: forall m. State -> Number -> TickMark -> H.ComponentHTML Action () m
renderTick _state ppf tick =
  let
    xPos = Int.toNumber tick.frame * ppf
    tickHeight = if tick.isMajor then "h-4" else "h-2"
    tickColor = if tick.isMajor then "bg-foreground/50" else "bg-foreground/20"
  in
    HH.div
      [ cls [ "absolute bottom-0 flex flex-col items-center" ]
      , HP.attr (HH.AttrName "style") ("left: " <> show xPos <> "px;")
      ]
      [ -- Label (if major)
        case tick.label of
          Just label ->
            HH.span
              [ cls [ "text-xs text-muted-foreground absolute -top-1 transform -translate-x-1/2 whitespace-nowrap" ] ]
              [ HH.text label ]
          Nothing ->
            HH.text ""
      -- Tick mark
      , HH.div
          [ cls [ "w-px", tickHeight, tickColor ] ]
          []
      ]

-- | Render current frame indicator
renderCurrentFrameIndicator :: forall m. State -> H.ComponentHTML Action () m
renderCurrentFrameIndicator state =
  let
    ppf = Zoom.pixelsPerFrame state.zoomLevel basePixelsPerFrame
    xPos = Temporal.unwrapFrames state.currentFrame * ppf - state.scrollOffset
  in
    HH.div
      [ cls [ "absolute top-0 h-full w-px bg-primary z-10 pointer-events-none" ]
      , HP.attr (HH.AttrName "style") ("left: " <> show xPos <> "px;")
      ]
      []

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // handle action
-- ═══════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    -- Could measure element width here
    pure unit
  
  Receive input -> do
    H.modify_ \s -> s
      { frameRate = input.frameRate
      , duration = input.duration
      , currentFrame = input.currentFrame
      , zoomLevel = input.zoomLevel
      , displayMode = input.displayMode
      , scrollOffset = input.scrollOffset
      }
  
  HandleClick event -> do
    state <- H.get
    case clientXToFrame state (MouseEvent.toEvent event) of
      Just frame' -> H.raise (Seek frame')
      Nothing -> pure unit
  
  HandleMouseDown event -> do
    H.modify_ _ { isScrubbing = true }
    H.raise ScrubStart
    state <- H.get
    case clientXToFrame state (MouseEvent.toEvent event) of
      Just frame' -> H.raise (Seek frame')
      Nothing -> pure unit
  
  HandleMouseMove event -> do
    state <- H.get
    when state.isScrubbing do
      case clientXToFrame state (MouseEvent.toEvent event) of
        Just frame' -> H.raise (Seek frame')
        Nothing -> pure unit
  
  HandleMouseUp _ -> do
    state <- H.get
    when state.isScrubbing do
      H.modify_ _ { isScrubbing = false }
      H.raise ScrubEnd
  
  HandleMouseLeave _ -> do
    state <- H.get
    when state.isScrubbing do
      H.modify_ _ { isScrubbing = false }
      H.raise ScrubEnd

-- | Convert client X position to frame number
-- |
-- | Uses FFI to access clientX from the event and element bounds,
-- | then calculates the frame based on scroll offset and zoom level.
clientXToFrame :: State -> Event -> Maybe Frames
clientXToFrame state event = 
  let
    clientX = getClientX event
    elementLeft = getTargetLeft event
    relativeX = clientX - elementLeft + state.scrollOffset
    ppf = Zoom.pixelsPerFrame state.zoomLevel basePixelsPerFrame
    frameNum = relativeX / ppf
    maxFrame = Temporal.unwrapFrames state.duration
  in
    -- Clamp to valid range
    if frameNum < 0.0
      then Just (Frames 0.0)
      else if frameNum > maxFrame
        then Just (Frames maxFrame)
        else Just (Frames frameNum)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // handle query
-- ═══════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action () Output m (Maybe a)
handleQuery = case _ of
  SetCurrentFrame frame' reply -> do
    H.modify_ _ { currentFrame = frame' }
    pure (Just reply)
  
  SetZoomLevel zoom reply -> do
    H.modify_ _ { zoomLevel = zoom }
    pure (Just reply)
  
  SetDisplayMode mode reply -> do
    H.modify_ _ { displayMode = mode }
    pure (Just reply)
  
  Refresh reply -> do
    pure (Just reply)
