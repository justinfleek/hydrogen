-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--               // hydrogen // component // motion // timeline // animationtimeline
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Animation Timeline - Main container for motion graphics timeline
-- |
-- | A professional-grade timeline component for animation editing, integrating
-- | ruler, playhead, layer tracks, property tracks, and keyframe markers into
-- | a cohesive scrubbing and editing interface.
-- |
-- | ## Features
-- |
-- | - Time ruler with frames/timecode/seconds display
-- | - Draggable playhead with keyboard nudging
-- | - Zoomable timeline with scroll synchronization
-- | - Layer tracks with in/out point trimming
-- | - Property tracks with keyframe editing
-- | - Multi-selection for layers and keyframes
-- | - Work area definition for preview/render bounds
-- | - Playback controls (play/pause/stop)
-- |
-- | ## Visual Structure
-- |
-- | ```
-- | ┌─────────────────────────────────────────────────────────┐
-- | │ [◀ Play ■]  00:00:30:00  [Zoom: 100%]                   │
-- | ├─────────────────────────────────────────────────────────┤
-- | │ 0         24        48        72        96              │ <- TimeRuler
-- | │      ▼                                                  │ <- Playhead
-- | ├─────────────────────────────────────────────────────────┤
-- | │ Layer 1  ┌────────────────────────┐                     │ <- LayerTrack
-- | │  ├ Pos   │ ◆──────◆──────◆        │                     │ <- PropertyTrack
-- | │  └ Rot   │    ◆────────◆         │                     │
-- | ├─────────────────────────────────────────────────────────┤
-- | │ Layer 2  ┌──────────────────┐                           │
-- | │  └ Opac  │ ◆──────────────◆ │                           │
-- | └─────────────────────────────────────────────────────────┘
-- | ```
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Motion.Timeline.AnimationTimeline as AnimTimeline
-- |
-- | HH.slot _timeline unit AnimTimeline.component
-- |   { frameRate: fps24
-- |   , duration: Frames 2880.0  -- 2 minutes at 24fps
-- |   , layers: myLayers
-- |   }
-- |   HandleTimelineOutput
-- | ```
module Hydrogen.Component.Motion.Timeline.AnimationTimeline
  ( -- * Component
    component
  
  -- * Types
  , Query(SetCurrentFrame, Play, Pause, Stop, SetZoomLevel, GetCurrentFrame, GetPlaybackState, GetSelectedLayers, GetSelectedKeyframes)
  , Input
  , Output(FrameChanged, PlaybackStateChanged, SelectionChanged, ZoomChanged, WorkAreaChanged, LayerTrimmed)
  , LayerData
  , Slot
  
  -- * Slot Type
  , _animationTimeline
  ) where

import Prelude

import Data.Array (filter, length, mapWithIndex)
import Data.Array (elem) as Array
import Data.Int (toNumber) as Int
import Data.Maybe (Maybe(Just, Nothing))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.Component.Motion.Timeline.LayerTrack as LayerTrack
import Hydrogen.Component.Motion.Timeline.Playhead as Playhead
import Hydrogen.Component.Motion.Timeline.TimeRuler as TimeRuler
import Hydrogen.Schema.Dimension.Temporal (FrameRate, Frames(Frames))
import Hydrogen.Schema.Dimension.Temporal (unwrapFrames) as Temporal
import Hydrogen.Schema.Motion.Keyframe (KeyframeId)
import Hydrogen.Schema.Motion.ZoomLevel (ZoomLevel)
import Hydrogen.Schema.Motion.ZoomLevel as Zoom
import Hydrogen.Style.Css as Css
import Hydrogen.Style.Motion as Motion
import Hydrogen.Style.Token as Token
import Hydrogen.UI.Core (cls)
import Type.Proxy (Proxy(Proxy))

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Layer data for timeline display
-- | Contains all information needed to render a layer track
type LayerData =
  { layerId :: LayerTrack.LayerId
  , name :: String
  , inPoint :: Frames
  , outPoint :: Frames
  , color :: String
  , isLocked :: Boolean
  , isVisible :: Boolean
  }

-- | Component input
type Input =
  { frameRate :: FrameRate
  , duration :: Frames
  , layers :: Array LayerData
  , initialFrame :: Frames
  }

-- | Component queries - external commands
data Query a
  = SetCurrentFrame Frames a
  | Play a
  | Pause a
  | Stop a
  | SetZoomLevel ZoomLevel a
  | GetCurrentFrame (Frames -> a)
  | GetPlaybackState (Boolean -> a)
  | GetSelectedLayers (Array LayerTrack.LayerId -> a)
  | GetSelectedKeyframes (Array KeyframeId -> a)

-- | Component output - events emitted to parent
data Output
  = FrameChanged Frames
  | PlaybackStateChanged Boolean
  | SelectionChanged (Array LayerTrack.LayerId) (Array KeyframeId)
  | ZoomChanged ZoomLevel
  | WorkAreaChanged (Maybe Frames) (Maybe Frames)
  | LayerTrimmed LayerTrack.LayerId Frames Frames  -- ID, new in, new out

-- | Internal state
type State =
  { frameRate :: FrameRate
  , duration :: Frames
  , currentFrame :: Frames
  , zoomLevel :: ZoomLevel
  , scrollOffset :: Number
  , isPlaying :: Boolean
  , displayMode :: TimeRuler.TimeDisplayMode
  , workAreaStart :: Maybe Frames
  , workAreaEnd :: Maybe Frames
  , layers :: Array LayerData
  , expandedLayers :: Array LayerTrack.LayerId
  , selectedLayers :: Array LayerTrack.LayerId
  , selectedKeyframes :: Array KeyframeId
  , trackHeight :: Number
  , rulerHeight :: Number
  , playheadHeight :: Number
  }

-- | Internal actions
data Action
  = Initialize
  | Receive Input
  | HandleTimeRulerOutput TimeRuler.Output
  | HandlePlayheadOutput Playhead.Output
  | HandleLayerTrackOutput LayerTrack.Output
  | TogglePlayback
  | StopPlayback
  | ZoomIn
  | ZoomOut
  | SetDisplayMode TimeRuler.TimeDisplayMode
  | HandleScroll Number

-- | Slot type for child components
type Slots =
  ( timeRuler :: H.Slot TimeRuler.Query TimeRuler.Output Unit
  , playhead :: H.Slot Playhead.Query Playhead.Output Unit
  , layerTrack :: H.Slot LayerTrack.Query LayerTrack.Output LayerTrack.LayerId
  )

-- | Slot type helper for parent components
type Slot = H.Slot Query Output Unit

-- | Slot proxy
_animationTimeline :: Proxy "animationTimeline"
_animationTimeline = Proxy

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // component
-- ═══════════════════════════════════════════════════════════════════════════════

-- | AnimationTimeline component
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
  , currentFrame: input.initialFrame
  , zoomLevel: Zoom.zoom100
  , scrollOffset: 0.0
  , isPlaying: false
  , displayMode: TimeRuler.TimecodeMode
  , workAreaStart: Nothing
  , workAreaEnd: Nothing
  , layers: input.layers
  , expandedLayers: []
  , selectedLayers: []
  , selectedKeyframes: []
  , trackHeight: 28.0
  , rulerHeight: 24.0
  , playheadHeight: 0.0  -- Calculated on render
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // render
-- ═══════════════════════════════════════════════════════════════════════════════

-- ─────────────────────────────────────────────────────────────────────────────────
--                                                               // style constants
-- ─────────────────────────────────────────────────────────────────────────────────

-- | Base pixels per frame at 100% zoom
basePixelsPerFrame :: Number
basePixelsPerFrame = 10.0

-- | Container styles - main timeline wrapper
containerStyles :: String
containerStyles = Css.cx
  [ "flex flex-col w-full"
  , "bg-background"
  , "border border-border"
  , Token.radius Token.RoundedLg
  , "overflow-hidden"
  ]

-- | Toolbar styles - control bar at top
toolbarStyles :: String
toolbarStyles = Css.cx
  [ "flex items-center"
  , Token.gap Token.S3
  , Token.paddingX Token.S3
  , Token.paddingY Token.S2
  , "border-b border-border"
  , "bg-muted/30"
  ]

-- | Button base styles with transitions
buttonBaseStyles :: String
buttonBaseStyles = Css.cx
  [ Token.paddingX Token.S2
  , Token.paddingY Token.S1
  , Token.radius Token.RoundedMd
  , "text-sm"
  , Motion.transition Motion.All
  , Motion.duration Motion.Quick
  , Motion.easing Motion.EaseOut
  , Css.motionReduce "transition-none"
  ]

-- | Primary button styles (play button)
primaryButtonStyles :: String
primaryButtonStyles = Css.cx
  [ buttonBaseStyles
  , "bg-primary text-primary-foreground"
  , Css.hover "bg-primary/90"
  , Css.active "scale-95"
  , Css.motionReduce (Css.active "scale-100")
  ]

-- | Secondary button styles (stop, zoom)
secondaryButtonStyles :: String
secondaryButtonStyles = Css.cx
  [ buttonBaseStyles
  , "bg-muted"
  , Css.hover "bg-muted/80"
  ]

-- | Toggle button styles (display mode)
toggleButtonStyles :: Boolean -> String
toggleButtonStyles isActive = Css.cx
  [ buttonBaseStyles
  , "text-xs"
  , Css.when isActive "bg-primary text-primary-foreground"
  , Css.unless isActive "bg-muted text-muted-foreground"
  , Css.unless isActive (Css.hover "bg-muted/80")
  ]

-- | Frame counter display styles
frameDisplayStyles :: String
frameDisplayStyles = Css.cx
  [ Token.paddingX Token.S3
  , Token.paddingY Token.S1
  , "bg-muted"
  , Token.radius Token.RoundedMd
  , "text-sm font-mono"
  ]

-- | Content area styles
contentAreaStyles :: String
contentAreaStyles = "relative flex-1 overflow-hidden"

-- ─────────────────────────────────────────────────────────────────────────────────
--                                                              // render functions
-- ─────────────────────────────────────────────────────────────────────────────────

-- | Pixels per frame at current zoom
pixelsPerFrame :: State -> Number
pixelsPerFrame state = Zoom.pixelsPerFrame state.zoomLevel basePixelsPerFrame

-- | Total content width in pixels
contentWidth :: State -> Number
contentWidth state = 
  Temporal.unwrapFrames state.duration * pixelsPerFrame state

-- | Total tracks height
tracksHeight :: State -> Number
tracksHeight state =
  Int.toNumber (length state.layers) * state.trackHeight

-- | Render the timeline
render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  let
    totalHeight = state.rulerHeight + tracksHeight state
    totalWidth = contentWidth state
  in
    HH.div
      [ cls [ containerStyles ]
      , HP.attr (HH.AttrName "data-component") "animation-timeline"
      , HP.attr (HH.AttrName "data-content-width") (show totalWidth)
      , HP.attr (HH.AttrName "role") "application"
      , ARIA.label "Animation Timeline"
      ]
      [ -- Toolbar
        renderToolbar state
      -- Timeline content
      , HH.div
          [ cls [ contentAreaStyles ]
          , HP.attr (HH.AttrName "style") ("min-height: " <> show totalHeight <> "px;")
          ]
          [ -- Time ruler
            renderTimeRuler state
          -- Tracks area
          , renderTracksArea state
          -- Playhead (positioned absolutely over everything)
          , renderPlayhead state totalHeight
          ]
      ]

-- | Render the toolbar with controls
renderToolbar :: forall m. State -> H.ComponentHTML Action Slots m
renderToolbar state =
  let
    playButtonLabel = if state.isPlaying then "Pause" else "Play"
    playButtonIcon = if state.isPlaying then "⏸" else "▶"
    
    currentFrameDisplay = 
      show (Temporal.unwrapFrames state.currentFrame) <> " / " <>
      show (Temporal.unwrapFrames state.duration)
  in
    HH.div
      [ cls [ toolbarStyles ] ]
      [ -- Playback controls
        HH.div
          [ cls [ Css.cx [ "flex items-center", Token.gap Token.S1 ] ] ]
          [ -- Play/Pause button
            HH.button
              [ cls [ primaryButtonStyles ]
              , HE.onClick (\_ -> TogglePlayback)
              , ARIA.label playButtonLabel
              ]
              [ HH.text playButtonIcon ]
          -- Stop button
          , HH.button
              [ cls [ secondaryButtonStyles ]
              , HE.onClick (\_ -> StopPlayback)
              , ARIA.label "Stop"
              ]
              [ HH.text "■" ]
          ]
      -- Frame display
      , HH.div
          [ cls [ frameDisplayStyles ] ]
          [ HH.text currentFrameDisplay ]
      -- Display mode selector
      , HH.div
          [ cls [ Css.cx [ "flex items-center", Token.gap Token.S1 ] ] ]
          [ renderDisplayModeButton state TimeRuler.FramesMode "F"
          , renderDisplayModeButton state TimeRuler.TimecodeMode "TC"
          , renderDisplayModeButton state TimeRuler.SecondsMode "S"
          ]
      -- Spacer
      , HH.div [ cls [ "flex-1" ] ] []
      -- Zoom controls
      , HH.div
          [ cls [ Css.cx [ "flex items-center", Token.gap Token.S1 ] ] ]
          [ HH.button
              [ cls [ secondaryButtonStyles ]
              , HE.onClick (\_ -> ZoomOut)
              , ARIA.label "Zoom out"
              ]
              [ HH.text "-" ]
          , HH.span
              [ cls [ Css.cx [ Token.paddingX Token.S2, "text-sm text-muted-foreground" ] ] ]
              [ HH.text (show (Zoom.toPercentage state.zoomLevel) <> "%") ]
          , HH.button
              [ cls [ secondaryButtonStyles ]
              , HE.onClick (\_ -> ZoomIn)
              , ARIA.label "Zoom in"
              ]
              [ HH.text "+" ]
          ]
      ]

-- | Render a display mode button
renderDisplayModeButton :: forall m. State -> TimeRuler.TimeDisplayMode -> String -> H.ComponentHTML Action Slots m
renderDisplayModeButton state mode label =
  let
    isActive = state.displayMode == mode
  in
    HH.button
      [ cls [ toggleButtonStyles isActive ]
      , HE.onClick (\_ -> SetDisplayMode mode)
      , ARIA.pressed (if isActive then "true" else "false")
      ]
      [ HH.text label ]

-- | Render the time ruler
renderTimeRuler :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
renderTimeRuler state =
  HH.div
    [ cls [ "relative border-b border-border" ]
    , HP.attr (HH.AttrName "style") ("height: " <> show state.rulerHeight <> "px;")
    ]
    [ HH.slot TimeRuler._timeRuler unit TimeRuler.component
        { frameRate: state.frameRate
        , duration: state.duration
        , currentFrame: state.currentFrame
        , zoomLevel: state.zoomLevel
        , displayMode: state.displayMode
        , scrollOffset: state.scrollOffset
        }
        HandleTimeRulerOutput
    ]

-- | Render the tracks area
renderTracksArea :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
renderTracksArea state =
  HH.div
    [ cls [ "relative overflow-y-auto" ]
    , HP.attr (HH.AttrName "style") ("padding-top: " <> show state.rulerHeight <> "px;")
    ]
    (mapWithIndex (renderLayerTrack state) state.layers)

-- | Render a single layer track
renderLayerTrack :: forall m. MonadAff m => State -> Int -> LayerData -> H.ComponentHTML Action Slots m
renderLayerTrack state _index layer =
  let
    isExpanded = Array.elem layer.layerId state.expandedLayers
    isSelected = Array.elem layer.layerId state.selectedLayers
  in
    HH.slot LayerTrack._layerTrack layer.layerId LayerTrack.component
      { layerId: layer.layerId
      , name: layer.name
      , inPoint: layer.inPoint
      , outPoint: layer.outPoint
      , color: layer.color
      , isSelected: isSelected
      , isLocked: layer.isLocked
      , isVisible: layer.isVisible
      , isExpanded: isExpanded
      , pixelsPerFrame: pixelsPerFrame state
      , scrollOffset: state.scrollOffset
      , trackHeight: state.trackHeight
      }
      HandleLayerTrackOutput

-- | Render the playhead
renderPlayhead :: forall m. MonadAff m => State -> Number -> H.ComponentHTML Action Slots m
renderPlayhead state totalHeight =
  HH.div
    [ cls [ "absolute top-0 left-0 right-0 pointer-events-none" ]
    , HP.attr (HH.AttrName "style") ("height: " <> show totalHeight <> "px;")
    ]
    [ HH.slot Playhead._playhead unit Playhead.component
        { currentFrame: state.currentFrame
        , frameRate: state.frameRate
        , displayMode: state.displayMode
        , height: totalHeight
        , pixelsPerFrame: pixelsPerFrame state
        , scrollOffset: state.scrollOffset
        }
        HandlePlayheadOutput
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // handle action
-- ═══════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Output m Unit
handleAction = case _ of
  Initialize -> do
    -- Initial setup - could load persisted state, etc.
    pure unit
  
  Receive input -> do
    H.modify_ \s -> s
      { frameRate = input.frameRate
      , duration = input.duration
      , layers = input.layers
      }
  
  HandleTimeRulerOutput output -> case output of
    TimeRuler.Seek frame -> do
      H.modify_ _ { currentFrame = frame }
      H.raise (FrameChanged frame)
    
    TimeRuler.ScrubStart -> do
      -- Could pause playback during scrub
      pure unit
    
    TimeRuler.ScrubEnd -> do
      pure unit
  
  HandlePlayheadOutput output -> case output of
    Playhead.DragStart -> do
      pure unit
    
    Playhead.Dragging frame -> do
      H.modify_ _ { currentFrame = frame }
      H.raise (FrameChanged frame)
    
    Playhead.DragEnd -> do
      pure unit
    
    Playhead.NudgeRequested delta -> do
      state <- H.get
      let 
        newFrame = Frames (Temporal.unwrapFrames state.currentFrame + Int.toNumber delta)
        clampedFrame = clampFrame (Frames 0.0) state.duration newFrame
      H.modify_ _ { currentFrame = clampedFrame }
      H.raise (FrameChanged clampedFrame)
  
  HandleLayerTrackOutput output -> case output of
    LayerTrack.Selected layerId addToSelection -> do
      state <- H.get
      let
        newSelection = 
          if addToSelection
            then if Array.elem layerId state.selectedLayers
                   then filter (_ /= layerId) state.selectedLayers
                   else state.selectedLayers <> [layerId]
            else [layerId]
      H.modify_ _ { selectedLayers = newSelection }
      H.raise (SelectionChanged newSelection state.selectedKeyframes)
    
    LayerTrack.ExpandToggled layerId expanded -> do
      state <- H.get
      let
        newExpanded = 
          if expanded
            then state.expandedLayers <> [layerId]
            else filter (_ /= layerId) state.expandedLayers
      H.modify_ _ { expandedLayers = newExpanded }
    
    LayerTrack.InPointChanged layerId newIn -> do
      state <- H.get
      let 
        updateLayer l = 
          if l.layerId == layerId 
            then l { inPoint = newIn }
            else l
        newLayers = map updateLayer state.layers
        outPoint = findLayerOutPoint layerId state.layers
      H.modify_ _ { layers = newLayers }
      H.raise (LayerTrimmed layerId newIn outPoint)
    
    LayerTrack.OutPointChanged layerId newOut -> do
      state <- H.get
      let 
        updateLayer l = 
          if l.layerId == layerId 
            then l { outPoint = newOut }
            else l
        newLayers = map updateLayer state.layers
        inPoint = findLayerInPoint layerId state.layers
      H.modify_ _ { layers = newLayers }
      H.raise (LayerTrimmed layerId inPoint newOut)
    
    LayerTrack.Moved _layerId _newStart -> do
      -- Handle layer move - update in/out points
      pure unit
    
    LayerTrack.DragStarted _layerId _mode -> do
      pure unit
    
    LayerTrack.DragEnded _layerId -> do
      pure unit
    
    LayerTrack.DoubleClicked _layerId -> do
      -- Could open layer settings
      pure unit
    
    LayerTrack.ContextMenuRequested _layerId -> do
      -- Could show context menu
      pure unit
  
  TogglePlayback -> do
    state <- H.get
    let newPlaying = not state.isPlaying
    H.modify_ _ { isPlaying = newPlaying }
    H.raise (PlaybackStateChanged newPlaying)
  
  StopPlayback -> do
    H.modify_ _ { isPlaying = false, currentFrame = Frames 0.0 }
    H.raise (PlaybackStateChanged false)
    H.raise (FrameChanged (Frames 0.0))
  
  ZoomIn -> do
    state <- H.get
    let newZoom = Zoom.zoomIn state.zoomLevel
    H.modify_ _ { zoomLevel = newZoom }
    H.raise (ZoomChanged newZoom)
  
  ZoomOut -> do
    state <- H.get
    let newZoom = Zoom.zoomOut state.zoomLevel
    H.modify_ _ { zoomLevel = newZoom }
    H.raise (ZoomChanged newZoom)
  
  SetDisplayMode mode -> do
    H.modify_ _ { displayMode = mode }
  
  HandleScroll offset -> do
    H.modify_ _ { scrollOffset = offset }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // handle query
-- ═══════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action Slots Output m (Maybe a)
handleQuery = case _ of
  SetCurrentFrame frame reply -> do
    H.modify_ _ { currentFrame = frame }
    pure (Just reply)
  
  Play reply -> do
    H.modify_ _ { isPlaying = true }
    H.raise (PlaybackStateChanged true)
    pure (Just reply)
  
  Pause reply -> do
    H.modify_ _ { isPlaying = false }
    H.raise (PlaybackStateChanged false)
    pure (Just reply)
  
  Stop reply -> do
    H.modify_ _ { isPlaying = false, currentFrame = Frames 0.0 }
    H.raise (PlaybackStateChanged false)
    pure (Just reply)
  
  SetZoomLevel zoom reply -> do
    H.modify_ _ { zoomLevel = zoom }
    H.raise (ZoomChanged zoom)
    pure (Just reply)
  
  GetCurrentFrame reply -> do
    state <- H.get
    pure (Just (reply state.currentFrame))
  
  GetPlaybackState reply -> do
    state <- H.get
    pure (Just (reply state.isPlaying))
  
  GetSelectedLayers reply -> do
    state <- H.get
    pure (Just (reply state.selectedLayers))
  
  GetSelectedKeyframes reply -> do
    state <- H.get
    pure (Just (reply state.selectedKeyframes))

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Clamp a frame to valid range
clampFrame :: Frames -> Frames -> Frames -> Frames
clampFrame (Frames minF) (Frames maxF) (Frames f) = 
  Frames (max minF (min maxF f))

-- | Find a layer's out point
findLayerOutPoint :: LayerTrack.LayerId -> Array LayerData -> Frames
findLayerOutPoint layerId layers =
  case filter (\l -> l.layerId == layerId) layers of
    [layer] -> layer.outPoint
    _ -> Frames 0.0

-- | Find a layer's in point
findLayerInPoint :: LayerTrack.LayerId -> Array LayerData -> Frames
findLayerInPoint layerId layers =
  case filter (\l -> l.layerId == layerId) layers of
    [layer] -> layer.inPoint
    _ -> Frames 0.0
