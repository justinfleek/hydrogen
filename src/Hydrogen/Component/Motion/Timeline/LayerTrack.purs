-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                      // hydrogen // component // motion // timeline // layertrack
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Layer Track for Animation Timeline
-- |
-- | A horizontal track representing a layer's duration in the timeline.
-- | Shows the layer as a colored bar with draggable in/out handles for
-- | trimming, and supports drag-to-move for repositioning in time.
-- |
-- | ## Features
-- |
-- | - Colored bar showing layer duration
-- | - Draggable left edge (in point)
-- | - Draggable right edge (out point)
-- | - Drag body to move layer in time
-- | - Selection highlight
-- | - Expand/collapse for property tracks
-- | - Layer name display
-- | - Lock and visibility indicators
-- |
-- | ## Visual Structure
-- |
-- | ```
-- |  ┌──────────────────────────────────────┐
-- |  │▌ Layer Name                        ▐│
-- |  └──────────────────────────────────────┘
-- |   ↑                                    ↑
-- |   in handle                     out handle
-- | ```
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Motion.Timeline.LayerTrack as LayerTrack
-- |
-- | HH.slot _layerTrack layerId LayerTrack.component
-- |   { layerId: layer.id
-- |   , name: layer.name
-- |   , inPoint: layer.inPoint
-- |   , outPoint: layer.outPoint
-- |   , color: layer.color
-- |   , isSelected: Array.elem layer.id selectedLayers
-- |   , isLocked: layer.locked
-- |   , isVisible: layer.visible
-- |   , isExpanded: layer.expanded
-- |   , pixelsPerFrame: ppf
-- |   , scrollOffset: scroll
-- |   }
-- |   HandleLayerTrackOutput
-- | ```
module Hydrogen.Component.Motion.Timeline.LayerTrack
  ( -- * Component
    component
  
  -- * Types
  , Query(..)
  , Input
  , Output(..)
  , LayerId(..)
  , Slot
  , DragMode(..)
  
  -- * Slot Type
  , _layerTrack
  ) where

import Prelude

import Data.Maybe (Maybe(Just))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.Schema.Dimension.Temporal (Frames)
import Hydrogen.Schema.Dimension.Temporal (unwrapFrames) as Temporal
import Hydrogen.Schema.Motion.TimeRange (TimeRange)
import Hydrogen.Schema.Motion.TimeRange as TR
import Hydrogen.UI.Core (cls)
import Type.Proxy (Proxy(Proxy))
import Web.UIEvent.MouseEvent (MouseEvent)
import Web.UIEvent.MouseEvent (shiftKey) as MouseEvent

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for a layer
newtype LayerId = LayerId String

derive instance eqLayerId :: Eq LayerId
derive instance ordLayerId :: Ord LayerId

instance showLayerId :: Show LayerId where
  show (LayerId id) = "Layer:" <> id

-- | What part of the track is being dragged
data DragMode
  = DragInPoint      -- Dragging left edge
  | DragOutPoint     -- Dragging right edge
  | DragBody         -- Dragging the whole layer
  | NoDrag

derive instance eqDragMode :: Eq DragMode

-- | Component input
type Input =
  { layerId :: LayerId
  , name :: String
  , inPoint :: Frames
  , outPoint :: Frames
  , color :: String           -- CSS color value
  , isSelected :: Boolean
  , isLocked :: Boolean
  , isVisible :: Boolean
  , isExpanded :: Boolean
  , pixelsPerFrame :: Number
  , scrollOffset :: Number
  , trackHeight :: Number
  }

-- | Component queries
data Query a
  = SetSelected Boolean a
  | SetExpanded Boolean a
  | SetTimeRange TimeRange a
  | GetTimeRange (TimeRange -> a)

-- | Component output
data Output
  = Selected LayerId Boolean            -- ID, add to selection?
  | ExpandToggled LayerId Boolean       -- ID, new expanded state
  | InPointChanged LayerId Frames       -- Trim in point
  | OutPointChanged LayerId Frames      -- Trim out point
  | Moved LayerId Frames                -- Layer moved to new start
  | DragStarted LayerId DragMode
  | DragEnded LayerId
  | DoubleClicked LayerId               -- Open layer settings
  | ContextMenuRequested LayerId        -- Right-click menu

-- | Internal state
type State =
  { layerId :: LayerId
  , name :: String
  , inPoint :: Frames
  , outPoint :: Frames
  , color :: String
  , isSelected :: Boolean
  , isLocked :: Boolean
  , isVisible :: Boolean
  , isExpanded :: Boolean
  , pixelsPerFrame :: Number
  , scrollOffset :: Number
  , trackHeight :: Number
  , dragMode :: DragMode
  , isHovered :: Boolean
  , hoverZone :: HoverZone
  }

-- | Which zone is being hovered
data HoverZone
  = HoverNone
  | HoverInHandle
  | HoverOutHandle
  | HoverBody

derive instance eqHoverZone :: Eq HoverZone

-- | Internal actions
data Action
  = Receive Input
  | HandleClick MouseEvent
  | HandleDoubleClick MouseEvent
  | HandleMouseDown MouseEvent HoverZone
  | HandleMouseUp MouseEvent
  | HandleMouseEnter HoverZone
  | HandleMouseLeave
  | HandleExpandToggle

-- | Slot type helper
type Slot = H.Slot Query Output LayerId

-- | Slot proxy
_layerTrack :: Proxy "layerTrack"
_layerTrack = Proxy

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // component
-- ═══════════════════════════════════════════════════════════════════════════════

-- | LayerTrack component
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
  { layerId: input.layerId
  , name: input.name
  , inPoint: input.inPoint
  , outPoint: input.outPoint
  , color: input.color
  , isSelected: input.isSelected
  , isLocked: input.isLocked
  , isVisible: input.isVisible
  , isExpanded: input.isExpanded
  , pixelsPerFrame: input.pixelsPerFrame
  , scrollOffset: input.scrollOffset
  , trackHeight: input.trackHeight
  , dragMode: NoDrag
  , isHovered: false
  , hoverZone: HoverNone
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // render
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Handle width for in/out trim handles
handleWidth :: Number
handleWidth = 8.0

-- | Minimum layer width in pixels
minLayerWidth :: Number
minLayerWidth = 20.0

-- | Render the layer track
render :: forall m. State -> H.ComponentHTML Action () m
render state =
  let
    -- Calculate positions
    inPx = Temporal.unwrapFrames state.inPoint * state.pixelsPerFrame - state.scrollOffset
    outPx = Temporal.unwrapFrames state.outPoint * state.pixelsPerFrame - state.scrollOffset
    width = max minLayerWidth (outPx - inPx)
    
    -- Container classes
    containerClasses = 
      "relative h-full select-none " <>
      (if state.isSelected then "z-10" else "z-0")
    
    -- Track bar classes
    barClasses =
      "absolute top-1 bottom-1 rounded flex items-center overflow-hidden " <>
      "transition-shadow duration-100 " <>
      (if state.isSelected then "ring-2 ring-primary ring-offset-1" else "") <>
      (if state.isLocked then " opacity-60" else "") <>
      (if not state.isVisible then " opacity-40" else "") <>
      (if state.dragMode /= NoDrag then " cursor-grabbing" else " cursor-grab")
  in
    HH.div
      [ cls [ containerClasses ]
      , HP.attr (HH.AttrName "data-component") "layer-track"
      , HP.attr (HH.AttrName "data-layer-id") (unwrapLayerId state.layerId)
      , HP.attr (HH.AttrName "style") ("height: " <> show state.trackHeight <> "px;")
      , HE.onMouseLeave (\_ -> HandleMouseLeave)
      ]
      [ -- The layer bar
        HH.div
          [ cls [ barClasses ]
          , HP.attr (HH.AttrName "style") 
              ("left: " <> show inPx <> "px; width: " <> show width <> "px; background-color: " <> state.color <> ";")
          , HE.onClick HandleClick
          , HE.onDoubleClick HandleDoubleClick
          , ARIA.role "button"
          , ARIA.label ("Layer: " <> state.name)
          ]
          [ -- In handle (left edge)
            renderInHandle state
          -- Layer content (name, icons)
          , renderLayerContent state
          -- Out handle (right edge)
          , renderOutHandle state
          ]
      -- Expand/collapse toggle (left of bar)
      , renderExpandToggle state inPx
      ]

-- | Extract string from LayerId
unwrapLayerId :: LayerId -> String
unwrapLayerId (LayerId id) = id

-- | Render the in point (left) handle
renderInHandle :: forall m. State -> H.ComponentHTML Action () m
renderInHandle state =
  let
    isActive = state.hoverZone == HoverInHandle || state.dragMode == DragInPoint
    handleClasses =
      "absolute left-0 top-0 bottom-0 cursor-ew-resize " <>
      "flex items-center justify-center " <>
      "transition-colors duration-100 " <>
      (if isActive then "bg-black/30" else "bg-black/10 hover:bg-black/20")
  in
    HH.div
      [ cls [ handleClasses ]
      , HP.attr (HH.AttrName "style") ("width: " <> show handleWidth <> "px;")
      , HE.onMouseDown (\e -> HandleMouseDown e HoverInHandle)
      , HE.onMouseUp HandleMouseUp
      , HE.onMouseEnter (\_ -> HandleMouseEnter HoverInHandle)
      , ARIA.label "Trim in point"
      ]
      [ -- Visual grip indicator
        HH.div
          [ cls [ "w-0.5 h-4 bg-white/50 rounded" ] ]
          []
      ]

-- | Render the out point (right) handle
renderOutHandle :: forall m. State -> H.ComponentHTML Action () m
renderOutHandle state =
  let
    isActive = state.hoverZone == HoverOutHandle || state.dragMode == DragOutPoint
    handleClasses =
      "absolute right-0 top-0 bottom-0 cursor-ew-resize " <>
      "flex items-center justify-center " <>
      "transition-colors duration-100 " <>
      (if isActive then "bg-black/30" else "bg-black/10 hover:bg-black/20")
  in
    HH.div
      [ cls [ handleClasses ]
      , HP.attr (HH.AttrName "style") ("width: " <> show handleWidth <> "px;")
      , HE.onMouseDown (\e -> HandleMouseDown e HoverOutHandle)
      , HE.onMouseUp HandleMouseUp
      , HE.onMouseEnter (\_ -> HandleMouseEnter HoverOutHandle)
      , ARIA.label "Trim out point"
      ]
      [ -- Visual grip indicator
        HH.div
          [ cls [ "w-0.5 h-4 bg-white/50 rounded" ] ]
          []
      ]

-- | Render the layer content (name, status icons)
renderLayerContent :: forall m. State -> H.ComponentHTML Action () m
renderLayerContent state =
  let
    contentClasses =
      "flex-1 px-2 flex items-center gap-1 min-w-0 " <>
      "cursor-grab"
  in
    HH.div
      [ cls [ contentClasses ]
      , HE.onMouseDown (\e -> HandleMouseDown e HoverBody)
      , HE.onMouseUp HandleMouseUp
      , HE.onMouseEnter (\_ -> HandleMouseEnter HoverBody)
      ]
      [ -- Layer name
        HH.span
          [ cls [ "text-xs font-medium text-white truncate drop-shadow-sm" ] ]
          [ HH.text state.name ]
      -- Status icons
      , if state.isLocked
          then HH.span 
            [ cls [ "text-white/70 text-xs" ] ] 
            [ HH.text "L" ]  -- Lock indicator
          else HH.text ""
      , if not state.isVisible
          then HH.span 
            [ cls [ "text-white/70 text-xs" ] ] 
            [ HH.text "H" ]  -- Hidden indicator
          else HH.text ""
      ]

-- | Render expand/collapse toggle
renderExpandToggle :: forall m. State -> Number -> H.ComponentHTML Action () m
renderExpandToggle state inPx =
  let
    toggleSize = 16.0
    toggleLeft = inPx - toggleSize - 4.0
    
    toggleClasses =
      "absolute top-1/2 transform -translate-y-1/2 " <>
      "w-4 h-4 flex items-center justify-center " <>
      "text-muted-foreground hover:text-foreground " <>
      "cursor-pointer transition-colors"
    
    icon = if state.isExpanded then "v" else ">"
  in
    HH.div
      [ cls [ toggleClasses ]
      , HP.attr (HH.AttrName "style") ("left: " <> show toggleLeft <> "px;")
      , HE.onClick (\_ -> HandleExpandToggle)
      , ARIA.role "button"
      , ARIA.label (if state.isExpanded then "Collapse layer" else "Expand layer")
      , ARIA.expanded (if state.isExpanded then "true" else "false")
      ]
      [ HH.span
          [ cls [ "text-xs font-mono" ] ]
          [ HH.text icon ]
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // handle action
-- ═══════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Receive input -> do
    H.modify_ \s -> s
      { layerId = input.layerId
      , name = input.name
      , inPoint = input.inPoint
      , outPoint = input.outPoint
      , color = input.color
      , isSelected = input.isSelected
      , isLocked = input.isLocked
      , isVisible = input.isVisible
      , isExpanded = input.isExpanded
      , pixelsPerFrame = input.pixelsPerFrame
      , scrollOffset = input.scrollOffset
      , trackHeight = input.trackHeight
      }
  
  HandleClick event -> do
    state <- H.get
    -- Don't process clicks on locked layers
    unless state.isLocked do
      let addToSelection = MouseEvent.shiftKey event
      H.raise (Selected state.layerId addToSelection)
  
  HandleDoubleClick _ -> do
    state <- H.get
    H.raise (DoubleClicked state.layerId)
  
  HandleMouseDown event zone -> do
    state <- H.get
    -- Don't allow dragging locked layers
    unless state.isLocked do
      let
        dragMode' = case zone of
          HoverInHandle -> DragInPoint
          HoverOutHandle -> DragOutPoint
          HoverBody -> DragBody
          HoverNone -> NoDrag
      
      -- Check for right-click
      if mouseButton event == 2
        then H.raise (ContextMenuRequested state.layerId)
        else when (dragMode' /= NoDrag) do
          H.modify_ _ { dragMode = dragMode' }
          H.raise (DragStarted state.layerId dragMode')
  
  HandleMouseUp _ -> do
    state <- H.get
    when (state.dragMode /= NoDrag) do
      H.modify_ _ { dragMode = NoDrag }
      H.raise (DragEnded state.layerId)
  
  HandleMouseEnter zone -> do
    H.modify_ _ { isHovered = true, hoverZone = zone }
  
  HandleMouseLeave -> do
    H.modify_ _ { isHovered = false, hoverZone = HoverNone }
  
  HandleExpandToggle -> do
    state <- H.get
    let newExpanded = not state.isExpanded
    H.modify_ _ { isExpanded = newExpanded }
    H.raise (ExpandToggled state.layerId newExpanded)

-- | Get mouse button (0=left, 1=middle, 2=right)
foreign import mouseButton :: MouseEvent -> Int

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // handle query
-- ═══════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action () Output m (Maybe a)
handleQuery = case _ of
  SetSelected selected reply -> do
    H.modify_ _ { isSelected = selected }
    pure (Just reply)
  
  SetExpanded expanded reply -> do
    H.modify_ _ { isExpanded = expanded }
    pure (Just reply)
  
  SetTimeRange range reply -> do
    H.modify_ _ 
      { inPoint = TR.inPoint range
      , outPoint = TR.outPoint range
      }
    pure (Just reply)
  
  GetTimeRange reply -> do
    state <- H.get
    let range = TR.timeRange state.inPoint state.outPoint
    pure (Just (reply range))
