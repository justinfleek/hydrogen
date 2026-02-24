-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                   // hydrogen // component // motion // timeline // keyframemarker
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Keyframe marker for Animation Timeline
-- |
-- | A diamond-shaped indicator representing a keyframe on a property track.
-- | Supports selection, dragging, and context menu operations.
-- |
-- | ## Features
-- |
-- | - Diamond shape (default) or circle (hold keyframe)
-- | - Draggable in time
-- | - Multi-select support (Shift+click)
-- | - Context menu (delete, copy, ease)
-- | - Color based on interpolation type
-- |
-- | ## Visual
-- |
-- | ```
-- |    ◇ Linear (outline diamond)
-- |    ◆ Bezier (filled diamond)
-- |    ● Hold (filled circle)
-- |    ◇ Auto (outline with dot)
-- | ```
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Motion.Timeline.KeyframeMarker as KFMarker
-- |
-- | HH.slot _keyframe keyframeId KFMarker.component
-- |   { keyframeId: kf.id
-- |   , frame: kf.frame
-- |   , interpolationType: kf.interpolation
-- |   , isSelected: Array.elem kf.id selectedKeyframes
-- |   , pixelsPerFrame: 10.0
-- |   }
-- |   HandleKeyframeOutput
-- | ```
module Hydrogen.Component.Motion.Timeline.KeyframeMarker
  ( -- * Component
    component
  
  -- * Types
  , Query(SetSelected, SetFrame, GetFrame)
  , Input
  , Output(Selected, DragStart, Dragging, DragEnd, ContextMenu, DoubleClick)
  , Slot
  
  -- * Slot Type
  , _keyframeMarker
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
import Hydrogen.Schema.Dimension.Temporal (Frames)
import Hydrogen.Schema.Dimension.Temporal (unwrapFrames) as Temporal
import Hydrogen.Schema.Motion.Keyframe (KeyframeId(KeyframeId), InterpolationType(Linear, Bezier, Hold, Auto))
import Hydrogen.UI.Core (cls)
import Type.Proxy (Proxy(Proxy))
import Web.UIEvent.MouseEvent (MouseEvent)
import Web.UIEvent.MouseEvent (shiftKey, button) as MouseEvent

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Component input
type Input =
  { keyframeId :: KeyframeId
  , frame :: Frames
  , interpolationType :: InterpolationType
  , isSelected :: Boolean
  , pixelsPerFrame :: Number
  , scrollOffset :: Number
  }

-- | Component queries
data Query a
  = SetSelected Boolean a
  | SetFrame Frames a
  | GetFrame (Frames -> a)

-- | Component output
data Output
  = Selected KeyframeId Boolean      -- ID, add to selection (shift held)?
  | DragStart KeyframeId
  | Dragging KeyframeId Frames       -- New frame position
  | DragEnd KeyframeId
  | ContextMenu KeyframeId           -- Right-click
  | DoubleClick KeyframeId           -- Open easing editor

-- | Internal state
type State =
  { keyframeId :: KeyframeId
  , frame :: Frames
  , interpolationType :: InterpolationType
  , isSelected :: Boolean
  , pixelsPerFrame :: Number
  , scrollOffset :: Number
  , isDragging :: Boolean
  , isHovered :: Boolean
  }

-- | Internal actions
data Action
  = Receive Input
  | HandleClick MouseEvent
  | HandleDoubleClick MouseEvent
  | HandleMouseDown MouseEvent
  | HandleMouseUp MouseEvent
  | HandleMouseEnter
  | HandleMouseLeave

-- | Slot type helper
type Slot = H.Slot Query Output KeyframeId

-- | Slot proxy
_keyframeMarker :: Proxy "keyframeMarker"
_keyframeMarker = Proxy

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // component
-- ═══════════════════════════════════════════════════════════════════════════════

-- | KeyframeMarker component
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
  { keyframeId: input.keyframeId
  , frame: input.frame
  , interpolationType: input.interpolationType
  , isSelected: input.isSelected
  , pixelsPerFrame: input.pixelsPerFrame
  , scrollOffset: input.scrollOffset
  , isDragging: false
  , isHovered: false
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // render
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Marker size in pixels
markerSize :: Number
markerSize = 12.0

-- | Render the keyframe marker
render :: forall m. State -> H.ComponentHTML Action () m
render state =
  let
    xPos = Temporal.unwrapFrames state.frame * state.pixelsPerFrame - state.scrollOffset
    halfSize = markerSize / 2.0
  in
    HH.div
      [ cls [ "absolute top-1/2 transform -translate-y-1/2 cursor-pointer" ]
      , HP.attr (HH.AttrName "style") 
          ("left: " <> show (xPos - halfSize) <> "px; width: " <> show markerSize <> "px; height: " <> show markerSize <> "px;")
      , HP.attr (HH.AttrName "data-component") "keyframe-marker"
      , HP.attr (HH.AttrName "data-keyframe-id") (unwrapKeyframeId state.keyframeId)
      , HE.onClick HandleClick
      , HE.onDoubleClick HandleDoubleClick
      , HE.onMouseDown HandleMouseDown
      , HE.onMouseUp HandleMouseUp
      -- Context menu handled via onMouseDown with right button check
      , HE.onMouseEnter (\_ -> HandleMouseEnter)
      , HE.onMouseLeave (\_ -> HandleMouseLeave)
      , ARIA.role "button"
      , ARIA.label ("Keyframe at frame " <> show (round $ Temporal.unwrapFrames state.frame))
      ]
      [ renderMarkerShape state ]

-- | Extract string from KeyframeId
unwrapKeyframeId :: KeyframeId -> String
unwrapKeyframeId (KeyframeId id) = id

-- | Render the marker shape based on interpolation type
renderMarkerShape :: forall m. State -> H.ComponentHTML Action () m
renderMarkerShape state =
  case state.interpolationType of
    Hold -> renderCircleMarker state
    _ -> renderDiamondMarker state

-- | Render diamond marker (for Linear, Bezier, Auto)
renderDiamondMarker :: forall m. State -> H.ComponentHTML Action () m
renderDiamondMarker state =
  let
    baseColor = interpolationColor state.interpolationType
    fillColor = 
      if state.interpolationType == Bezier || state.interpolationType == Auto
        then baseColor
        else "transparent"
    strokeColor = baseColor
    
    selectedRing = 
      if state.isSelected
        then "ring-2 ring-primary ring-offset-1"
        else ""
    
    hoverScale =
      if state.isHovered
        then "scale-110"
        else ""
    
    draggingStyle =
      if state.isDragging
        then "opacity-75"
        else ""
  in
    HH.div
      [ cls [ "w-full h-full transform rotate-45 transition-transform duration-100"
            , selectedRing, hoverScale, draggingStyle
            ]
      , HP.attr (HH.AttrName "style")
          ("background-color: " <> fillColor <> "; border: 2px solid " <> strokeColor <> "; border-radius: 2px;")
      ]
      -- Auto interpolation gets a center dot
      (if state.interpolationType == Auto
        then 
          [ HH.div
              [ cls [ "absolute top-1/2 left-1/2 transform -translate-x-1/2 -translate-y-1/2 -rotate-45" ]
              , HP.attr (HH.AttrName "style") "width: 4px; height: 4px; background-color: white; border-radius: 50%;"
              ]
              []
          ]
        else [])

-- | Render circle marker (for Hold)
renderCircleMarker :: forall m. State -> H.ComponentHTML Action () m
renderCircleMarker state =
  let
    baseColor = interpolationColor Hold
    
    selectedRing = 
      if state.isSelected
        then "ring-2 ring-primary ring-offset-1"
        else ""
    
    hoverScale =
      if state.isHovered
        then "scale-110"
        else ""
  in
    HH.div
      [ cls [ "w-full h-full rounded-full transition-transform duration-100"
            , selectedRing, hoverScale
            ]
      , HP.attr (HH.AttrName "style")
          ("background-color: " <> baseColor <> ";")
      ]
      []

-- | Get color for interpolation type
interpolationColor :: InterpolationType -> String
interpolationColor = case _ of
  Linear -> "hsl(var(--primary))"
  Bezier -> "hsl(var(--accent))"
  Hold -> "hsl(var(--destructive))"
  Auto -> "hsl(var(--success, 142 76% 36%))"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // handle action
-- ═══════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Receive input -> do
    H.modify_ \s -> s
      { keyframeId = input.keyframeId
      , frame = input.frame
      , interpolationType = input.interpolationType
      , isSelected = input.isSelected
      , pixelsPerFrame = input.pixelsPerFrame
      , scrollOffset = input.scrollOffset
      }
  
  HandleClick event -> do
    state <- H.get
    let addToSelection = MouseEvent.shiftKey event
    H.raise (Selected state.keyframeId addToSelection)
  
  HandleDoubleClick _ -> do
    state <- H.get
    H.raise (DoubleClick state.keyframeId)
  
  HandleMouseDown event -> do
    state <- H.get
    -- Check for right-click (button 2)
    if MouseEvent.button event == 2
      then H.raise (ContextMenu state.keyframeId)
      else do
        H.modify_ _ { isDragging = true }
        H.raise (DragStart state.keyframeId)
  
  HandleMouseUp _ -> do
    state <- H.get
    when state.isDragging do
      H.modify_ _ { isDragging = false }
      H.raise (DragEnd state.keyframeId)
  
  HandleMouseEnter -> do
    H.modify_ _ { isHovered = true }
  
  HandleMouseLeave -> do
    H.modify_ _ { isHovered = false }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // handle query
-- ═══════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action () Output m (Maybe a)
handleQuery = case _ of
  SetSelected selected reply -> do
    H.modify_ _ { isSelected = selected }
    pure (Just reply)
  
  SetFrame frame' reply -> do
    H.modify_ _ { frame = frame' }
    pure (Just reply)
  
  GetFrame reply -> do
    state <- H.get
    pure (Just (reply state.frame))
