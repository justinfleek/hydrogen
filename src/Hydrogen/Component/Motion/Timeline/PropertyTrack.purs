-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                   // hydrogen // component // motion // timeline // propertytrack
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Property Track for Animation Timeline
-- |
-- | A collapsible track that displays animated property keyframes within a
-- | layer. Shows as a child row beneath the parent LayerTrack.
-- |
-- | ## Features
-- |
-- | - Property name label
-- | - Keyframe markers along track
-- | - Value preview at current time (optional)
-- | - Expression indicator icon
-- | - Nested property groups (Transform > Position > X)
-- | - Collapse to hide sub-properties
-- |
-- | ## Visual Structure
-- |
-- | ```
-- |  Layer: Shape
-- |    └─ Transform
-- |         ├─ Position     ◆───────◆─────────◆
-- |         │   ├─ X        ◆───────◆
-- |         │   └─ Y        ◆───────◆
-- |         └─ Rotation     ◆───────────────◆
-- | ```
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Motion.Timeline.PropertyTrack as PropTrack
-- |
-- | HH.slot _propertyTrack propertyId PropTrack.component
-- |   { propertyId: prop.id
-- |   , propertyName: prop.name
-- |   , keyframes: prop.keyframes
-- |   , hasExpression: isJust prop.expression
-- |   , depth: 1  -- Nesting level
-- |   , pixelsPerFrame: ppf
-- |   , scrollOffset: scroll
-- |   , currentFrame: playhead
-- |   }
-- |   HandlePropertyTrackOutput
-- | ```
module Hydrogen.Component.Motion.Timeline.PropertyTrack
  ( -- * Component
    component
  
  -- * Types
  , Query(..)
  , Input
  , Output(..)
  , PropertyId(..)
  , Slot
  
  -- * Slot Type
  , _propertyTrack
  ) where

import Prelude

import Data.Array (length, mapWithIndex)
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
import Hydrogen.Schema.Motion.Keyframe (Keyframe, KeyframeId)
import Hydrogen.Schema.Motion.Keyframe (frame, keyframeId) as KF
import Hydrogen.UI.Core (cls)
import Type.Proxy (Proxy(Proxy))
import Web.UIEvent.MouseEvent (MouseEvent)
import Web.UIEvent.MouseEvent (shiftKey) as MouseEvent

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for a property
newtype PropertyId = PropertyId String

derive instance eqPropertyId :: Eq PropertyId
derive instance ordPropertyId :: Ord PropertyId

instance showPropertyId :: Show PropertyId where
  show (PropertyId id) = "Prop:" <> id

-- | Component input
type Input =
  { propertyId :: PropertyId
  , propertyName :: String
  , keyframes :: Array Keyframe
  , hasExpression :: Boolean
  , isExpanded :: Boolean
  , depth :: Int                  -- Nesting level (0 = top level)
  , pixelsPerFrame :: Number
  , scrollOffset :: Number
  , currentFrame :: Frames
  , trackHeight :: Number
  , layerInPoint :: Frames        -- Parent layer's in point
  , layerOutPoint :: Frames       -- Parent layer's out point
  }

-- | Component queries
data Query a
  = SetExpanded Boolean a
  | SetKeyframes (Array Keyframe) a
  | GetKeyframes (Array Keyframe -> a)

-- | Component output
data Output
  = ExpandToggled PropertyId Boolean
  | KeyframeSelected PropertyId KeyframeId Boolean  -- Add to selection?
  | KeyframeDoubleClicked PropertyId KeyframeId     -- Edit keyframe
  | AddKeyframeRequested PropertyId Frames          -- Click on empty track
  | PropertyNameClicked PropertyId                  -- Select property
  | ExpressionClicked PropertyId                    -- Edit expression

-- | Internal state
type State =
  { propertyId :: PropertyId
  , propertyName :: String
  , keyframes :: Array Keyframe
  , hasExpression :: Boolean
  , isExpanded :: Boolean
  , depth :: Int
  , pixelsPerFrame :: Number
  , scrollOffset :: Number
  , currentFrame :: Frames
  , trackHeight :: Number
  , layerInPoint :: Frames
  , layerOutPoint :: Frames
  , isHovered :: Boolean
  }

-- | Internal actions
data Action
  = Receive Input
  | HandleExpandToggle
  | HandleNameClick MouseEvent
  | HandleExpressionClick
  | HandleTrackClick MouseEvent
  | HandleKeyframeClick KeyframeId MouseEvent
  | HandleKeyframeDoubleClick KeyframeId
  | HandleMouseEnter
  | HandleMouseLeave

-- | Slot type helper
type Slot = H.Slot Query Output PropertyId

-- | Slot proxy
_propertyTrack :: Proxy "propertyTrack"
_propertyTrack = Proxy

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // component
-- ═══════════════════════════════════════════════════════════════════════════════

-- | PropertyTrack component
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
  { propertyId: input.propertyId
  , propertyName: input.propertyName
  , keyframes: input.keyframes
  , hasExpression: input.hasExpression
  , isExpanded: input.isExpanded
  , depth: input.depth
  , pixelsPerFrame: input.pixelsPerFrame
  , scrollOffset: input.scrollOffset
  , currentFrame: input.currentFrame
  , trackHeight: input.trackHeight
  , layerInPoint: input.layerInPoint
  , layerOutPoint: input.layerOutPoint
  , isHovered: false
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // render
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Indentation per nesting level
indentPerLevel :: Number
indentPerLevel = 16.0

-- | Keyframe marker size
keyframeSize :: Number
keyframeSize = 10.0

-- | Label column width
labelColumnWidth :: Number
labelColumnWidth = 150.0

-- | Render the property track
render :: forall m. State -> H.ComponentHTML Action () m
render state =
  let
    indent = intToNumber state.depth * indentPerLevel
    
    containerClasses =
      "flex items-center h-full border-b border-border/50 " <>
      (if state.isHovered then "bg-muted/30" else "")
  in
    HH.div
      [ cls [ containerClasses ]
      , HP.attr (HH.AttrName "data-component") "property-track"
      , HP.attr (HH.AttrName "data-property-id") (unwrapPropertyId state.propertyId)
      , HP.attr (HH.AttrName "style") ("height: " <> show state.trackHeight <> "px;")
      , HE.onMouseEnter (\_ -> HandleMouseEnter)
      , HE.onMouseLeave (\_ -> HandleMouseLeave)
      ]
      [ -- Label column (fixed width)
        renderLabelColumn state indent
      -- Keyframe track (flexible)
      , renderKeyframeTrack state
      ]

-- | Extract string from PropertyId
unwrapPropertyId :: PropertyId -> String
unwrapPropertyId (PropertyId id) = id

-- | Convert Int to Number
foreign import intToNumber :: Int -> Number

-- | Render the label column
renderLabelColumn :: forall m. State -> Number -> H.ComponentHTML Action () m
renderLabelColumn state indent =
  let
    hasChildren = length state.keyframes > 0  -- Simplified check
    
    labelClasses =
      "flex items-center gap-1 px-2 text-xs text-muted-foreground " <>
      "hover:text-foreground cursor-pointer select-none"
  in
    HH.div
      [ cls [ "shrink-0 flex items-center border-r border-border/50" ]
      , HP.attr (HH.AttrName "style") ("width: " <> show labelColumnWidth <> "px; padding-left: " <> show indent <> "px;")
      ]
      [ -- Expand toggle (if has children)
        if hasChildren
          then renderExpandToggle state
          else HH.div [ cls [ "w-4" ] ] []  -- Spacer
      -- Property name
      , HH.div
          [ cls [ labelClasses ]
          , HE.onClick HandleNameClick
          ]
          [ HH.text state.propertyName ]
      -- Expression indicator
      , if state.hasExpression
          then renderExpressionIndicator
          else HH.text ""
      ]

-- | Render expand/collapse toggle
renderExpandToggle :: forall m. State -> H.ComponentHTML Action () m
renderExpandToggle state =
  let
    icon = if state.isExpanded then "v" else ">"
  in
    HH.div
      [ cls [ "w-4 h-4 flex items-center justify-center cursor-pointer text-muted-foreground hover:text-foreground" ]
      , HE.onClick (\_ -> HandleExpandToggle)
      , ARIA.role "button"
      , ARIA.label (if state.isExpanded then "Collapse" else "Expand")
      ]
      [ HH.span
          [ cls [ "text-xs font-mono" ] ]
          [ HH.text icon ]
      ]

-- | Render expression indicator (= icon)
renderExpressionIndicator :: forall m. H.ComponentHTML Action () m
renderExpressionIndicator =
  HH.div
    [ cls [ "w-4 h-4 flex items-center justify-center cursor-pointer text-accent hover:text-accent/80" ]
    , HE.onClick (\_ -> HandleExpressionClick)
    , ARIA.label "Edit expression"
    ]
    [ HH.span
        [ cls [ "text-xs font-mono font-bold" ] ]
        [ HH.text "=" ]
    ]

-- | Render the keyframe track area
renderKeyframeTrack :: forall m. State -> H.ComponentHTML Action () m
renderKeyframeTrack state =
  let
    -- Calculate track boundaries based on layer
    trackStartPx = Temporal.unwrapFrames state.layerInPoint * state.pixelsPerFrame - state.scrollOffset
    trackEndPx = Temporal.unwrapFrames state.layerOutPoint * state.pixelsPerFrame - state.scrollOffset
    trackWidth = max 0.0 (trackEndPx - trackStartPx)
    
    trackClasses =
      "flex-1 relative h-full cursor-crosshair"
  in
    HH.div
      [ cls [ trackClasses ]
      , HE.onClick HandleTrackClick
      ]
      [ -- Track background (shows layer extent)
        HH.div
          [ cls [ "absolute top-1 bottom-1 bg-muted/20 rounded-sm" ]
          , HP.attr (HH.AttrName "style") 
              ("left: " <> show trackStartPx <> "px; width: " <> show trackWidth <> "px;")
          ]
          []
      -- Keyframe markers
      , HH.div
          [ cls [ "absolute inset-0" ] ]
          (mapWithIndex (renderKeyframe state) state.keyframes)
      -- Current frame indicator
      , renderCurrentFrameIndicator state
      ]

-- | Render a single keyframe marker
renderKeyframe :: forall m. State -> Int -> Keyframe -> H.ComponentHTML Action () m
renderKeyframe state _index kf =
  let
    kfFrame = KF.frame kf
    kfId = KF.keyframeId kf
    xPos = Temporal.unwrapFrames kfFrame * state.pixelsPerFrame - state.scrollOffset
    halfSize = keyframeSize / 2.0
    
    markerClasses =
      "absolute top-1/2 transform -translate-y-1/2 " <>
      "cursor-pointer transition-transform hover:scale-125"
  in
    HH.div
      [ cls [ markerClasses ]
      , HP.attr (HH.AttrName "style") 
          ("left: " <> show (xPos - halfSize) <> "px; width: " <> show keyframeSize <> "px; height: " <> show keyframeSize <> "px;")
      , HE.onClick (HandleKeyframeClick kfId)
      , HE.onDoubleClick (\_ -> HandleKeyframeDoubleClick kfId)
      , ARIA.role "button"
      , ARIA.label ("Keyframe at frame " <> show (round $ Temporal.unwrapFrames kfFrame))
      ]
      [ -- Diamond shape
        HH.div
          [ cls [ "w-full h-full bg-primary transform rotate-45 rounded-sm" ] ]
          []
      ]

-- | Render current frame indicator on track
renderCurrentFrameIndicator :: forall m. State -> H.ComponentHTML Action () m
renderCurrentFrameIndicator state =
  let
    xPos = Temporal.unwrapFrames state.currentFrame * state.pixelsPerFrame - state.scrollOffset
  in
    HH.div
      [ cls [ "absolute top-0 bottom-0 w-px bg-primary/30 pointer-events-none" ]
      , HP.attr (HH.AttrName "style") ("left: " <> show xPos <> "px;")
      ]
      []

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // handle action
-- ═══════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Receive input -> do
    H.modify_ \s -> s
      { propertyId = input.propertyId
      , propertyName = input.propertyName
      , keyframes = input.keyframes
      , hasExpression = input.hasExpression
      , isExpanded = input.isExpanded
      , depth = input.depth
      , pixelsPerFrame = input.pixelsPerFrame
      , scrollOffset = input.scrollOffset
      , currentFrame = input.currentFrame
      , trackHeight = input.trackHeight
      , layerInPoint = input.layerInPoint
      , layerOutPoint = input.layerOutPoint
      }
  
  HandleExpandToggle -> do
    state <- H.get
    let newExpanded = not state.isExpanded
    H.modify_ _ { isExpanded = newExpanded }
    H.raise (ExpandToggled state.propertyId newExpanded)
  
  HandleNameClick _ -> do
    state <- H.get
    H.raise (PropertyNameClicked state.propertyId)
  
  HandleExpressionClick -> do
    state <- H.get
    H.raise (ExpressionClicked state.propertyId)
  
  HandleTrackClick _event -> do
    -- Calculating exact frame from click position requires FFI to get
    -- clientX and element bounds. The parent component (AnimationTimeline)
    -- handles this via its own mouse handling and coordinate system.
    -- 
    -- This handler exists for future direct track click handling.
    -- Currently, keyframe creation is triggered via the parent.
    pure unit
  
  HandleKeyframeClick kfId event -> do
    state <- H.get
    let addToSelection = MouseEvent.shiftKey event
    H.raise (KeyframeSelected state.propertyId kfId addToSelection)
  
  HandleKeyframeDoubleClick kfId -> do
    state <- H.get
    H.raise (KeyframeDoubleClicked state.propertyId kfId)
  
  HandleMouseEnter -> do
    H.modify_ _ { isHovered = true }
  
  HandleMouseLeave -> do
    H.modify_ _ { isHovered = false }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // handle query
-- ═══════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action () Output m (Maybe a)
handleQuery = case _ of
  SetExpanded expanded reply -> do
    H.modify_ _ { isExpanded = expanded }
    pure (Just reply)
  
  SetKeyframes kfs reply -> do
    H.modify_ _ { keyframes = kfs }
    pure (Just reply)
  
  GetKeyframes reply -> do
    state <- H.get
    pure (Just (reply state.keyframes))
