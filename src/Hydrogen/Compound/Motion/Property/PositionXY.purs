-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                     // hydrogen // component // motion // property // positionxy
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Linked X/Y Position Input Component
-- |
-- | A compound input for 2D position values, with individual X and Y inputs
-- | that can be optionally linked for proportional changes.
-- |
-- | ## Visual Layout
-- |
-- | ```
-- | ┌───────────────────────────────────────┐
-- | │  X  ████ 250.0 ████   🔗   Y  ████ 150.0 ████  │
-- | └───────────────────────────────────────┘
-- |    └── X input ──┘    │     └── Y input ──┘
-- |                       │
-- |                  Link toggle
-- | ```
-- |
-- | ## Features
-- |
-- | - Two scrubable number inputs for X and Y
-- | - Link toggle to maintain aspect ratio
-- | - Independent or proportional editing
-- | - Combined output for both values
-- | - Visual feedback when linked
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Motion.Property.PositionXY as PositionXY
-- |
-- | HH.slot _position unit PositionXY.component
-- |   { x: 250.0
-- |   , y: 150.0
-- |   , linked: false
-- |   , xLabel: "X"
-- |   , yLabel: "Y"
-- |   , step: 1.0
-- |   , precision: 1
-- |   , disabled: false
-- |   }
-- |   HandlePositionChange
-- | ```
module Hydrogen.Component.Motion.Property.PositionXY
  ( -- * Component
    component
  
  -- * Types
  , Query(SetPosition, GetPosition, SetLinked, SetDisabled)
  , Input
  , Output(PositionChanged, PositionChanging, ScrubStart, ScrubEnd, LinkedToggled)
  , Position
  , Slot
  
  -- * Slot Type
  , _positionXY
  ) where

import Prelude

import Data.Int (toNumber) as Int
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Data.Number (fromString) as Number
import Data.Number.Format (fixed, toStringWith)
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)
import Type.Proxy (Proxy(Proxy))
import Web.Event.Event (preventDefault)
import Web.UIEvent.KeyboardEvent (KeyboardEvent)
import Web.UIEvent.KeyboardEvent (key, toEvent) as KeyboardEvent
import Web.UIEvent.MouseEvent (MouseEvent)
import Web.UIEvent.MouseEvent (clientX, toEvent, shiftKey, ctrlKey, metaKey) as MouseEvent

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Extract clientX from a mouse event (pure implementation)
-- | Uses Web.UIEvent.MouseEvent.clientX which returns Int, converted to Number
getClientX :: MouseEvent -> Number
getClientX = Int.toNumber <<< MouseEvent.clientX

-- | Parse a string to a Number safely
-- | Pure implementation using Data.Number.fromString
parseNumber :: String -> Maybe Number
parseNumber = Number.fromString

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | 2D Position value
type Position = { x :: Number, y :: Number }

-- | Component input
type Input =
  { x :: Number
  , y :: Number
  , linked :: Boolean
  , xLabel :: String
  , yLabel :: String
  , step :: Number
  , precision :: Int
  , disabled :: Boolean
  }

-- | Component queries
data Query a
  = SetPosition Position a
  | GetPosition (Position -> a)
  | SetLinked Boolean a
  | SetDisabled Boolean a

-- | Component output
data Output
  = PositionChanged Position        -- Final value after interaction
  | PositionChanging Position       -- Value during drag (for live preview)
  | ScrubStart                      -- User started scrubbing
  | ScrubEnd                        -- User ended scrubbing
  | LinkedToggled Boolean           -- Link state changed

-- | Which axis is being edited
data ActiveAxis = AxisX | AxisY | NoAxis

derive instance eqActiveAxis :: Eq ActiveAxis

-- | Internal state
type State =
  { x :: Number
  , y :: Number
  , displayX :: Number
  , displayY :: Number
  , linked :: Boolean
  , xLabel :: String
  , yLabel :: String
  , step :: Number
  , precision :: Int
  , disabled :: Boolean
  , activeAxis :: ActiveAxis
  , isScrubbing :: Boolean
  , scrubStartX :: Number
  , scrubStartValue :: Number
  , isEditingX :: Boolean
  , isEditingY :: Boolean
  , textInputValue :: String
  , linkRatio :: Number           -- Y/X ratio when linked
  }

-- | Internal actions
data Action
  = Initialize
  | Receive Input
  -- X axis actions
  | HandleXMouseDown MouseEvent
  | HandleXMouseMove MouseEvent
  | HandleXMouseUp MouseEvent
  | HandleXDoubleClick MouseEvent
  | HandleXTextInput String
  | HandleXKeyDown KeyboardEvent
  | HandleXBlur
  -- Y axis actions
  | HandleYMouseDown MouseEvent
  | HandleYMouseMove MouseEvent
  | HandleYMouseUp MouseEvent
  | HandleYDoubleClick MouseEvent
  | HandleYTextInput String
  | HandleYKeyDown KeyboardEvent
  | HandleYBlur
  -- Link toggle
  | HandleLinkClick MouseEvent
  -- Commit
  | CommitXValue
  | CommitYValue
  | CancelEdit

-- | Slot type helper
type Slot = H.Slot Query Output Unit

-- | Slot proxy
_positionXY :: Proxy "positionXY"
_positionXY = Proxy

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // component
-- ═══════════════════════════════════════════════════════════════════════════════

-- | PositionXY component
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
  { x: input.x
  , y: input.y
  , displayX: input.x
  , displayY: input.y
  , linked: input.linked
  , xLabel: input.xLabel
  , yLabel: input.yLabel
  , step: input.step
  , precision: input.precision
  , disabled: input.disabled
  , activeAxis: NoAxis
  , isScrubbing: false
  , scrubStartX: 0.0
  , scrubStartValue: 0.0
  , isEditingX: false
  , isEditingY: false
  , textInputValue: ""
  , linkRatio: if input.x == 0.0 then 1.0 else input.y / input.x
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // render
-- ═══════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ cls [ "inline-flex items-center gap-1" ]
    , ARIA.role "group"
    , ARIA.label "Position XY input"
    ]
    [ -- X Input
      renderAxisInput state AxisX
    
    -- Link toggle
    , HH.button
        [ cls [ linkButtonClasses state ]
        , HE.onClick HandleLinkClick
        , HP.disabled state.disabled
        , ARIA.label (if state.linked then "Unlink X and Y" else "Link X and Y")
        , HP.title (if state.linked then "Click to unlink" else "Click to link")
        ]
        [ HH.text (if state.linked then "🔗" else "⛓️") ]
    
    -- Y Input
    , renderAxisInput state AxisY
    ]

-- | Render a single axis input
renderAxisInput :: forall m. State -> ActiveAxis -> H.ComponentHTML Action () m
renderAxisInput state axis =
  let
    isX = axis == AxisX
    label = if isX then state.xLabel else state.yLabel
    value = if isX then state.displayX else state.displayY
    isEditing = if isX then state.isEditingX else state.isEditingY
    isScrubbing = state.isScrubbing && state.activeAxis == axis
  in
    HH.div
      [ cls [ axisContainerClasses isScrubbing state.disabled ] ]
      [ -- Axis label
        HH.span
          [ cls [ "text-xs text-muted-foreground w-4" ] ]
          [ HH.text label ]
      
      -- Value display or input
      , if isEditing
          then renderTextInput state isX
          else renderScrubable state axis value
      ]

-- | Render scrubable value
renderScrubable :: forall m. State -> ActiveAxis -> Number -> H.ComponentHTML Action () m
renderScrubable state axis value =
  let
    isX = axis == AxisX
    isScrubbing = state.isScrubbing && state.activeAxis == axis
  in
    HH.span
      [ cls [ scrubableClasses isScrubbing ]
      , if isX
          then HE.onMouseDown HandleXMouseDown
          else HE.onMouseDown HandleYMouseDown
      , if isX
          then HE.onDoubleClick HandleXDoubleClick
          else HE.onDoubleClick HandleYDoubleClick
      ]
      [ HH.text (toStringWith (fixed state.precision) value) ]

-- | Render text input
renderTextInput :: forall m. State -> Boolean -> H.ComponentHTML Action () m
renderTextInput state isX =
  HH.input
    [ cls [ inputClasses ]
    , HP.type_ HP.InputText
    , HP.value state.textInputValue
    , HP.autofocus true
    , if isX
        then HE.onValueInput HandleXTextInput
        else HE.onValueInput HandleYTextInput
    , if isX
        then HE.onBlur (const HandleXBlur)
        else HE.onBlur (const HandleYBlur)
    , if isX
        then HE.onKeyDown HandleXKeyDown
        else HE.onKeyDown HandleYKeyDown
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // styles
-- ═══════════════════════════════════════════════════════════════════════════════

axisContainerClasses :: Boolean -> Boolean -> String
axisContainerClasses isScrubbing disabled =
  "inline-flex items-center gap-0.5 px-1.5 py-0.5 rounded text-sm font-mono " <>
  if disabled
    then "opacity-50"
    else if isScrubbing
      then "bg-primary/20"
      else "hover:bg-accent"

scrubableClasses :: Boolean -> String
scrubableClasses isScrubbing =
  "cursor-ew-resize select-none " <>
  if isScrubbing
    then "text-primary font-medium"
    else "text-foreground"

linkButtonClasses :: State -> String
linkButtonClasses state =
  "w-6 h-6 flex items-center justify-center rounded text-sm " <>
  "transition-colors duration-75 " <>
  if state.disabled
    then "opacity-50 cursor-not-allowed"
    else if state.linked
      then "bg-primary/20 text-primary hover:bg-primary/30"
      else "text-muted-foreground hover:text-foreground hover:bg-accent"

inputClasses :: String
inputClasses =
  "w-14 px-1 py-0 rounded text-sm font-mono " <>
  "bg-background border border-input focus:outline-none focus:ring-1 focus:ring-ring"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // handle action
-- ═══════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    pure unit
  
  Receive input -> do
    state <- H.get
    unless state.isScrubbing do
      H.modify_ \s -> s
        { x = input.x
        , y = input.y
        , displayX = input.x
        , displayY = input.y
        , linked = input.linked
        , xLabel = input.xLabel
        , yLabel = input.yLabel
        , step = input.step
        , precision = input.precision
        , disabled = input.disabled
        , linkRatio = if input.x == 0.0 then s.linkRatio else input.y / input.x
        }
  
  -- X Axis handlers
  HandleXMouseDown event -> do
    state <- H.get
    unless state.disabled do
      let clientX = getClientX event
      H.modify_ _
        { activeAxis = AxisX
        , isScrubbing = true
        , scrubStartX = clientX
        , scrubStartValue = state.x
        }
      H.raise ScrubStart
  
  HandleXMouseMove event -> do
    state <- H.get
    when (state.isScrubbing && state.activeAxis == AxisX) do
      let
        clientX = getClientX event
        deltaX = clientX - state.scrubStartX
        sensitivity = getSensitivity event
        rawDelta = deltaX * state.step * sensitivity / 2.0
        newX = state.scrubStartValue + rawDelta
        newY = if state.linked then newX * state.linkRatio else state.displayY
      
      H.modify_ _ { displayX = newX, displayY = newY }
      H.raise (PositionChanging { x: newX, y: newY })
  
  HandleXMouseUp _ -> do
    state <- H.get
    when (state.isScrubbing && state.activeAxis == AxisX) do
      let pos = { x: state.displayX, y: state.displayY }
      H.modify_ _
        { isScrubbing = false
        , activeAxis = NoAxis
        , x = state.displayX
        , y = state.displayY
        }
      H.raise ScrubEnd
      H.raise (PositionChanged pos)
  
  HandleXDoubleClick event -> do
    state <- H.get
    unless state.disabled do
      H.liftEffect $ preventDefault (MouseEvent.toEvent event)
      H.modify_ _
        { isEditingX = true
        , textInputValue = toStringWith (fixed state.precision) state.x
        }
  
  HandleXTextInput str -> do
    H.modify_ _ { textInputValue = str }
  
  HandleXKeyDown event -> do
    case KeyboardEvent.key event of
      "Enter" -> do
        H.liftEffect $ preventDefault (KeyboardEvent.toEvent event)
        handleAction CommitXValue
      "Escape" -> do
        H.liftEffect $ preventDefault (KeyboardEvent.toEvent event)
        handleAction CancelEdit
      _ -> pure unit
  
  HandleXBlur -> do
    handleAction CommitXValue
  
  -- Y Axis handlers (mirror of X)
  HandleYMouseDown event -> do
    state <- H.get
    unless state.disabled do
      let clientX = getClientX event
      H.modify_ _
        { activeAxis = AxisY
        , isScrubbing = true
        , scrubStartX = clientX
        , scrubStartValue = state.y
        }
      H.raise ScrubStart
  
  HandleYMouseMove event -> do
    state <- H.get
    when (state.isScrubbing && state.activeAxis == AxisY) do
      let
        clientX = getClientX event
        deltaX = clientX - state.scrubStartX
        sensitivity = getSensitivity event
        rawDelta = deltaX * state.step * sensitivity / 2.0
        newY = state.scrubStartValue + rawDelta
        newX = if state.linked && state.linkRatio /= 0.0
               then newY / state.linkRatio
               else state.displayX
      
      H.modify_ _ { displayX = newX, displayY = newY }
      H.raise (PositionChanging { x: newX, y: newY })
  
  HandleYMouseUp _ -> do
    state <- H.get
    when (state.isScrubbing && state.activeAxis == AxisY) do
      let pos = { x: state.displayX, y: state.displayY }
      H.modify_ _
        { isScrubbing = false
        , activeAxis = NoAxis
        , x = state.displayX
        , y = state.displayY
        }
      H.raise ScrubEnd
      H.raise (PositionChanged pos)
  
  HandleYDoubleClick event -> do
    state <- H.get
    unless state.disabled do
      H.liftEffect $ preventDefault (MouseEvent.toEvent event)
      H.modify_ _
        { isEditingY = true
        , textInputValue = toStringWith (fixed state.precision) state.y
        }
  
  HandleYTextInput str -> do
    H.modify_ _ { textInputValue = str }
  
  HandleYKeyDown event -> do
    case KeyboardEvent.key event of
      "Enter" -> do
        H.liftEffect $ preventDefault (KeyboardEvent.toEvent event)
        handleAction CommitYValue
      "Escape" -> do
        H.liftEffect $ preventDefault (KeyboardEvent.toEvent event)
        handleAction CancelEdit
      _ -> pure unit
  
  HandleYBlur -> do
    handleAction CommitYValue
  
  -- Link toggle
  HandleLinkClick _ -> do
    state <- H.get
    unless state.disabled do
      let
        newLinked = not state.linked
        -- Update ratio when linking
        newRatio = if state.x == 0.0 then 1.0 else state.y / state.x
      H.modify_ _ { linked = newLinked, linkRatio = newRatio }
      H.raise (LinkedToggled newLinked)
  
  -- Commit handlers
  CommitXValue -> do
    state <- H.get
    let
      newX = fromMaybe state.x (parseNumber state.textInputValue)
      newY = if state.linked then newX * state.linkRatio else state.y
    H.modify_ _
      { isEditingX = false
      , x = newX
      , y = newY
      , displayX = newX
      , displayY = newY
      , textInputValue = ""
      }
    when (newX /= state.x || newY /= state.y) do
      H.raise (PositionChanged { x: newX, y: newY })
  
  CommitYValue -> do
    state <- H.get
    let
      newY = fromMaybe state.y (parseNumber state.textInputValue)
      newX = if state.linked && state.linkRatio /= 0.0
             then newY / state.linkRatio
             else state.x
    H.modify_ _
      { isEditingY = false
      , x = newX
      , y = newY
      , displayX = newX
      , displayY = newY
      , textInputValue = ""
      }
    when (newX /= state.x || newY /= state.y) do
      H.raise (PositionChanged { x: newX, y: newY })
  
  CancelEdit -> do
    H.modify_ _
      { isEditingX = false
      , isEditingY = false
      , textInputValue = ""
      }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // handle query
-- ═══════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action () Output m (Maybe a)
handleQuery = case _ of
  SetPosition pos reply -> do
    H.modify_ _
      { x = pos.x
      , y = pos.y
      , displayX = pos.x
      , displayY = pos.y
      , linkRatio = if pos.x == 0.0 then 1.0 else pos.y / pos.x
      }
    pure (Just reply)
  
  GetPosition reply -> do
    state <- H.get
    pure (Just (reply { x: state.x, y: state.y }))
  
  SetLinked linked reply -> do
    state <- H.get
    let newRatio = if state.x == 0.0 then 1.0 else state.y / state.x
    H.modify_ _ { linked = linked, linkRatio = newRatio }
    pure (Just reply)
  
  SetDisabled disabled reply -> do
    H.modify_ _ { disabled = disabled }
    pure (Just reply)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get sensitivity based on modifier keys
getSensitivity :: MouseEvent -> Number
getSensitivity event
  | MouseEvent.shiftKey event = 0.1   -- Fine control
  | MouseEvent.ctrlKey event = 10.0   -- Coarse control
  | MouseEvent.metaKey event = 10.0   -- Coarse control (Mac)
  | otherwise = 1.0                    -- Normal
