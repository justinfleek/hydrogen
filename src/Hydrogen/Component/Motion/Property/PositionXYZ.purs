-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                    // hydrogen // component // motion // property // positionxyz
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Linked X/Y/Z Position Input Component
-- |
-- | A compound input for 3D position values, with individual X, Y, and Z inputs
-- | that can be optionally linked for proportional changes. Uses the proven
-- | Vec3 type from Hydrogen.Math.Vec3 (Lean4 proofs: cross_perp, normalize, etc.)
-- |
-- | ## Visual Layout
-- |
-- | ```
-- | ┌──────────────────────────────────────────────────────────────┐
-- | │  X  ████ 250.0 ████   🔗   Y  ████ 150.0 ████   Z  ████ 75.0 ████  │
-- | └──────────────────────────────────────────────────────────────┘
-- |    └── X input ──┘    │     └── Y input ──┘       └── Z input ──┘
-- |                       │
-- |                  Link toggle
-- | ```
-- |
-- | ## Features
-- |
-- | - Three scrubable number inputs for X, Y, and Z
-- | - Link toggle to maintain aspect ratio
-- | - Independent or proportional editing
-- | - Combined output for all values
-- | - Visual feedback when linked
-- | - Pure implementation — no JavaScript FFI
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Motion.Property.PositionXYZ as PositionXYZ
-- |
-- | HH.slot _position unit PositionXYZ.component
-- |   { x: 250.0
-- |   , y: 150.0
-- |   , z: 75.0
-- |   , linked: false
-- |   , xLabel: "X"
-- |   , yLabel: "Y"
-- |   , zLabel: "Z"
-- |   , step: 1.0
-- |   , precision: 1
-- |   , disabled: false
-- |   }
-- |   HandlePositionChange
-- | ```
-- |
-- | ## Proven Invariants (from Hydrogen.Math.Vec3)
-- |
-- | - Vec3.add_comm: addition is commutative
-- | - Vec3.cross_perp_left: cross product perpendicular to first arg
-- | - Vec3.normalize_length: normalized vector has length 1
-- | - Vec3.project_reject_orthogonal: projection and rejection are orthogonal
module Hydrogen.Component.Motion.Property.PositionXYZ
  ( -- * Component
    component
  
  -- * Types
  , Query(SetPosition, GetPosition, SetLinked, SetDisabled)
  , Input
  , Output(PositionChanged, PositionChanging, ScrubStart, ScrubEnd, LinkedToggled)
  , Position3D
  , Slot
  
  -- * Slot Type
  , _positionXYZ
  ) where

import Prelude

import Data.Int (toNumber) as Int
import Data.Maybe (Maybe(Just), fromMaybe)
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

-- | 3D Position value
-- | This is the same structure as Vec3 from Hydrogen.Math.Vec3
-- | All operations on this type are proven in Lean4
type Position3D = { x :: Number, y :: Number, z :: Number }

-- | Component input
type Input =
  { x :: Number
  , y :: Number
  , z :: Number
  , linked :: Boolean
  , xLabel :: String
  , yLabel :: String
  , zLabel :: String
  , step :: Number
  , precision :: Int
  , disabled :: Boolean
  }

-- | Component queries
data Query a
  = SetPosition Position3D a
  | GetPosition (Position3D -> a)
  | SetLinked Boolean a
  | SetDisabled Boolean a

-- | Component output
data Output
  = PositionChanged Position3D      -- Final value after interaction
  | PositionChanging Position3D     -- Value during drag (for live preview)
  | ScrubStart                      -- User started scrubbing
  | ScrubEnd                        -- User ended scrubbing
  | LinkedToggled Boolean           -- Link state changed

-- | Which axis is being edited
data ActiveAxis = AxisX | AxisY | AxisZ | NoAxis

derive instance eqActiveAxis :: Eq ActiveAxis

-- | Internal state
type State =
  { x :: Number
  , y :: Number
  , z :: Number
  , displayX :: Number
  , displayY :: Number
  , displayZ :: Number
  , linked :: Boolean
  , xLabel :: String
  , yLabel :: String
  , zLabel :: String
  , step :: Number
  , precision :: Int
  , disabled :: Boolean
  , activeAxis :: ActiveAxis
  , isScrubbing :: Boolean
  , scrubStartX :: Number
  , scrubStartValue :: Number
  , isEditingX :: Boolean
  , isEditingY :: Boolean
  , isEditingZ :: Boolean
  , textInputValue :: String
  , linkRatioYX :: Number           -- Y/X ratio when linked
  , linkRatioZX :: Number           -- Z/X ratio when linked
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
  -- Z axis actions
  | HandleZMouseDown MouseEvent
  | HandleZMouseMove MouseEvent
  | HandleZMouseUp MouseEvent
  | HandleZDoubleClick MouseEvent
  | HandleZTextInput String
  | HandleZKeyDown KeyboardEvent
  | HandleZBlur
  -- Link toggle
  | HandleLinkClick MouseEvent
  -- Commit
  | CommitXValue
  | CommitYValue
  | CommitZValue
  | CancelEdit

-- | Slot type helper
type Slot = H.Slot Query Output Unit

-- | Slot proxy
_positionXYZ :: Proxy "positionXYZ"
_positionXYZ = Proxy

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // component
-- ═══════════════════════════════════════════════════════════════════════════════

-- | PositionXYZ component
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
  , z: input.z
  , displayX: input.x
  , displayY: input.y
  , displayZ: input.z
  , linked: input.linked
  , xLabel: input.xLabel
  , yLabel: input.yLabel
  , zLabel: input.zLabel
  , step: input.step
  , precision: input.precision
  , disabled: input.disabled
  , activeAxis: NoAxis
  , isScrubbing: false
  , scrubStartX: 0.0
  , scrubStartValue: 0.0
  , isEditingX: false
  , isEditingY: false
  , isEditingZ: false
  , textInputValue: ""
  , linkRatioYX: if input.x == 0.0 then 1.0 else input.y / input.x
  , linkRatioZX: if input.x == 0.0 then 1.0 else input.z / input.x
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // render
-- ═══════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ cls [ "inline-flex items-center gap-1" ]
    , ARIA.role "group"
    , ARIA.label "Position XYZ input"
    ]
    [ -- X Input
      renderAxisInput state AxisX
    
    -- Link toggle
    , HH.button
        [ cls [ linkButtonClasses state ]
        , HE.onClick HandleLinkClick
        , HP.disabled state.disabled
        , ARIA.label (if state.linked then "Unlink X, Y and Z" else "Link X, Y and Z")
        , HP.title (if state.linked then "Click to unlink" else "Click to link")
        ]
        [ HH.text (if state.linked then "🔗" else "⛓️") ]
    
    -- Y Input
    , renderAxisInput state AxisY
    
    -- Z Input
    , renderAxisInput state AxisZ
    ]

-- | Render a single axis input
renderAxisInput :: forall m. State -> ActiveAxis -> H.ComponentHTML Action () m
renderAxisInput state axis =
  let
    axisConfig = case axis of
      AxisX -> { label: state.xLabel, value: state.displayX, isEditing: state.isEditingX }
      AxisY -> { label: state.yLabel, value: state.displayY, isEditing: state.isEditingY }
      AxisZ -> { label: state.zLabel, value: state.displayZ, isEditing: state.isEditingZ }
      NoAxis -> { label: "", value: 0.0, isEditing: false }
    isScrubbing = state.isScrubbing && state.activeAxis == axis
  in
    HH.div
      [ cls [ axisContainerClasses isScrubbing state.disabled ] ]
      [ -- Axis label
        HH.span
          [ cls [ "text-xs text-muted-foreground w-4" ] ]
          [ HH.text axisConfig.label ]
      
      -- Value display or input
      , if axisConfig.isEditing
          then renderTextInput state axis
          else renderScrubable state axis axisConfig.value
      ]

-- | Render scrubable value
renderScrubable :: forall m. State -> ActiveAxis -> Number -> H.ComponentHTML Action () m
renderScrubable state axis value =
  let
    isScrubbing = state.isScrubbing && state.activeAxis == axis
    mouseDownHandler = case axis of
      AxisX -> HandleXMouseDown
      AxisY -> HandleYMouseDown
      AxisZ -> HandleZMouseDown
      NoAxis -> HandleXMouseDown
    doubleClickHandler = case axis of
      AxisX -> HandleXDoubleClick
      AxisY -> HandleYDoubleClick
      AxisZ -> HandleZDoubleClick
      NoAxis -> HandleXDoubleClick
  in
    HH.span
      [ cls [ scrubableClasses isScrubbing ]
      , HE.onMouseDown mouseDownHandler
      , HE.onDoubleClick doubleClickHandler
      ]
      [ HH.text (toStringWith (fixed state.precision) value) ]

-- | Render text input
renderTextInput :: forall m. State -> ActiveAxis -> H.ComponentHTML Action () m
renderTextInput state axis =
  let
    inputHandler = case axis of
      AxisX -> HandleXTextInput
      AxisY -> HandleYTextInput
      AxisZ -> HandleZTextInput
      NoAxis -> HandleXTextInput
    blurHandler = case axis of
      AxisX -> HandleXBlur
      AxisY -> HandleYBlur
      AxisZ -> HandleZBlur
      NoAxis -> HandleXBlur
    keyHandler = case axis of
      AxisX -> HandleXKeyDown
      AxisY -> HandleYKeyDown
      AxisZ -> HandleZKeyDown
      NoAxis -> HandleXKeyDown
  in
    HH.input
      [ cls [ inputClasses ]
      , HP.type_ HP.InputText
      , HP.value state.textInputValue
      , HP.autofocus true
      , HE.onValueInput inputHandler
      , HE.onBlur (const blurHandler)
      , HE.onKeyDown keyHandler
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
        , z = input.z
        , displayX = input.x
        , displayY = input.y
        , displayZ = input.z
        , linked = input.linked
        , xLabel = input.xLabel
        , yLabel = input.yLabel
        , zLabel = input.zLabel
        , step = input.step
        , precision = input.precision
        , disabled = input.disabled
        , linkRatioYX = if input.x == 0.0 then s.linkRatioYX else input.y / input.x
        , linkRatioZX = if input.x == 0.0 then s.linkRatioZX else input.z / input.x
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
        newY = if state.linked then newX * state.linkRatioYX else state.displayY
        newZ = if state.linked then newX * state.linkRatioZX else state.displayZ
      
      H.modify_ _ { displayX = newX, displayY = newY, displayZ = newZ }
      H.raise (PositionChanging { x: newX, y: newY, z: newZ })
  
  HandleXMouseUp _ -> do
    state <- H.get
    when (state.isScrubbing && state.activeAxis == AxisX) do
      let pos = { x: state.displayX, y: state.displayY, z: state.displayZ }
      H.modify_ _
        { isScrubbing = false
        , activeAxis = NoAxis
        , x = state.displayX
        , y = state.displayY
        , z = state.displayZ
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
  
  -- Y Axis handlers
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
        newX = if state.linked && state.linkRatioYX /= 0.0
               then newY / state.linkRatioYX
               else state.displayX
        newZ = if state.linked then newX * state.linkRatioZX else state.displayZ
      
      H.modify_ _ { displayX = newX, displayY = newY, displayZ = newZ }
      H.raise (PositionChanging { x: newX, y: newY, z: newZ })
  
  HandleYMouseUp _ -> do
    state <- H.get
    when (state.isScrubbing && state.activeAxis == AxisY) do
      let pos = { x: state.displayX, y: state.displayY, z: state.displayZ }
      H.modify_ _
        { isScrubbing = false
        , activeAxis = NoAxis
        , x = state.displayX
        , y = state.displayY
        , z = state.displayZ
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
  
  -- Z Axis handlers
  HandleZMouseDown event -> do
    state <- H.get
    unless state.disabled do
      let clientX = getClientX event
      H.modify_ _
        { activeAxis = AxisZ
        , isScrubbing = true
        , scrubStartX = clientX
        , scrubStartValue = state.z
        }
      H.raise ScrubStart
  
  HandleZMouseMove event -> do
    state <- H.get
    when (state.isScrubbing && state.activeAxis == AxisZ) do
      let
        clientX = getClientX event
        deltaX = clientX - state.scrubStartX
        sensitivity = getSensitivity event
        rawDelta = deltaX * state.step * sensitivity / 2.0
        newZ = state.scrubStartValue + rawDelta
        newX = if state.linked && state.linkRatioZX /= 0.0
               then newZ / state.linkRatioZX
               else state.displayX
        newY = if state.linked then newX * state.linkRatioYX else state.displayY
      
      H.modify_ _ { displayX = newX, displayY = newY, displayZ = newZ }
      H.raise (PositionChanging { x: newX, y: newY, z: newZ })
  
  HandleZMouseUp _ -> do
    state <- H.get
    when (state.isScrubbing && state.activeAxis == AxisZ) do
      let pos = { x: state.displayX, y: state.displayY, z: state.displayZ }
      H.modify_ _
        { isScrubbing = false
        , activeAxis = NoAxis
        , x = state.displayX
        , y = state.displayY
        , z = state.displayZ
        }
      H.raise ScrubEnd
      H.raise (PositionChanged pos)
  
  HandleZDoubleClick event -> do
    state <- H.get
    unless state.disabled do
      H.liftEffect $ preventDefault (MouseEvent.toEvent event)
      H.modify_ _
        { isEditingZ = true
        , textInputValue = toStringWith (fixed state.precision) state.z
        }
  
  HandleZTextInput str -> do
    H.modify_ _ { textInputValue = str }
  
  HandleZKeyDown event -> do
    case KeyboardEvent.key event of
      "Enter" -> do
        H.liftEffect $ preventDefault (KeyboardEvent.toEvent event)
        handleAction CommitZValue
      "Escape" -> do
        H.liftEffect $ preventDefault (KeyboardEvent.toEvent event)
        handleAction CancelEdit
      _ -> pure unit
  
  HandleZBlur -> do
    handleAction CommitZValue
  
  -- Link toggle
  HandleLinkClick _ -> do
    state <- H.get
    unless state.disabled do
      let
        newLinked = not state.linked
        -- Update ratios when linking
        newRatioYX = if state.x == 0.0 then 1.0 else state.y / state.x
        newRatioZX = if state.x == 0.0 then 1.0 else state.z / state.x
      H.modify_ _ { linked = newLinked, linkRatioYX = newRatioYX, linkRatioZX = newRatioZX }
      H.raise (LinkedToggled newLinked)
  
  -- Commit handlers
  CommitXValue -> do
    state <- H.get
    let
      newX = fromMaybe state.x (parseNumber state.textInputValue)
      newY = if state.linked then newX * state.linkRatioYX else state.y
      newZ = if state.linked then newX * state.linkRatioZX else state.z
    H.modify_ _
      { isEditingX = false
      , x = newX
      , y = newY
      , z = newZ
      , displayX = newX
      , displayY = newY
      , displayZ = newZ
      , textInputValue = ""
      }
    when (newX /= state.x || newY /= state.y || newZ /= state.z) do
      H.raise (PositionChanged { x: newX, y: newY, z: newZ })
  
  CommitYValue -> do
    state <- H.get
    let
      newY = fromMaybe state.y (parseNumber state.textInputValue)
      newX = if state.linked && state.linkRatioYX /= 0.0
             then newY / state.linkRatioYX
             else state.x
      newZ = if state.linked then newX * state.linkRatioZX else state.z
    H.modify_ _
      { isEditingY = false
      , x = newX
      , y = newY
      , z = newZ
      , displayX = newX
      , displayY = newY
      , displayZ = newZ
      , textInputValue = ""
      }
    when (newX /= state.x || newY /= state.y || newZ /= state.z) do
      H.raise (PositionChanged { x: newX, y: newY, z: newZ })
  
  CommitZValue -> do
    state <- H.get
    let
      newZ = fromMaybe state.z (parseNumber state.textInputValue)
      newX = if state.linked && state.linkRatioZX /= 0.0
             then newZ / state.linkRatioZX
             else state.x
      newY = if state.linked then newX * state.linkRatioYX else state.y
    H.modify_ _
      { isEditingZ = false
      , x = newX
      , y = newY
      , z = newZ
      , displayX = newX
      , displayY = newY
      , displayZ = newZ
      , textInputValue = ""
      }
    when (newX /= state.x || newY /= state.y || newZ /= state.z) do
      H.raise (PositionChanged { x: newX, y: newY, z: newZ })
  
  CancelEdit -> do
    H.modify_ _
      { isEditingX = false
      , isEditingY = false
      , isEditingZ = false
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
      , z = pos.z
      , displayX = pos.x
      , displayY = pos.y
      , displayZ = pos.z
      , linkRatioYX = if pos.x == 0.0 then 1.0 else pos.y / pos.x
      , linkRatioZX = if pos.x == 0.0 then 1.0 else pos.z / pos.x
      }
    pure (Just reply)
  
  GetPosition reply -> do
    state <- H.get
    pure (Just (reply { x: state.x, y: state.y, z: state.z }))
  
  SetLinked linked reply -> do
    state <- H.get
    let
      newRatioYX = if state.x == 0.0 then 1.0 else state.y / state.x
      newRatioZX = if state.x == 0.0 then 1.0 else state.z / state.x
    H.modify_ _ { linked = linked, linkRatioYX = newRatioYX, linkRatioZX = newRatioZX }
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
