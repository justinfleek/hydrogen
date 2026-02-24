-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                      // hydrogen // component // motion // property // angledial
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Circular Angle Dial Component
-- |
-- | A visual angle input control with a circular dial display. Common in
-- | motion graphics for rotation, direction, and other angle-based properties.
-- |
-- | ## Visual
-- |
-- | ```
-- |      ┌───────┐
-- |      │  ╱    │
-- |      │ ◯────│ ← Indicator line shows angle
-- |      │       │
-- |      └───────┘  45.0°
-- | ```
-- |
-- | ## Features
-- |
-- | - Circular dial with angle indicator
-- | - Drag to rotate (360° continuous)
-- | - Shift+drag for 15° snap increments
-- | - Double-click for direct text input
-- | - Supports multiple revolutions (>360°)
-- | - Numeric display with degree suffix
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Motion.Property.AngleDial as AngleDial
-- |
-- | HH.slot _rotation unit AngleDial.component
-- |   { value: 45.0
-- |   , min: Nothing      -- Unbounded (can rotate freely)
-- |   , max: Nothing
-- |   , disabled: false
-- |   }
-- |   HandleAngleChange
-- | ```
module Hydrogen.Component.Motion.Property.AngleDial
  ( -- * Component
    component
  
  -- * Types
  , Query(..)
  , Input
  , Output(..)
  , Slot
  
  -- * Slot Type
  , _angleDial
  ) where

import Prelude

import Data.Int (toNumber) as Int
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Data.Number (pi)
import Data.Number (fromString) as Number
import Data.Number.Format (fixed, toStringWith)
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.Math.Core as Math
import Hydrogen.UI.Core (cls)
import Type.Proxy (Proxy(Proxy))
import Web.Event.Event (preventDefault)
import Web.UIEvent.KeyboardEvent (KeyboardEvent)
import Web.UIEvent.KeyboardEvent (key, toEvent) as KeyboardEvent
import Web.UIEvent.MouseEvent (MouseEvent)
import Web.UIEvent.MouseEvent (clientX, clientY, toEvent, shiftKey) as MouseEvent

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Extract clientX from a mouse event (pure implementation)
getClientX :: MouseEvent -> Number
getClientX = Int.toNumber <<< MouseEvent.clientX

-- | Extract clientY from a mouse event (pure implementation)
getClientY :: MouseEvent -> Number
getClientY = Int.toNumber <<< MouseEvent.clientY

-- | Parse a string to a Number safely (pure implementation)
parseNumber :: String -> Maybe Number
parseNumber = Number.fromString

-- | Get element center X position
-- | Uses getBoundingClientRect which requires FFI
foreign import getElementCenterX :: MouseEvent -> Number

-- | Get element center Y position
-- | Uses getBoundingClientRect which requires FFI
foreign import getElementCenterY :: MouseEvent -> Number

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Component input
type Input =
  { value :: Number            -- Angle in degrees
  , min :: Maybe Number        -- Optional minimum bound
  , max :: Maybe Number        -- Optional maximum bound
  , disabled :: Boolean
  }

-- | Component queries
data Query a
  = SetValue Number a
  | GetValue (Number -> a)
  | SetBounds (Maybe Number) (Maybe Number) a

-- | Component output
data Output
  = ValueChanged Number        -- Final value after interaction
  | ValueChanging Number       -- Value during drag (for live preview)
  | DragStart                  -- User started dragging
  | DragEnd                    -- User ended dragging

-- | Internal state
type State =
  { value :: Number
  , displayValue :: Number
  , min :: Maybe Number
  , max :: Maybe Number
  , disabled :: Boolean
  , isDragging :: Boolean
  , isEditing :: Boolean
  , dragStartAngle :: Number
  , dragStartValue :: Number
  , textInputValue :: String
  , isHovered :: Boolean
  }

-- | Internal actions
data Action
  = Initialize
  | Receive Input
  | HandleMouseDown MouseEvent
  | HandleMouseMove MouseEvent
  | HandleMouseUp MouseEvent
  | HandleDoubleClick MouseEvent
  | HandleMouseEnter
  | HandleMouseLeave
  | HandleKeyDown KeyboardEvent
  | HandleTextInput String
  | HandleBlur
  | CommitTextValue
  | CancelEdit

-- | Slot type helper
type Slot = H.Slot Query Output Unit

-- | Slot proxy
_angleDial :: Proxy "angleDial"
_angleDial = Proxy

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // component
-- ═══════════════════════════════════════════════════════════════════════════════

-- | AngleDial component
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
  { value: input.value
  , displayValue: input.value
  , min: input.min
  , max: input.max
  , disabled: input.disabled
  , isDragging: false
  , isEditing: false
  , dragStartAngle: 0.0
  , dragStartValue: 0.0
  , textInputValue: ""
  , isHovered: false
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // render
-- ═══════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state
  | state.isEditing = renderTextInput state
  | otherwise = renderDial state

-- | Render the dial display
renderDial :: forall m. State -> H.ComponentHTML Action () m
renderDial state =
  HH.div
    [ cls [ containerClasses state ]
    , HE.onMouseDown HandleMouseDown
    , HE.onDoubleClick HandleDoubleClick
    , HE.onMouseEnter (const HandleMouseEnter)
    , HE.onMouseLeave (const HandleMouseLeave)
    , ARIA.role "slider"
    , ARIA.valueNow (show state.displayValue)
    , ARIA.valueMin (show (fromMaybe (-360.0) state.min))
    , ARIA.valueMax (show (fromMaybe 360.0 state.max))
    , HP.tabIndex 0
    ]
    [ -- Circular dial
      renderCircularDial state
    
    -- Numeric value
    , HH.span
        [ cls [ "ml-1 text-sm font-mono" ] ]
        [ HH.text (formatAngle state.displayValue <> "°") ]
    ]

-- | Render the circular dial SVG
renderCircularDial :: forall m. State -> H.ComponentHTML Action () m
renderCircularDial state =
  let
    -- Normalize angle to 0-360 for visual display
    normalizedAngle = normalizeAngle state.displayValue
    -- Convert to radians, offset by -90° so 0° points up
    radians = (normalizedAngle - 90.0) * pi / 180.0
    -- Calculate indicator endpoint
    radius = 8.0
    centerX = 12.0
    centerY = 12.0
    endX = centerX + radius * Math.cos radians
    endY = centerY + radius * Math.sin radians
  in
    HH.element (HH.ElemName "svg")
      [ HP.attr (HH.AttrName "width") "24"
      , HP.attr (HH.AttrName "height") "24"
      , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
      , cls [ dialClasses state ]
      ]
      [ -- Outer circle
        HH.element (HH.ElemName "circle")
          [ HP.attr (HH.AttrName "cx") "12"
          , HP.attr (HH.AttrName "cy") "12"
          , HP.attr (HH.AttrName "r") "10"
          , HP.attr (HH.AttrName "fill") "none"
          , HP.attr (HH.AttrName "stroke") "currentColor"
          , HP.attr (HH.AttrName "stroke-width") "1.5"
          , cls [ "text-border" ]
          ]
          []
      
      -- Center dot
      , HH.element (HH.ElemName "circle")
          [ HP.attr (HH.AttrName "cx") "12"
          , HP.attr (HH.AttrName "cy") "12"
          , HP.attr (HH.AttrName "r") "2"
          , HP.attr (HH.AttrName "fill") "currentColor"
          , cls [ indicatorColorClass state ]
          ]
          []
      
      -- Angle indicator line
      , HH.element (HH.ElemName "line")
          [ HP.attr (HH.AttrName "x1") (show centerX)
          , HP.attr (HH.AttrName "y1") (show centerY)
          , HP.attr (HH.AttrName "x2") (show endX)
          , HP.attr (HH.AttrName "y2") (show endY)
          , HP.attr (HH.AttrName "stroke") "currentColor"
          , HP.attr (HH.AttrName "stroke-width") "2"
          , HP.attr (HH.AttrName "stroke-linecap") "round"
          , cls [ indicatorColorClass state ]
          ]
          []
      ]

-- | Render text input mode
renderTextInput :: forall m. State -> H.ComponentHTML Action () m
renderTextInput state =
  HH.input
    [ cls [ inputClasses ]
    , HP.type_ HP.InputText
    , HP.value state.textInputValue
    , HP.autofocus true
    , HE.onValueInput HandleTextInput
    , HE.onBlur (const HandleBlur)
    , HE.onKeyDown HandleKeyDown
    , ARIA.label "Enter angle in degrees"
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // styles
-- ═══════════════════════════════════════════════════════════════════════════════

containerClasses :: State -> String
containerClasses state =
  "inline-flex items-center px-1 py-0.5 rounded " <>
  "select-none transition-colors duration-75 " <>
  if state.disabled
    then "opacity-50 cursor-not-allowed"
    else if state.isDragging
      then "bg-primary/20 cursor-grabbing"
      else "hover:bg-accent cursor-grab"

dialClasses :: State -> String
dialClasses state =
  "flex-shrink-0 " <>
  if state.isDragging
    then "text-primary"
    else "text-foreground"

indicatorColorClass :: State -> String
indicatorColorClass state =
  if state.isDragging
    then "text-primary"
    else "text-foreground"

inputClasses :: String
inputClasses =
  "w-16 px-1.5 py-0.5 rounded text-sm font-mono " <>
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
    unless state.isDragging do
      H.modify_ \s -> s
        { value = input.value
        , displayValue = input.value
        , min = input.min
        , max = input.max
        , disabled = input.disabled
        }
  
  HandleMouseDown event -> do
    state <- H.get
    unless state.disabled do
      let
        centerX = getElementCenterX event
        centerY = getElementCenterY event
        clientX = getClientX event
        clientY = getClientY event
        startAngle = Math.atan2 (clientY - centerY) (clientX - centerX) * 180.0 / pi
      
      H.modify_ _
        { isDragging = true
        , dragStartAngle = startAngle
        , dragStartValue = state.value
        }
      H.raise DragStart
  
  HandleMouseMove event -> do
    state <- H.get
    when state.isDragging do
      let
        centerX = getElementCenterX event
        centerY = getElementCenterY event
        clientX = getClientX event
        clientY = getClientY event
        currentAngle = Math.atan2 (clientY - centerY) (clientX - centerX) * 180.0 / pi
        deltaAngle = currentAngle - state.dragStartAngle
        
        -- Snap to 15° increments when shift is held
        snappedDelta = 
          if MouseEvent.shiftKey event
            then snapTo15 deltaAngle
            else deltaAngle
        
        newValue = clampValue state (state.dragStartValue + snappedDelta)
      
      H.modify_ _ { displayValue = newValue }
      H.raise (ValueChanging newValue)
  
  HandleMouseUp _ -> do
    state <- H.get
    when state.isDragging do
      let finalValue = state.displayValue
      H.modify_ _
        { isDragging = false
        , value = finalValue
        }
      H.raise DragEnd
      H.raise (ValueChanged finalValue)
  
  HandleDoubleClick event -> do
    state <- H.get
    unless state.disabled do
      H.liftEffect $ preventDefault (MouseEvent.toEvent event)
      H.modify_ _
        { isEditing = true
        , textInputValue = formatAngle state.value
        }
  
  HandleMouseEnter -> do
    H.modify_ _ { isHovered = true }
  
  HandleMouseLeave -> do
    H.modify_ _ { isHovered = false }
  
  HandleKeyDown event -> do
    case KeyboardEvent.key event of
      "Enter" -> do
        H.liftEffect $ preventDefault (KeyboardEvent.toEvent event)
        handleAction CommitTextValue
      "Escape" -> do
        H.liftEffect $ preventDefault (KeyboardEvent.toEvent event)
        handleAction CancelEdit
      _ -> pure unit
  
  HandleTextInput str -> do
    H.modify_ _ { textInputValue = str }
  
  HandleBlur -> do
    handleAction CommitTextValue
  
  CommitTextValue -> do
    state <- H.get
    let
      newValue = case parseNumber state.textInputValue of
        Just parsed -> clampValue state parsed
        Nothing -> state.value
    H.modify_ _
      { isEditing = false
      , value = newValue
      , displayValue = newValue
      , textInputValue = ""
      }
    when (newValue /= state.value) do
      H.raise (ValueChanged newValue)
  
  CancelEdit -> do
    H.modify_ _
      { isEditing = false
      , textInputValue = ""
      }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // handle query
-- ═══════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action () Output m (Maybe a)
handleQuery = case _ of
  SetValue val reply -> do
    state <- H.get
    let clamped = clampValue state val
    H.modify_ _ { value = clamped, displayValue = clamped }
    pure (Just reply)
  
  GetValue reply -> do
    state <- H.get
    pure (Just (reply state.value))
  
  SetBounds newMin newMax reply -> do
    H.modify_ _ { min = newMin, max = newMax }
    state <- H.get
    let clamped = clampValue state state.value
    H.modify_ _ { value = clamped, displayValue = clamped }
    pure (Just reply)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Clamp value to bounds
clampValue :: State -> Number -> Number
clampValue state val =
  let
    withMin = case state.min of
      Just m -> max m val
      Nothing -> val
    withMax = case state.max of
      Just m -> min m withMin
      Nothing -> withMin
  in
    withMax

-- | Normalize angle to 0-360 range
normalizeAngle :: Number -> Number
normalizeAngle angle =
  let
    modAngle = angle - (Math.floor (angle / 360.0) * 360.0)
  in
    if modAngle < 0.0 then modAngle + 360.0 else modAngle

-- | Snap angle to nearest 15° increment
snapTo15 :: Number -> Number
snapTo15 angle =
  let
    snapped = Math.round (angle / 15.0) * 15.0
  in
    snapped

-- | Format angle for display
formatAngle :: Number -> String
formatAngle angle = toStringWith (fixed 1) angle
