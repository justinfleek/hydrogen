-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                  // hydrogen // component // motion // property // scrubablenumber
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Drag-to-Scrub Numeric Input
-- |
-- | An After Effects style numeric input where clicking and dragging
-- | horizontally adjusts the value. Essential for precise control in
-- | motion graphics workflows.
-- |
-- | ## Features
-- |
-- | - Click and drag horizontally to scrub value
-- | - Double-click to enter direct text input mode
-- | - Shift+drag for fine adjustment (0.1x sensitivity)
-- | - Ctrl/Cmd+drag for coarse adjustment (10x sensitivity)
-- | - Configurable min/max bounds
-- | - Configurable step size
-- | - Visual feedback during scrubbing
-- | - Cursor changes to ew-resize during drag
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Motion.Property.ScrubableNumber as ScrubableNumber
-- |
-- | HH.slot _opacity unit ScrubableNumber.component
-- |   { value: 75.0
-- |   , min: Just 0.0
-- |   , max: Just 100.0
-- |   , step: 1.0
-- |   , precision: 1
-- |   , suffix: Just "%"
-- |   , disabled: false
-- |   }
-- |   HandleOpacityChange
-- | ```
module Hydrogen.Component.Motion.Property.ScrubableNumber
  ( -- * Component
    component
  
  -- * Types
  , Query(..)
  , Input
  , Output(..)
  , Slot
  
  -- * Slot Type
  , _scrubableNumber
  ) where

import Prelude

import Data.Int (round)
import Data.Maybe (Maybe(Just, Nothing))
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
import Web.UIEvent.MouseEvent (toEvent, shiftKey, ctrlKey, metaKey) as MouseEvent

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Extract clientX from a mouse event
foreign import getClientX :: MouseEvent -> Number

-- | Parse a string to a Number, returning Nothing on failure
foreign import parseNumberImpl :: (forall a. a -> Maybe a) -> (forall a. Maybe a) -> String -> Maybe Number

-- | Parse a string to a Number safely
parseNumber :: String -> Maybe Number
parseNumber = parseNumberImpl Just Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Component input
type Input =
  { value :: Number
  , min :: Maybe Number
  , max :: Maybe Number
  , step :: Number
  , precision :: Int
  , suffix :: Maybe String
  , prefix :: Maybe String
  , disabled :: Boolean
  }

-- | Component queries
data Query a
  = SetValue Number a
  | GetValue (Number -> a)
  | SetBounds (Maybe Number) (Maybe Number) a
  | SetDisabled Boolean a

-- | Component output
data Output
  = ValueChanged Number      -- Final value after scrub or text entry
  | ValueChanging Number     -- Value during scrubbing (for live preview)
  | ScrubStart               -- User started scrubbing
  | ScrubEnd                 -- User ended scrubbing

-- | Internal state
type State =
  { value :: Number
  , displayValue :: Number    -- Value shown during scrubbing
  , min :: Maybe Number
  , max :: Maybe Number
  , step :: Number
  , precision :: Int
  , suffix :: Maybe String
  , prefix :: Maybe String
  , disabled :: Boolean
  , isScrubbing :: Boolean
  , isEditing :: Boolean
  , scrubStartX :: Number
  , scrubStartValue :: Number
  , textInputValue :: String
  , inputId :: String
  }

-- | Internal actions
data Action
  = Initialize
  | Receive Input
  | HandleMouseDown MouseEvent
  | HandleMouseMove MouseEvent
  | HandleMouseUp MouseEvent
  | HandleDoubleClick MouseEvent
  | HandleBlur
  | HandleKeyDown KeyboardEvent
  | HandleTextInput String
  | CommitTextValue
  | CancelEdit

-- | Slot type helper
type Slot = H.Slot Query Output Unit

-- | Slot proxy
_scrubableNumber :: Proxy "scrubableNumber"
_scrubableNumber = Proxy

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // component
-- ═══════════════════════════════════════════════════════════════════════════════

-- | ScrubableNumber component
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
  , step: input.step
  , precision: input.precision
  , suffix: input.suffix
  , prefix: input.prefix
  , disabled: input.disabled
  , isScrubbing: false
  , isEditing: false
  , scrubStartX: 0.0
  , scrubStartValue: 0.0
  , textInputValue: ""
  , inputId: "scrubable-input-" <> show (round (input.value * 1000.0))
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // render
-- ═══════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state
  | state.isEditing = renderTextInput state
  | otherwise = renderScrubable state

-- | Render the scrubable display (normal mode)
renderScrubable :: forall m. State -> H.ComponentHTML Action () m
renderScrubable state =
  HH.div
    [ cls [ containerClasses state ]
    , HE.onMouseDown HandleMouseDown
    , HE.onDoubleClick HandleDoubleClick
    , ARIA.label ("Scrubable number input, value: " <> formatValue state)
    , ARIA.role "slider"
    , ARIA.valueNow (show state.displayValue)
    , HP.tabIndex 0
    ]
    [ -- Prefix (if any)
      case state.prefix of
        Just p -> HH.span [ cls [ "text-muted-foreground mr-0.5" ] ] [ HH.text p ]
        Nothing -> HH.text ""
    
    -- Value display
    , HH.span
        [ cls [ valueClasses state ] ]
        [ HH.text (formatValue state) ]
    
    -- Suffix (if any)
    , case state.suffix of
        Just s -> HH.span [ cls [ "text-muted-foreground ml-0.5" ] ] [ HH.text s ]
        Nothing -> HH.text ""
    ]

-- | Render the text input (editing mode)
renderTextInput :: forall m. State -> H.ComponentHTML Action () m
renderTextInput state =
  HH.input
    [ cls [ inputClasses ]
    , HP.type_ HP.InputText
    , HP.value state.textInputValue
    , HP.id state.inputId
    , HP.autofocus true
    , HE.onValueInput HandleTextInput
    , HE.onBlur (const HandleBlur)
    , HE.onKeyDown HandleKeyDown
    , ARIA.label "Enter numeric value"
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // styles
-- ═══════════════════════════════════════════════════════════════════════════════

containerClasses :: State -> String
containerClasses state = 
  "inline-flex items-center px-1.5 py-0.5 rounded text-sm font-mono " <>
  "select-none transition-colors duration-75 " <>
  if state.disabled
    then "opacity-50 cursor-not-allowed"
    else if state.isScrubbing
      then "bg-primary/20 cursor-ew-resize"
      else "hover:bg-accent cursor-ew-resize"

valueClasses :: State -> String
valueClasses state =
  if state.isScrubbing
    then "text-primary font-medium"
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
    -- Component initialized
    pure unit
  
  Receive input -> do
    state <- H.get
    -- Only update value if not currently scrubbing
    unless state.isScrubbing do
      H.modify_ \s -> s
        { value = input.value
        , displayValue = input.value
        , min = input.min
        , max = input.max
        , step = input.step
        , precision = input.precision
        , suffix = input.suffix
        , prefix = input.prefix
        , disabled = input.disabled
        }
  
  HandleMouseDown event -> do
    state <- H.get
    unless state.disabled do
      let clientX = getClientX event
      H.modify_ _ 
        { isScrubbing = true
        , scrubStartX = clientX
        , scrubStartValue = state.value
        }
      H.raise ScrubStart
  
  HandleMouseMove event -> do
    state <- H.get
    when state.isScrubbing do
      let
        clientX = getClientX event
        deltaX = clientX - state.scrubStartX
        
        -- Sensitivity modifiers
        sensitivity = 
          if MouseEvent.shiftKey event
            then 0.1  -- Fine control
            else if MouseEvent.ctrlKey event || MouseEvent.metaKey event
              then 10.0  -- Coarse control
              else 1.0   -- Normal
        
        -- Calculate new value
        rawDelta = deltaX * state.step * sensitivity / 2.0
        newValue = clampValue state (state.scrubStartValue + rawDelta)
      
      H.modify_ _ { displayValue = newValue }
      H.raise (ValueChanging newValue)
  
  HandleMouseUp _ -> do
    state <- H.get
    when state.isScrubbing do
      let finalValue = state.displayValue
      H.modify_ _ 
        { isScrubbing = false
        , value = finalValue
        }
      H.raise ScrubEnd
      H.raise (ValueChanged finalValue)
  
  HandleDoubleClick event -> do
    state <- H.get
    unless state.disabled do
      H.liftEffect $ preventDefault (MouseEvent.toEvent event)
      H.modify_ _ 
        { isEditing = true
        , textInputValue = formatValueRaw state
        }
  
  HandleBlur -> do
    handleAction CommitTextValue
  
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
  
  CommitTextValue -> do
    state <- H.get
    let
      newValue = case parseNumber state.textInputValue of
        Just parsed -> clampValue state parsed
        Nothing -> state.value  -- Keep old value on parse failure
    H.modify_ _ 
      { isEditing = false
      , value = newValue
      , displayValue = newValue
      , textInputValue = ""
      }
    -- Only emit if value actually changed
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
    -- Re-clamp current value to new bounds
    state <- H.get
    let clamped = clampValue state state.value
    H.modify_ _ { value = clamped, displayValue = clamped }
    pure (Just reply)
  
  SetDisabled dis reply -> do
    H.modify_ _ { disabled = dis }
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

-- | Format value for display (with precision)
formatValue :: State -> String
formatValue state = toStringWith (fixed state.precision) state.displayValue

-- | Format value for text input (no suffix/prefix)
formatValueRaw :: State -> String
formatValueRaw state = toStringWith (fixed state.precision) state.value
