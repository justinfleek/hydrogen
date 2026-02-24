-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                    // hydrogen // numberinput
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | NumberInput component
-- |
-- | A specialized input for numeric values with increment/decrement controls.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.NumberInput as NumberInput
-- |
-- | -- Basic number input
-- | NumberInput.numberInput
-- |   [ NumberInput.value state.quantity
-- |   , NumberInput.onChange HandleChange
-- |   ]
-- |
-- | -- With min/max bounds
-- | NumberInput.numberInput
-- |   [ NumberInput.value state.rating
-- |   , NumberInput.min 1.0
-- |   , NumberInput.max 5.0
-- |   , NumberInput.step 0.5
-- |   , NumberInput.onChange HandleRating
-- |   ]
-- |
-- | -- Currency input
-- | NumberInput.numberInput
-- |   [ NumberInput.value state.price
-- |   , NumberInput.prefix "$"
-- |   , NumberInput.precision 2
-- |   , NumberInput.onChange HandlePrice
-- |   ]
-- |
-- | -- With custom formatting
-- | NumberInput.numberInput
-- |   [ NumberInput.value state.percentage
-- |   , NumberInput.suffix "%"
-- |   , NumberInput.min 0.0
-- |   , NumberInput.max 100.0
-- |   ]
-- | ```
module Hydrogen.Component.NumberInput
  ( -- * NumberInput Component
    numberInput
  , numberInputWithButtons
    -- * Props
  , NumberInputProps
  , NumberInputProp
  , defaultProps
    -- * Prop Builders
  , value
  , min
  , max
  , step
  , precision
  , prefix
  , suffix
  , disabled
  , readOnly
  , showButtons
  , buttonPosition
  , allowNegative
  , allowDecimal
  , clampOnBlur
  , selectOnFocus
  , className
  , id
  , name
  , placeholder
  , ariaLabel
  , onChange
  , onIncrement
  , onDecrement
  , onBlur
  , onFocus
    -- * Types
  , ButtonPosition(Sides, Right, None)
  ) where

import Prelude

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just))
import Data.Number as Number
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)
import Web.UIEvent.FocusEvent (FocusEvent)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Position of increment/decrement buttons
data ButtonPosition
  = Sides      -- Buttons on left and right
  | Right      -- Both buttons stacked on right
  | None       -- No buttons

derive instance eqButtonPosition :: Eq ButtonPosition

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | NumberInput properties
type NumberInputProps i =
  { value :: Number
  , min :: Maybe Number
  , max :: Maybe Number
  , step :: Number
  , precision :: Maybe Int
  , prefix :: Maybe String
  , suffix :: Maybe String
  , disabled :: Boolean
  , readOnly :: Boolean
  , showButtons :: Boolean
  , buttonPosition :: ButtonPosition
  , allowNegative :: Boolean
  , allowDecimal :: Boolean
  , clampOnBlur :: Boolean
  , selectOnFocus :: Boolean
  , className :: String
  , id :: Maybe String
  , name :: Maybe String
  , placeholder :: String
  , ariaLabel :: Maybe String
  , onChange :: Maybe (Number -> i)
  , onIncrement :: Maybe i
  , onDecrement :: Maybe i
  , onBlur :: Maybe (FocusEvent -> i)
  , onFocus :: Maybe (FocusEvent -> i)
  }

-- | Property modifier
type NumberInputProp i = NumberInputProps i -> NumberInputProps i

-- | Default properties
defaultProps :: forall i. NumberInputProps i
defaultProps =
  { value: 0.0
  , min: Nothing
  , max: Nothing
  , step: 1.0
  , precision: Nothing
  , prefix: Nothing
  , suffix: Nothing
  , disabled: false
  , readOnly: false
  , showButtons: true
  , buttonPosition: Right
  , allowNegative: true
  , allowDecimal: true
  , clampOnBlur: true
  , selectOnFocus: true
  , className: ""
  , id: Nothing
  , name: Nothing
  , placeholder: "0"
  , ariaLabel: Nothing
  , onChange: Nothing
  , onIncrement: Nothing
  , onDecrement: Nothing
  , onBlur: Nothing
  , onFocus: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set current value
value :: forall i. Number -> NumberInputProp i
value v props = props { value = v }

-- | Set minimum value
min :: forall i. Number -> NumberInputProp i
min m props = props { min = Just m }

-- | Set maximum value
max :: forall i. Number -> NumberInputProp i
max m props = props { max = Just m }

-- | Set step increment
step :: forall i. Number -> NumberInputProp i
step s props = props { step = s }

-- | Set decimal precision
precision :: forall i. Int -> NumberInputProp i
precision p props = props { precision = Just p }

-- | Set prefix (e.g., "$")
prefix :: forall i. String -> NumberInputProp i
prefix p props = props { prefix = Just p }

-- | Set suffix (e.g., "%")
suffix :: forall i. String -> NumberInputProp i
suffix s props = props { suffix = Just s }

-- | Set disabled state
disabled :: forall i. Boolean -> NumberInputProp i
disabled d props = props { disabled = d }

-- | Set read-only state
readOnly :: forall i. Boolean -> NumberInputProp i
readOnly r props = props { readOnly = r }

-- | Show increment/decrement buttons
showButtons :: forall i. Boolean -> NumberInputProp i
showButtons s props = props { showButtons = s }

-- | Set button position
buttonPosition :: forall i. ButtonPosition -> NumberInputProp i
buttonPosition p props = props { buttonPosition = p }

-- | Allow negative numbers
allowNegative :: forall i. Boolean -> NumberInputProp i
allowNegative a props = props { allowNegative = a }

-- | Allow decimal numbers
allowDecimal :: forall i. Boolean -> NumberInputProp i
allowDecimal a props = props { allowDecimal = a }

-- | Clamp to min/max on blur
clampOnBlur :: forall i. Boolean -> NumberInputProp i
clampOnBlur c props = props { clampOnBlur = c }

-- | Select all text on focus
selectOnFocus :: forall i. Boolean -> NumberInputProp i
selectOnFocus s props = props { selectOnFocus = s }

-- | Add custom class
className :: forall i. String -> NumberInputProp i
className c props = props { className = props.className <> " " <> c }

-- | Set id
id :: forall i. String -> NumberInputProp i
id i props = props { id = Just i }

-- | Set name
name :: forall i. String -> NumberInputProp i
name n props = props { name = Just n }

-- | Set placeholder
placeholder :: forall i. String -> NumberInputProp i
placeholder p props = props { placeholder = p }

-- | Set aria label
ariaLabel :: forall i. String -> NumberInputProp i
ariaLabel l props = props { ariaLabel = Just l }

-- | Set change handler
onChange :: forall i. (Number -> i) -> NumberInputProp i
onChange handler props = props { onChange = Just handler }

-- | Set increment handler
onIncrement :: forall i. i -> NumberInputProp i
onIncrement handler props = props { onIncrement = Just handler }

-- | Set decrement handler
onDecrement :: forall i. i -> NumberInputProp i
onDecrement handler props = props { onDecrement = Just handler }

-- | Set blur handler
onBlur :: forall i. (FocusEvent -> i) -> NumberInputProp i
onBlur handler props = props { onBlur = Just handler }

-- | Set focus handler
onFocus :: forall i. (FocusEvent -> i) -> NumberInputProp i
onFocus handler props = props { onFocus = Just handler }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // styling
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Container classes
containerClasses :: String
containerClasses =
  "relative flex items-center"

-- | Input base classes
inputClasses :: String
inputClasses =
  "flex h-10 w-full rounded-md border border-input bg-background px-3 py-2 text-sm ring-offset-background placeholder:text-muted-foreground focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2 disabled:cursor-not-allowed disabled:opacity-50"

-- | Input classes when buttons on right
inputWithButtonsClasses :: String
inputWithButtonsClasses =
  "rounded-r-none border-r-0"

-- | Input classes when buttons on sides
inputWithSideButtonsClasses :: String
inputWithSideButtonsClasses =
  "rounded-none border-x-0 text-center"

-- | Button base classes
buttonClasses :: String
buttonClasses =
  "flex items-center justify-center h-10 w-8 border border-input bg-background text-foreground hover:bg-accent hover:text-accent-foreground focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring disabled:cursor-not-allowed disabled:opacity-50 transition-colors"

-- | Stacked button classes (right position)
stackedButtonClasses :: String
stackedButtonClasses =
  "flex items-center justify-center h-5 w-8 border border-input bg-background text-foreground hover:bg-accent hover:text-accent-foreground focus-visible:outline-none focus-visible:ring-1 focus-visible:ring-ring disabled:cursor-not-allowed disabled:opacity-50 transition-colors"

-- | Prefix/suffix addon classes
addonClasses :: String
addonClasses =
  "flex items-center justify-center h-10 px-3 border border-input bg-muted text-muted-foreground text-sm"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Basic number input (no buttons)
numberInput :: forall w i. Array (NumberInputProp i) -> HH.HTML w i
numberInput propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    -- Build input handlers
    inputHandlers = 
      case props.onChange of
        Just handler -> 
          [ HE.onValueInput (\str -> 
              case Number.fromString str of
                Just n -> handler n
                Nothing -> handler props.value
            )
          ]
        Nothing -> []
    
    blurHandlers = case props.onBlur of
      Just handler -> [ HE.onBlur handler ]
      Nothing -> []
    
    focusHandlers = case props.onFocus of
      Just handler -> [ HE.onFocus handler ]
      Nothing -> []
    
    -- Optional attributes
    idAttr = case props.id of
      Just i -> [ HP.id i ]
      Nothing -> []
    
    nameAttr = case props.name of
      Just n -> [ HP.name n ]
      Nothing -> []
    
    ariaLabelAttr = case props.ariaLabel of
      Just l -> [ ARIA.label l ]
      Nothing -> []
    
    minAttr = case props.min of
      Just m -> [ HP.attr (HH.AttrName "min") (show m) ]
      Nothing -> []
    
    maxAttr = case props.max of
      Just m -> [ HP.attr (HH.AttrName "max") (show m) ]
      Nothing -> []
  in
    HH.div
      [ cls [ containerClasses, props.className ] ]
      ( -- Prefix addon
        case props.prefix of
          Just p -> 
            [ HH.span 
                [ cls [ addonClasses, "rounded-l-md border-r-0" ] ] 
                [ HH.text p ] 
            ]
          Nothing -> []
        <>
        -- Input
        [ HH.input
            ( [ cls [ inputClasses ]
              , HP.type_ HP.InputNumber
              , HP.value (show props.value)
              , HP.placeholder props.placeholder
              , HP.disabled props.disabled
              , HP.readOnly props.readOnly
              , HP.attr (HH.AttrName "step") (show props.step)
              ] 
              <> idAttr 
              <> nameAttr 
              <> ariaLabelAttr
              <> minAttr
              <> maxAttr
              <> inputHandlers 
              <> blurHandlers 
              <> focusHandlers
            )
        ]
        <>
        -- Suffix addon
        case props.suffix of
          Just s -> 
            [ HH.span 
                [ cls [ addonClasses, "rounded-r-md border-l-0" ] ] 
                [ HH.text s ] 
            ]
          Nothing -> []
      )

-- | Number input with increment/decrement buttons
numberInputWithButtons :: forall w i. Array (NumberInputProp i) -> HH.HTML w i
numberInputWithButtons propMods =
  let
    props = foldl (\p f -> f p) (defaultProps { showButtons = true }) propMods
    
    -- Check if at bounds
    atMin = case props.min of
      Just m -> props.value <= m
      Nothing -> false
    
    atMax = case props.max of
      Just m -> props.value >= m
      Nothing -> false
    
    -- Input handlers
    inputHandlers = 
      case props.onChange of
        Just handler -> 
          [ HE.onValueInput (\str -> 
              case Number.fromString str of
                Just n -> handler n
                Nothing -> handler props.value
            )
          ]
        Nothing -> []
    
    blurHandlers = case props.onBlur of
      Just handler -> [ HE.onBlur handler ]
      Nothing -> []
    
    focusHandlers = case props.onFocus of
      Just handler -> [ HE.onFocus handler ]
      Nothing -> []
    
    -- Button handlers
    decrementHandler = case props.onDecrement of
      Just handler -> [ HE.onClick (\_ -> handler) ]
      Nothing -> case props.onChange of
        Just handler -> [ HE.onClick (\_ -> handler (props.value - props.step)) ]
        Nothing -> []
    
    incrementHandler = case props.onIncrement of
      Just handler -> [ HE.onClick (\_ -> handler) ]
      Nothing -> case props.onChange of
        Just handler -> [ HE.onClick (\_ -> handler (props.value + props.step)) ]
        Nothing -> []
    
    -- Decrement button
    decrementButton :: HH.HTML w i
    decrementButton =
      HH.button
        ( [ cls [ buttonClasses, "rounded-l-md" ]
          , HP.type_ HP.ButtonButton
          , HP.disabled (props.disabled || atMin)
          , ARIA.label "Decrease value"
          ] <> decrementHandler
        )
        [ minusIcon ]
    
    -- Increment button
    incrementButton :: HH.HTML w i
    incrementButton =
      HH.button
        ( [ cls [ buttonClasses, "rounded-r-md" ]
          , HP.type_ HP.ButtonButton
          , HP.disabled (props.disabled || atMax)
          , ARIA.label "Increase value"
          ] <> incrementHandler
        )
        [ plusIcon ]
    
    -- Stacked buttons (for Right position)
    stackedButtons :: HH.HTML w i
    stackedButtons =
      HH.div
        [ cls [ "flex flex-col" ] ]
        [ HH.button
            ( [ cls [ stackedButtonClasses, "rounded-tr-md border-b-0" ]
              , HP.type_ HP.ButtonButton
              , HP.disabled (props.disabled || atMax)
              , ARIA.label "Increase value"
              ] <> incrementHandler
            )
            [ chevronUpIcon ]
        , HH.button
            ( [ cls [ stackedButtonClasses, "rounded-br-md" ]
              , HP.type_ HP.ButtonButton
              , HP.disabled (props.disabled || atMin)
              , ARIA.label "Decrease value"
              ] <> decrementHandler
            )
            [ chevronDownIcon ]
        ]
    
    -- Input classes based on button position
    inputCls = case props.buttonPosition of
      Sides -> inputWithSideButtonsClasses
      Right -> inputWithButtonsClasses
      None -> ""
    
    -- Optional attributes
    idAttr = case props.id of
      Just i -> [ HP.id i ]
      Nothing -> []
    
    nameAttr = case props.name of
      Just n -> [ HP.name n ]
      Nothing -> []
    
    minAttr = case props.min of
      Just m -> [ HP.attr (HH.AttrName "min") (show m) ]
      Nothing -> []
    
    maxAttr = case props.max of
      Just m -> [ HP.attr (HH.AttrName "max") (show m) ]
      Nothing -> []
  in
    HH.div
      [ cls [ containerClasses, props.className ]
      , ARIA.role "group"
      ]
      ( case props.buttonPosition of
          Sides ->
            [ decrementButton
            , HH.input
                ( [ cls [ inputClasses, inputCls ]
                  , HP.type_ HP.InputNumber
                  , HP.value (show props.value)
                  , HP.placeholder props.placeholder
                  , HP.disabled props.disabled
                  , HP.readOnly props.readOnly
                  , HP.attr (HH.AttrName "step") (show props.step)
                  ] 
                  <> idAttr 
                  <> nameAttr 
                  <> minAttr
                  <> maxAttr
                  <> inputHandlers 
                  <> blurHandlers 
                  <> focusHandlers
                )
            , incrementButton
            ]
          Right ->
            [ HH.input
                ( [ cls [ inputClasses, inputCls ]
                  , HP.type_ HP.InputNumber
                  , HP.value (show props.value)
                  , HP.placeholder props.placeholder
                  , HP.disabled props.disabled
                  , HP.readOnly props.readOnly
                  , HP.attr (HH.AttrName "step") (show props.step)
                  ] 
                  <> idAttr 
                  <> nameAttr
                  <> minAttr
                  <> maxAttr
                  <> inputHandlers 
                  <> blurHandlers 
                  <> focusHandlers
                )
            , stackedButtons
            ]
          None ->
            [ HH.input
                ( [ cls [ inputClasses ]
                  , HP.type_ HP.InputNumber
                  , HP.value (show props.value)
                  , HP.placeholder props.placeholder
                  , HP.disabled props.disabled
                  , HP.readOnly props.readOnly
                  , HP.attr (HH.AttrName "step") (show props.step)
                  ] 
                  <> idAttr 
                  <> nameAttr
                  <> minAttr
                  <> maxAttr
                  <> inputHandlers 
                  <> blurHandlers 
                  <> focusHandlers
                )
            ]
      )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // icons
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Plus icon
plusIcon :: forall w i. HH.HTML w i
plusIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "h-4 w-4" ]
    , HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , HP.attr (HH.AttrName "stroke-linejoin") "round"
    ]
    [ HH.element (HH.ElemName "line")
        [ HP.attr (HH.AttrName "x1") "12"
        , HP.attr (HH.AttrName "y1") "5"
        , HP.attr (HH.AttrName "x2") "12"
        , HP.attr (HH.AttrName "y2") "19"
        ]
        []
    , HH.element (HH.ElemName "line")
        [ HP.attr (HH.AttrName "x1") "5"
        , HP.attr (HH.AttrName "y1") "12"
        , HP.attr (HH.AttrName "x2") "19"
        , HP.attr (HH.AttrName "y2") "12"
        ]
        []
    ]

-- | Minus icon
minusIcon :: forall w i. HH.HTML w i
minusIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "h-4 w-4" ]
    , HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , HP.attr (HH.AttrName "stroke-linejoin") "round"
    ]
    [ HH.element (HH.ElemName "line")
        [ HP.attr (HH.AttrName "x1") "5"
        , HP.attr (HH.AttrName "y1") "12"
        , HP.attr (HH.AttrName "x2") "19"
        , HP.attr (HH.AttrName "y2") "12"
        ]
        []
    ]

-- | Chevron up icon (for stacked buttons)
chevronUpIcon :: forall w i. HH.HTML w i
chevronUpIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "h-3 w-3" ]
    , HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , HP.attr (HH.AttrName "stroke-linejoin") "round"
    ]
    [ HH.element (HH.ElemName "polyline")
        [ HP.attr (HH.AttrName "points") "18 15 12 9 6 15" ]
        []
    ]

-- | Chevron down icon (for stacked buttons)
chevronDownIcon :: forall w i. HH.HTML w i
chevronDownIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "h-3 w-3" ]
    , HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , HP.attr (HH.AttrName "stroke-linejoin") "round"
    ]
    [ HH.element (HH.ElemName "polyline")
        [ HP.attr (HH.AttrName "points") "6 9 12 15 18 9" ]
        []
    ]
