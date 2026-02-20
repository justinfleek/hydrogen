-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                          // hydrogen // radio
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Radio button component
-- |
-- | Radio buttons and radio groups for single-choice selection.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Radio as Radio
-- |
-- | -- Basic radio group
-- | Radio.radioGroup
-- |   [ Radio.name "size"
-- |   , Radio.value state.size
-- |   , Radio.onValueChange HandleSizeChange
-- |   ]
-- |   [ Radio.radioItem "sm" [ HH.text "Small" ]
-- |   , Radio.radioItem "md" [ HH.text "Medium" ]
-- |   , Radio.radioItem "lg" [ HH.text "Large" ]
-- |   ]
-- |
-- | -- Horizontal layout
-- | Radio.radioGroup
-- |   [ Radio.orientation Horizontal
-- |   , Radio.name "plan"
-- |   ]
-- |   [ Radio.radioItem "free" [ HH.text "Free" ]
-- |   , Radio.radioItem "pro" [ HH.text "Pro" ]
-- |   ]
-- |
-- | -- Disabled state
-- | Radio.radioGroup
-- |   [ Radio.disabled true ]
-- |   [ Radio.radioItem "a" [ HH.text "Option A" ]
-- |   , Radio.radioItem "b" [ HH.text "Option B" ]
-- |   ]
-- |
-- | -- Individual radio with custom styling
-- | Radio.radio
-- |   [ Radio.checked true
-- |   , Radio.variant Primary
-- |   ]
-- | ```
module Hydrogen.Component.Radio
  ( -- * Radio Components
    radioGroup
  , radioItem
  , radioItemWithDescription
  , radio
  , radioWithLabel
    -- * Types
  , Orientation(..)
  , RadioVariant(..)
    -- * Props
  , RadioGroupProps
  , RadioGroupProp
  , RadioProps
  , RadioProp
    -- * Group Prop Builders
  , name
  , value
  , orientation
  , disabled
  , className
  , onValueChange
    -- * Radio Prop Builders
  , checked
  , radioDisabled
  , radioClassName
  , variant
  , onClick
  ) where

import Prelude

import Data.Array (foldl)
import Data.Maybe (Maybe(..))
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)
import Web.UIEvent.MouseEvent (MouseEvent)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Radio group orientation
data Orientation
  = Horizontal
  | Vertical

derive instance eqOrientation :: Eq Orientation

-- | Radio button visual variant
data RadioVariant
  = Default
  | Primary
  | Accent

derive instance eqRadioVariant :: Eq RadioVariant

-- | Get variant classes
variantClasses :: RadioVariant -> String
variantClasses = case _ of
  Default -> "border-primary text-primary"
  Primary -> "border-primary text-primary"
  Accent -> "border-accent text-accent"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // group props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Radio group properties
type RadioGroupProps i =
  { name :: String
  , value :: Maybe String
  , orientation :: Orientation
  , disabled :: Boolean
  , className :: String
  , onValueChange :: Maybe (String -> i)
  }

-- | Property modifier for radio group
type RadioGroupProp i = RadioGroupProps i -> RadioGroupProps i

-- | Default radio group properties
defaultGroupProps :: forall i. RadioGroupProps i
defaultGroupProps =
  { name: ""
  , value: Nothing
  , orientation: Vertical
  , disabled: false
  , className: ""
  , onValueChange: Nothing
  }

-- | Set group name (for form submission)
name :: forall i. String -> RadioGroupProp i
name n props = props { name = n }

-- | Set selected value
value :: forall i. String -> RadioGroupProp i
value v props = props { value = Just v }

-- | Set orientation
orientation :: forall i. Orientation -> RadioGroupProp i
orientation o props = props { orientation = o }

-- | Set disabled state for entire group
disabled :: forall i. Boolean -> RadioGroupProp i
disabled d props = props { disabled = d }

-- | Add custom class
className :: forall i. String -> RadioGroupProp i
className c props = props { className = props.className <> " " <> c }

-- | Set value change handler
onValueChange :: forall i. (String -> i) -> RadioGroupProp i
onValueChange handler props = props { onValueChange = Just handler }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // radio props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Individual radio button properties
type RadioProps i =
  { checked :: Boolean
  , disabled :: Boolean
  , className :: String
  , variant :: RadioVariant
  , onClick :: Maybe (MouseEvent -> i)
  }

-- | Property modifier for radio button
type RadioProp i = RadioProps i -> RadioProps i

-- | Default radio properties
defaultRadioProps :: forall i. RadioProps i
defaultRadioProps =
  { checked: false
  , disabled: false
  , className: ""
  , variant: Default
  , onClick: Nothing
  }

-- | Set checked state
checked :: forall i. Boolean -> RadioProp i
checked c props = props { checked = c }

-- | Set disabled state
radioDisabled :: forall i. Boolean -> RadioProp i
radioDisabled d props = props { disabled = d }

-- | Add custom class
radioClassName :: forall i. String -> RadioProp i
radioClassName c props = props { className = props.className <> " " <> c }

-- | Set visual variant
variant :: forall i. RadioVariant -> RadioProp i
variant v props = props { variant = v }

-- | Set click handler
onClick :: forall i. (MouseEvent -> i) -> RadioProp i
onClick handler props = props { onClick = Just handler }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Base radio button classes
radioClasses :: String
radioClasses =
  "aspect-square h-4 w-4 rounded-full border border-primary text-primary ring-offset-background focus:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2 disabled:cursor-not-allowed disabled:opacity-50"

-- | Radio group container
radioGroup :: forall w i. Array (RadioGroupProp i) -> Array (HH.HTML w i) -> HH.HTML w i
radioGroup propMods children =
  let
    props = foldl (\p f -> f p) defaultGroupProps propMods
    orientationClass = case props.orientation of
      Horizontal -> "flex flex-row gap-4"
      Vertical -> "flex flex-col gap-2"
    disabledClass = if props.disabled then "opacity-50 pointer-events-none" else ""
  in
    HH.div
      [ cls [ orientationClass, disabledClass, props.className ]
      , ARIA.role "radiogroup"
      ]
      children

-- | Radio item within a group (value + label)
radioItem :: forall w i. String -> Array (HH.HTML w i) -> HH.HTML w i
radioItem itemValue children =
  HH.label
    [ cls [ "flex items-center space-x-2 cursor-pointer" ] ]
    [ HH.input
        [ cls [ radioClasses ]
        , HP.type_ HP.InputRadio
        , HP.value itemValue
        ]
    , HH.span
        [ cls [ "text-sm font-medium leading-none peer-disabled:cursor-not-allowed peer-disabled:opacity-70" ] ]
        children
    ]

-- | Radio item with description
radioItemWithDescription :: forall w i. 
  { value :: String, label :: String, description :: String } -> 
  HH.HTML w i
radioItemWithDescription opts =
  HH.label
    [ cls [ "flex items-start space-x-3 cursor-pointer" ] ]
    [ HH.input
        [ cls [ radioClasses, "mt-0.5" ]
        , HP.type_ HP.InputRadio
        , HP.value opts.value
        ]
    , HH.div
        [ cls [ "space-y-1" ] ]
        [ HH.span
            [ cls [ "text-sm font-medium leading-none" ] ]
            [ HH.text opts.label ]
        , HH.p
            [ cls [ "text-sm text-muted-foreground" ] ]
            [ HH.text opts.description ]
        ]
    ]

-- | Standalone radio button (for custom usage)
radio :: forall w i. Array (RadioProp i) -> HH.HTML w i
radio propMods =
  let
    props = foldl (\p f -> f p) defaultRadioProps propMods
    checkedClass = if props.checked then "bg-primary" else ""
  in
    HH.button
      ( [ cls [ radioClasses, variantClasses props.variant, checkedClass, props.className ]
        , HP.type_ HP.ButtonButton
        , HP.disabled props.disabled
        , ARIA.role "radio"
        , ARIA.checked (if props.checked then "true" else "false")
        ] <> case props.onClick of
          Just handler -> [ HE.onClick handler ]
          Nothing -> []
      )
      [ -- Inner dot indicator
        if props.checked
          then HH.span [ cls [ "block h-2.5 w-2.5 rounded-full bg-current m-auto" ] ] []
          else HH.text ""
      ]

-- | Radio button with label
radioWithLabel :: forall w i. String -> Array (RadioProp i) -> HH.HTML w i
radioWithLabel labelText propMods =
  HH.label
    [ cls [ "flex items-center space-x-2 cursor-pointer" ] ]
    [ radio propMods
    , HH.span
        [ cls [ "text-sm font-medium leading-none peer-disabled:cursor-not-allowed peer-disabled:opacity-70" ] ]
        [ HH.text labelText ]
    ]
