-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // hydrogen // checkbox
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Checkbox component
-- |
-- | Styled checkbox inputs.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Checkbox as Checkbox
-- |
-- | -- Basic checkbox
-- | Checkbox.checkbox [ Checkbox.checked true ]
-- |
-- | -- With label
-- | Checkbox.checkboxWithLabel "Accept terms" [ Checkbox.checked state.accepted ]
-- |
-- | -- Disabled
-- | Checkbox.checkbox [ Checkbox.disabled true ]
-- | ```
module Hydrogen.Component.Checkbox
  ( -- * Checkbox Component
    checkbox
  , checkboxWithLabel
    -- * Props
  , CheckboxProps
  , CheckboxProp
  , checked
  , disabled
  , className
  , id
  , onChange
  ) where

import Prelude

import Data.Array (foldl)
import Data.Maybe (Maybe(..))
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Hydrogen.UI.Core (cls)
import Web.Event.Event (Event)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

type CheckboxProps i =
  { checked :: Boolean
  , disabled :: Boolean
  , className :: String
  , id :: Maybe String
  , onChange :: Maybe (Event -> i)
  }

type CheckboxProp i = CheckboxProps i -> CheckboxProps i

defaultProps :: forall i. CheckboxProps i
defaultProps =
  { checked: false
  , disabled: false
  , className: ""
  , id: Nothing
  , onChange: Nothing
  }

-- | Set checked state
checked :: forall i. Boolean -> CheckboxProp i
checked c props = props { checked = c }

-- | Set disabled state
disabled :: forall i. Boolean -> CheckboxProp i
disabled d props = props { disabled = d }

-- | Add custom class
className :: forall i. String -> CheckboxProp i
className c props = props { className = props.className <> " " <> c }

-- | Set id
id :: forall i. String -> CheckboxProp i
id i props = props { id = Just i }

-- | Set change handler
onChange :: forall i. (Event -> i) -> CheckboxProp i
onChange handler props = props { onChange = Just handler }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Checkbox input
checkbox :: forall w i. Array (CheckboxProp i) -> HH.HTML w i
checkbox propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    baseClasses = "peer h-4 w-4 shrink-0 rounded-sm border border-primary ring-offset-background focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2 disabled:cursor-not-allowed disabled:opacity-50 data-[state=checked]:bg-primary data-[state=checked]:text-primary-foreground"
  in
    HH.input
      ( [ cls [ baseClasses, props.className ]
        , HP.type_ HP.InputCheckbox
        , HP.checked props.checked
        , HP.disabled props.disabled
        ] 
        <> case props.id of
            Just i -> [ HP.id i ]
            Nothing -> []
        <> case props.onChange of
            Just handler -> [ HE.onChange handler ]
            Nothing -> []
      )

-- | Checkbox with label
checkboxWithLabel :: forall w i. String -> Array (CheckboxProp i) -> HH.HTML w i
checkboxWithLabel labelText propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    inputId = case props.id of
      Just i -> i
      Nothing -> "checkbox-" <> labelText
    propsWithId = propMods <> [ id inputId ]
  in
    HH.div
      [ cls [ "flex items-center space-x-2" ] ]
      [ checkbox propsWithId
      , HH.label
          [ cls [ "text-sm font-medium leading-none peer-disabled:cursor-not-allowed peer-disabled:opacity-70" ]
          , HP.for inputId
          ]
          [ HH.text labelText ]
      ]
