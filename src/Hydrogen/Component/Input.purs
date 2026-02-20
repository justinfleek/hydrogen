-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                          // hydrogen // input
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Input component with variants
-- |
-- | Text input components inspired by shadcn/ui.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Input as Input
-- |
-- | -- Basic input
-- | Input.input [ Input.placeholder "Enter text..." ]
-- |
-- | -- With label
-- | Input.inputWithLabel "Email" [ Input.type_ Input.Email ]
-- |
-- | -- Textarea
-- | Input.textarea [ Input.rows 4 ]
-- |
-- | -- Disabled
-- | Input.input [ Input.disabled true ]
-- | ```
module Hydrogen.Component.Input
  ( -- * Input Components
    input
  , textarea
  , inputWithLabel
  , textareaWithLabel
    -- * Props
  , InputProps
  , InputProp
  , defaultProps
    -- * Prop Builders
  , type_
  , placeholder
  , value
  , disabled
  , required
  , readOnly
  , className
  , id
  , name
  , rows
  , onInput
  , onChange
    -- * Input Types
  , InputType(..)
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
--                                                                // input types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | HTML input types
data InputType
  = Text
  | Password
  | Email
  | Number
  | Tel
  | Url
  | Search
  | Date
  | Time
  | DatetimeLocal
  | Month
  | Week
  | Color
  | File
  | Hidden

derive instance eqInputType :: Eq InputType

inputTypeToHP :: InputType -> HP.InputType
inputTypeToHP = case _ of
  Text -> HP.InputText
  Password -> HP.InputPassword
  Email -> HP.InputEmail
  Number -> HP.InputNumber
  Tel -> HP.InputTel
  Url -> HP.InputUrl
  Search -> HP.InputSearch
  Date -> HP.InputDate
  Time -> HP.InputTime
  DatetimeLocal -> HP.InputDatetimeLocal
  Month -> HP.InputMonth
  Week -> HP.InputWeek
  Color -> HP.InputColor
  File -> HP.InputFile
  Hidden -> HP.InputHidden

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Input properties
type InputProps i =
  { type_ :: InputType
  , placeholder :: String
  , value :: String
  , disabled :: Boolean
  , required :: Boolean
  , readOnly :: Boolean
  , className :: String
  , id :: Maybe String
  , name :: Maybe String
  , rows :: Int
  , onInput :: Maybe (Event -> i)
  , onChange :: Maybe (Event -> i)
  }

-- | Property modifier
type InputProp i = InputProps i -> InputProps i

-- | Default input properties
defaultProps :: forall i. InputProps i
defaultProps =
  { type_: Text
  , placeholder: ""
  , value: ""
  , disabled: false
  , required: false
  , readOnly: false
  , className: ""
  , id: Nothing
  , name: Nothing
  , rows: 3
  , onInput: Nothing
  , onChange: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set input type
type_ :: forall i. InputType -> InputProp i
type_ t props = props { type_ = t }

-- | Set placeholder
placeholder :: forall i. String -> InputProp i
placeholder p props = props { placeholder = p }

-- | Set value
value :: forall i. String -> InputProp i
value v props = props { value = v }

-- | Set disabled state
disabled :: forall i. Boolean -> InputProp i
disabled d props = props { disabled = d }

-- | Set required state
required :: forall i. Boolean -> InputProp i
required r props = props { required = r }

-- | Set read-only state
readOnly :: forall i. Boolean -> InputProp i
readOnly r props = props { readOnly = r }

-- | Add custom class
className :: forall i. String -> InputProp i
className c props = props { className = props.className <> " " <> c }

-- | Set id
id :: forall i. String -> InputProp i
id i props = props { id = Just i }

-- | Set name
name :: forall i. String -> InputProp i
name n props = props { name = Just n }

-- | Set rows (for textarea)
rows :: forall i. Int -> InputProp i
rows r props = props { rows = r }

-- | Set input handler
onInput :: forall i. (Event -> i) -> InputProp i
onInput handler props = props { onInput = Just handler }

-- | Set change handler
onChange :: forall i. (Event -> i) -> InputProp i
onChange handler props = props { onChange = Just handler }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Base input classes
baseClasses :: String
baseClasses =
  "flex h-10 w-full rounded-md border border-input bg-background px-3 py-2 text-sm ring-offset-background file:border-0 file:bg-transparent file:text-sm file:font-medium placeholder:text-muted-foreground focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2 disabled:cursor-not-allowed disabled:opacity-50"

-- | Base textarea classes
textareaClasses :: String
textareaClasses =
  "flex min-h-[80px] w-full rounded-md border border-input bg-background px-3 py-2 text-sm ring-offset-background placeholder:text-muted-foreground focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2 disabled:cursor-not-allowed disabled:opacity-50"

-- | Render an input
input :: forall w i. Array (InputProp i) -> HH.HTML w i
input propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
  in
    HH.input
      ( [ cls [ baseClasses, props.className ]
        , HP.type_ (inputTypeToHP props.type_)
        , HP.placeholder props.placeholder
        , HP.value props.value
        , HP.disabled props.disabled
        , HP.required props.required
        , HP.readOnly props.readOnly
        ] 
        <> maybeAttr HP.id props.id
        <> maybeAttr HP.name props.name
        <> maybeHandler HE.onInput props.onInput
        <> maybeHandler HE.onChange props.onChange
      )

-- | Render a textarea
textarea :: forall w i. Array (InputProp i) -> HH.HTML w i
textarea propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
  in
    HH.textarea
      ( [ cls [ textareaClasses, props.className ]
        , HP.placeholder props.placeholder
        , HP.value props.value
        , HP.disabled props.disabled
        , HP.required props.required
        , HP.readOnly props.readOnly
        , HP.rows props.rows
        ]
        <> maybeAttr HP.id props.id
        <> maybeAttr HP.name props.name
        <> maybeHandler HE.onInput props.onInput
        <> maybeHandler HE.onChange props.onChange
      )

-- | Input with label
inputWithLabel :: forall w i. String -> Array (InputProp i) -> HH.HTML w i
inputWithLabel labelText propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    inputId = case props.id of
      Just i -> i
      Nothing -> "input-" <> labelText
    propsWithId = propMods <> [ id inputId ]
  in
    HH.div
      [ cls [ "space-y-2" ] ]
      [ HH.label
          [ cls [ "text-sm font-medium leading-none peer-disabled:cursor-not-allowed peer-disabled:opacity-70" ]
          , HP.for inputId
          ]
          [ HH.text labelText ]
      , input propsWithId
      ]

-- | Textarea with label
textareaWithLabel :: forall w i. String -> Array (InputProp i) -> HH.HTML w i
textareaWithLabel labelText propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    inputId = case props.id of
      Just i -> i
      Nothing -> "textarea-" <> labelText
    propsWithId = propMods <> [ id inputId ]
  in
    HH.div
      [ cls [ "space-y-2" ] ]
      [ HH.label
          [ cls [ "text-sm font-medium leading-none peer-disabled:cursor-not-allowed peer-disabled:opacity-70" ]
          , HP.for inputId
          ]
          [ HH.text labelText ]
      , textarea propsWithId
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

maybeAttr :: forall r i a. (a -> HH.IProp r i) -> Maybe a -> Array (HH.IProp r i)
maybeAttr _ Nothing = []
maybeAttr f (Just a) = [ f a ]

maybeHandler :: forall r i. ((Event -> i) -> HH.IProp r i) -> Maybe (Event -> i) -> Array (HH.IProp r i)
maybeHandler _ Nothing = []
maybeHandler f (Just handler) = [ f handler ]
