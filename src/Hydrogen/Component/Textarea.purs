-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // hydrogen // textarea
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Enhanced Textarea component
-- |
-- | A feature-rich textarea with auto-resize, character counting,
-- | and validation states.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Textarea as Textarea
-- |
-- | -- Basic textarea
-- | Textarea.textarea [ Textarea.placeholder "Enter your message..." ]
-- |
-- | -- With auto-resize
-- | Textarea.textarea
-- |   [ Textarea.autoResize true
-- |   , Textarea.minRows 3
-- |   , Textarea.maxRows 10
-- |   ]
-- |
-- | -- With character limit
-- | Textarea.textareaWithCounter
-- |   [ Textarea.maxLength 500
-- |   , Textarea.value state.message
-- |   ]
-- |
-- | -- With label and error state
-- | Textarea.textareaWithLabel "Description"
-- |   [ Textarea.error true
-- |   , Textarea.errorMessage "Description is required"
-- |   , Textarea.required true
-- |   ]
-- |
-- | -- Disabled/readonly states
-- | Textarea.textarea [ Textarea.disabled true ]
-- | Textarea.textarea [ Textarea.readOnly true ]
-- | ```
module Hydrogen.Component.Textarea
  ( -- * Textarea Components
    textarea
  , textareaWithLabel
  , textareaWithCounter
  , textareaField
    -- * Props
  , TextareaProps
  , TextareaProp
  , defaultProps
    -- * Prop Builders
  , value
  , placeholder
  , disabled
  , readOnly
  , required
  , autoResize
  , minRows
  , maxRows
  , maxLength
  , error
  , errorMessage
  , className
  , id
  , name
  , onInput
  , onChange
  , onFocus
  , onBlur
  ) where

import Prelude

import Data.Array (foldl)
import Data.Maybe (Maybe(..))
import Data.String (length) as String
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)
import Web.Event.Event (Event)
import Web.UIEvent.FocusEvent (FocusEvent)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Textarea properties
type TextareaProps i =
  { value :: String
  , placeholder :: String
  , disabled :: Boolean
  , readOnly :: Boolean
  , required :: Boolean
  , autoResize :: Boolean
  , minRows :: Int
  , maxRows :: Int
  , maxLength :: Maybe Int
  , error :: Boolean
  , errorMessage :: String
  , className :: String
  , id :: Maybe String
  , name :: Maybe String
  , onInput :: Maybe (Event -> i)
  , onChange :: Maybe (Event -> i)
  , onFocus :: Maybe (FocusEvent -> i)
  , onBlur :: Maybe (FocusEvent -> i)
  }

-- | Property modifier
type TextareaProp i = TextareaProps i -> TextareaProps i

-- | Default textarea properties
defaultProps :: forall i. TextareaProps i
defaultProps =
  { value: ""
  , placeholder: ""
  , disabled: false
  , readOnly: false
  , required: false
  , autoResize: false
  , minRows: 3
  , maxRows: 10
  , maxLength: Nothing
  , error: false
  , errorMessage: ""
  , className: ""
  , id: Nothing
  , name: Nothing
  , onInput: Nothing
  , onChange: Nothing
  , onFocus: Nothing
  , onBlur: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set value
value :: forall i. String -> TextareaProp i
value v props = props { value = v }

-- | Set placeholder
placeholder :: forall i. String -> TextareaProp i
placeholder p props = props { placeholder = p }

-- | Set disabled state
disabled :: forall i. Boolean -> TextareaProp i
disabled d props = props { disabled = d }

-- | Set read-only state
readOnly :: forall i. Boolean -> TextareaProp i
readOnly r props = props { readOnly = r }

-- | Set required state
required :: forall i. Boolean -> TextareaProp i
required r props = props { required = r }

-- | Enable auto-resize to content
autoResize :: forall i. Boolean -> TextareaProp i
autoResize a props = props { autoResize = a }

-- | Set minimum rows (for auto-resize)
minRows :: forall i. Int -> TextareaProp i
minRows r props = props { minRows = r }

-- | Set maximum rows (for auto-resize)
maxRows :: forall i. Int -> TextareaProp i
maxRows r props = props { maxRows = r }

-- | Set maximum character length
maxLength :: forall i. Int -> TextareaProp i
maxLength l props = props { maxLength = Just l }

-- | Set error state
error :: forall i. Boolean -> TextareaProp i
error e props = props { error = e }

-- | Set error message
errorMessage :: forall i. String -> TextareaProp i
errorMessage msg props = props { errorMessage = msg, error = true }

-- | Add custom class
className :: forall i. String -> TextareaProp i
className c props = props { className = props.className <> " " <> c }

-- | Set id
id :: forall i. String -> TextareaProp i
id i props = props { id = Just i }

-- | Set name
name :: forall i. String -> TextareaProp i
name n props = props { name = Just n }

-- | Set input handler
onInput :: forall i. (Event -> i) -> TextareaProp i
onInput handler props = props { onInput = Just handler }

-- | Set change handler
onChange :: forall i. (Event -> i) -> TextareaProp i
onChange handler props = props { onChange = Just handler }

-- | Set focus handler
onFocus :: forall i. (FocusEvent -> i) -> TextareaProp i
onFocus handler props = props { onFocus = Just handler }

-- | Set blur handler
onBlur :: forall i. (FocusEvent -> i) -> TextareaProp i
onBlur handler props = props { onBlur = Just handler }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Base textarea classes
baseClasses :: String
baseClasses =
  "flex min-h-[80px] w-full rounded-md border border-input bg-background px-3 py-2 text-sm ring-offset-background placeholder:text-muted-foreground focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2 disabled:cursor-not-allowed disabled:opacity-50"

-- | Error state classes
errorClasses :: String
errorClasses =
  "border-destructive focus-visible:ring-destructive"

-- | Render a textarea
textarea :: forall w i. Array (TextareaProp i) -> HH.HTML w i
textarea propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    errorClass = if props.error then errorClasses else ""
    resizeClass = if props.autoResize then "resize-none overflow-hidden" else "resize-y"
  in
    HH.textarea
      ( [ cls [ baseClasses, errorClass, resizeClass, props.className ]
        , HP.placeholder props.placeholder
        , HP.value props.value
        , HP.disabled props.disabled
        , HP.readOnly props.readOnly
        , HP.required props.required
        , HP.rows props.minRows
        ]
        <> maybeAttr HP.id props.id
        <> maybeAttr HP.name props.name
        <> case props.maxLength of
            Just ml -> [ HP.attr (HH.AttrName "maxlength") (show ml) ]
            Nothing -> []
        <> case props.error of
            true -> [ ARIA.invalid "true" ]
            false -> []
        <> maybeHandler HE.onInput props.onInput
        <> maybeHandler HE.onChange props.onChange
        <> maybeFocusHandler HE.onFocus props.onFocus
        <> maybeFocusHandler HE.onBlur props.onBlur
      )

-- | Textarea with label
textareaWithLabel :: forall w i. String -> Array (TextareaProp i) -> HH.HTML w i
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
          [ HH.text labelText
          , if props.required
              then HH.span [ cls [ "text-destructive ml-1" ] ] [ HH.text "*" ]
              else HH.text ""
          ]
      , textarea propsWithId
      , if props.error && props.errorMessage /= ""
          then HH.p
            [ cls [ "text-sm text-destructive" ] ]
            [ HH.text props.errorMessage ]
          else HH.text ""
      ]

-- | Textarea with character counter
textareaWithCounter :: forall w i. Array (TextareaProp i) -> HH.HTML w i
textareaWithCounter propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    currentLength = String.length props.value
    counterText = case props.maxLength of
      Just ml -> show currentLength <> " / " <> show ml
      Nothing -> show currentLength <> " characters"
    isOverLimit = case props.maxLength of
      Just ml -> currentLength > ml
      Nothing -> false
    counterClass = if isOverLimit then "text-destructive" else "text-muted-foreground"
  in
    HH.div
      [ cls [ "space-y-1" ] ]
      [ textarea propMods
      , HH.div
          [ cls [ "flex justify-end" ] ]
          [ HH.span
              [ cls [ "text-xs", counterClass ] ]
              [ HH.text counterText ]
          ]
      ]

-- | Full textarea field (label + textarea + counter + error)
textareaField :: forall w i. String -> Array (TextareaProp i) -> HH.HTML w i
textareaField labelText propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    inputId = case props.id of
      Just i -> i
      Nothing -> "textarea-" <> labelText
    propsWithId = propMods <> [ id inputId ]
    currentLength = String.length props.value
    counterText = case props.maxLength of
      Just ml -> show currentLength <> " / " <> show ml
      Nothing -> ""
    isOverLimit = case props.maxLength of
      Just ml -> currentLength > ml
      Nothing -> false
  in
    HH.div
      [ cls [ "space-y-2" ] ]
      [ -- Label
        HH.label
          [ cls [ "text-sm font-medium leading-none peer-disabled:cursor-not-allowed peer-disabled:opacity-70" ]
          , HP.for inputId
          ]
          [ HH.text labelText
          , if props.required
              then HH.span [ cls [ "text-destructive ml-1" ] ] [ HH.text "*" ]
              else HH.text ""
          ]
      -- Textarea
      , textarea propsWithId
      -- Footer (counter + error)
      , HH.div
          [ cls [ "flex justify-between" ] ]
          [ -- Error message
            if props.error && props.errorMessage /= ""
              then HH.p [ cls [ "text-sm text-destructive" ] ] [ HH.text props.errorMessage ]
              else HH.text ""
          -- Character counter
          , case props.maxLength of
              Just _ -> 
                HH.span
                  [ cls [ "text-xs", if isOverLimit then "text-destructive" else "text-muted-foreground" ] ]
                  [ HH.text counterText ]
              Nothing -> HH.text ""
          ]
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

maybeFocusHandler :: forall r i. ((FocusEvent -> i) -> HH.IProp r i) -> Maybe (FocusEvent -> i) -> Array (HH.IProp r i)
maybeFocusHandler _ Nothing = []
maybeFocusHandler f (Just handler) = [ f handler ]
