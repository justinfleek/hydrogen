-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // hydrogen // taginput
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TagInput/MultiSelect component
-- |
-- | A component for selecting and managing multiple tags or items.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.TagInput as TagInput
-- |
-- | -- Basic tag input
-- | TagInput.tagInput
-- |   [ TagInput.tags state.selectedTags
-- |   , TagInput.onAdd HandleAddTag
-- |   , TagInput.onRemove HandleRemoveTag
-- |   ]
-- |
-- | -- With suggestions
-- | TagInput.tagInput
-- |   [ TagInput.tags state.tags
-- |   , TagInput.suggestions availableTags
-- |   , TagInput.onAdd HandleAdd
-- |   , TagInput.onRemove HandleRemove
-- |   ]
-- |
-- | -- With max tags limit
-- | TagInput.tagInput
-- |   [ TagInput.tags state.tags
-- |   , TagInput.maxTags 5
-- |   , TagInput.onAdd HandleAdd
-- |   , TagInput.onRemove HandleRemove
-- |   ]
-- |
-- | -- Custom tag rendering
-- | TagInput.tagInput
-- |   [ TagInput.tagsWithData userTags
-- |   , TagInput.renderTag \tag -> HH.div_ [ HH.text tag.label ]
-- |   ]
-- | ```
module Hydrogen.Component.TagInput
  ( -- * TagInput Component
    tagInput
  , tag
  , tagList
    -- * Tag Types
  , Tag
  , mkTag
  , tagWithData
    -- * Props
  , TagInputProps
  , TagInputProp
  , defaultProps
    -- * Prop Builders
  , tags
  , tagsWithData
  , suggestions
  , inputValue
  , placeholder
  , disabled
  , maxTags
  , allowDuplicates
  , allowCustom
  , delimiter
  , className
  , tagClassName
  , onAdd
  , onRemove
  , onChange
  , onInputChange
  , renderTag
    -- * Variants
  , TagVariant(..)
  , tagVariant
  ) where

import Prelude

import Data.Array (foldl)
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String as String
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)
import Web.UIEvent.KeyboardEvent as KE

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // tag types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A tag with value, label, and optional metadata
type Tag a =
  { value :: String
  , label :: String
  , data :: Maybe a
  , removable :: Boolean
  }

-- | Create a simple tag from a string
mkTag :: String -> Tag Unit
mkTag s = { value: s, label: s, data: Nothing, removable: true }

-- | Create a tag with attached data
tagWithData :: forall a. String -> String -> a -> Tag a
tagWithData val lbl d = 
  { value: val, label: lbl, data: Just d, removable: true }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // variants
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Tag visual variants
data TagVariant
  = Default
  | Primary
  | Secondary
  | Destructive
  | Outline

derive instance eqTagVariant :: Eq TagVariant

-- | Get variant classes
variantClasses :: TagVariant -> String
variantClasses = case _ of
  Default ->
    "bg-secondary text-secondary-foreground hover:bg-secondary/80"
  Primary ->
    "bg-primary text-primary-foreground hover:bg-primary/80"
  Secondary ->
    "bg-secondary text-secondary-foreground hover:bg-secondary/80"
  Destructive ->
    "bg-destructive text-destructive-foreground hover:bg-destructive/80"
  Outline ->
    "border border-input bg-background hover:bg-accent hover:text-accent-foreground"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | TagInput properties
type TagInputProps a i =
  { tags :: Array (Tag a)
  , suggestions :: Array String
  , inputValue :: String
  , placeholder :: String
  , disabled :: Boolean
  , maxTags :: Maybe Int
  , allowDuplicates :: Boolean
  , allowCustom :: Boolean
  , delimiter :: String
  , className :: String
  , tagClassName :: String
  , tagVariant :: TagVariant
  , onAdd :: Maybe (String -> i)
  , onRemove :: Maybe (String -> i)
  , onChange :: Maybe (Array (Tag a) -> i)
  , onInputChange :: Maybe (String -> i)
  , renderTag :: Maybe (Tag a -> forall w. HH.HTML w i)
  }

-- | Property modifier
type TagInputProp a i = TagInputProps a i -> TagInputProps a i

-- | Default properties
defaultProps :: forall a i. TagInputProps a i
defaultProps =
  { tags: []
  , suggestions: []
  , inputValue: ""
  , placeholder: "Add tags..."
  , disabled: false
  , maxTags: Nothing
  , allowDuplicates: false
  , allowCustom: true
  , delimiter: ","
  , className: ""
  , tagClassName: ""
  , tagVariant: Default
  , onAdd: Nothing
  , onRemove: Nothing
  , onChange: Nothing
  , onInputChange: Nothing
  , renderTag: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set tags from simple strings
tags :: forall a i. Array String -> TagInputProp a i
tags strs props = props 
  { tags = map (\s -> { value: s, label: s, data: Nothing, removable: true }) strs }

-- | Set tags with custom data
tagsWithData :: forall a i. Array (Tag a) -> TagInputProp a i
tagsWithData ts props = props { tags = ts }

-- | Set available suggestions
suggestions :: forall a i. Array String -> TagInputProp a i
suggestions sugs props = props { suggestions = sugs }

-- | Set current input value
inputValue :: forall a i. String -> TagInputProp a i
inputValue v props = props { inputValue = v }

-- | Set placeholder text
placeholder :: forall a i. String -> TagInputProp a i
placeholder p props = props { placeholder = p }

-- | Set disabled state
disabled :: forall a i. Boolean -> TagInputProp a i
disabled d props = props { disabled = d }

-- | Set maximum number of tags
maxTags :: forall a i. Int -> TagInputProp a i
maxTags n props = props { maxTags = Just n }

-- | Allow duplicate tags
allowDuplicates :: forall a i. Boolean -> TagInputProp a i
allowDuplicates a props = props { allowDuplicates = a }

-- | Allow custom tags (not from suggestions)
allowCustom :: forall a i. Boolean -> TagInputProp a i
allowCustom a props = props { allowCustom = a }

-- | Set delimiter for splitting input
delimiter :: forall a i. String -> TagInputProp a i
delimiter d props = props { delimiter = d }

-- | Add custom class to container
className :: forall a i. String -> TagInputProp a i
className c props = props { className = props.className <> " " <> c }

-- | Add custom class to tags
tagClassName :: forall a i. String -> TagInputProp a i
tagClassName c props = props { tagClassName = props.tagClassName <> " " <> c }

-- | Set tag variant
tagVariant :: forall a i. TagVariant -> TagInputProp a i
tagVariant v props = props { tagVariant = v }

-- | Set add handler
onAdd :: forall a i. (String -> i) -> TagInputProp a i
onAdd handler props = props { onAdd = Just handler }

-- | Set remove handler
onRemove :: forall a i. (String -> i) -> TagInputProp a i
onRemove handler props = props { onRemove = Just handler }

-- | Set change handler (receives full tag array)
onChange :: forall a i. (Array (Tag a) -> i) -> TagInputProp a i
onChange handler props = props { onChange = Just handler }

-- | Set input change handler
onInputChange :: forall a i. (String -> i) -> TagInputProp a i
onInputChange handler props = props { onInputChange = Just handler }

-- | Set custom tag renderer
renderTag :: forall a i. (Tag a -> forall w. HH.HTML w i) -> TagInputProp a i
renderTag renderer props = props { renderTag = Just renderer }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // styling
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Container classes
containerClasses :: String
containerClasses =
  "flex flex-wrap items-center gap-1.5 rounded-md border border-input bg-background px-3 py-2 text-sm ring-offset-background focus-within:ring-2 focus-within:ring-ring focus-within:ring-offset-2"

-- | Tag base classes
tagBaseClasses :: String
tagBaseClasses =
  "inline-flex items-center gap-1 rounded-md px-2 py-0.5 text-xs font-medium transition-colors"

-- | Input classes
inputClasses :: String
inputClasses =
  "flex-1 min-w-[120px] bg-transparent outline-none placeholder:text-muted-foreground disabled:cursor-not-allowed"

-- | Remove button classes
removeButtonClasses :: String
removeButtonClasses =
  "ml-1 rounded-full hover:bg-foreground/20 focus:outline-none focus:ring-1 focus:ring-ring"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render a single tag
tag :: forall w i. 
  { label :: String
  , variant :: TagVariant
  , removable :: Boolean
  , onRemove :: Maybe i
  , className :: String
  } -> 
  HH.HTML w i
tag opts =
  HH.span
    [ cls [ tagBaseClasses, variantClasses opts.variant, opts.className ] ]
    [ HH.text opts.label
    , if opts.removable
        then case opts.onRemove of
          Just handler ->
            HH.button
              [ cls [ removeButtonClasses ]
              , HP.type_ HP.ButtonButton
              , HE.onClick (\_ -> handler)
              , ARIA.label "Remove tag"
              ]
              [ removeIcon ]
          Nothing -> HH.text ""
        else HH.text ""
    ]

-- | Render a list of tags (standalone)
tagList :: forall w i. 
  { variant :: TagVariant, className :: String } -> 
  Array String -> 
  HH.HTML w i
tagList opts tagStrs =
  HH.div
    [ cls [ "flex flex-wrap gap-1.5", opts.className ] ]
    ( map (\t -> tag 
        { label: t
        , variant: opts.variant
        , removable: false
        , onRemove: Nothing
        , className: ""
        }
      ) tagStrs
    )

-- | Full TagInput component
tagInput :: forall w a i. Array (TagInputProp a i) -> HH.HTML w i
tagInput propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    -- Check if max tags reached
    atMaxTags = case props.maxTags of
      Just max -> Array.length props.tags >= max
      Nothing -> false
    
    -- Disabled state (explicit or at max)
    isDisabled = props.disabled || atMaxTags
    
    -- Default tag renderer
    defaultRenderer :: Tag a -> HH.HTML w i
    defaultRenderer t =
      let
        removeHandler = case props.onRemove of
          Just handler -> Just (handler t.value)
          Nothing -> Nothing
      in
        tag
          { label: t.label
          , variant: props.tagVariant
          , removable: t.removable && not props.disabled
          , onRemove: removeHandler
          , className: props.tagClassName
          }
    
    -- Render all tags
    renderedTags :: Array (HH.HTML w i)
    renderedTags = map defaultRenderer props.tags
    
    -- Input handlers
    inputChangeHandler = case props.onInputChange of
      Just handler -> [ HE.onValueInput handler ]
      Nothing -> []
    
    keyHandler = case props.onAdd of
      Just handler -> 
        [ HE.onKeyDown (\e -> 
            if KE.key e == "Enter" || KE.key e == props.delimiter
              then handler (String.trim props.inputValue)
              else handler ""
          )
        ]
      Nothing -> []
    
    -- Container disabled styling
    disabledClass = if props.disabled then "opacity-50 cursor-not-allowed" else ""
  in
    HH.div
      [ cls [ containerClasses, disabledClass, props.className ]
      , ARIA.role "listbox"
      , ARIA.label "Selected tags"
      ]
      ( renderedTags <>
        [ HH.input
            ( [ cls [ inputClasses ]
              , HP.type_ HP.InputText
              , HP.placeholder (if atMaxTags then "Max tags reached" else props.placeholder)
              , HP.value props.inputValue
              , HP.disabled isDisabled
              , ARIA.label "Add tag"
              ] <> inputChangeHandler <> keyHandler
            )
        ]
      )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // icons
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Small X icon for remove button
removeIcon :: forall w i. HH.HTML w i
removeIcon =
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
    [ HH.element (HH.ElemName "line")
        [ HP.attr (HH.AttrName "x1") "18"
        , HP.attr (HH.AttrName "y1") "6"
        , HP.attr (HH.AttrName "x2") "6"
        , HP.attr (HH.AttrName "y2") "18"
        ]
        []
    , HH.element (HH.ElemName "line")
        [ HP.attr (HH.AttrName "x1") "6"
        , HP.attr (HH.AttrName "y1") "6"
        , HP.attr (HH.AttrName "x2") "18"
        , HP.attr (HH.AttrName "y2") "18"
        ]
        []
    ]
