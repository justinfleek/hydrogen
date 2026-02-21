-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                    // hydrogen // searchinput
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | SearchInput component
-- |
-- | A search input with icon, loading state, and clear button.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.SearchInput as SearchInput
-- |
-- | -- Basic search input
-- | SearchInput.searchInput
-- |   [ SearchInput.value state.query
-- |   , SearchInput.onInput HandleSearch
-- |   ]
-- |
-- | -- With loading state
-- | SearchInput.searchInput
-- |   [ SearchInput.value state.query
-- |   , SearchInput.loading state.isSearching
-- |   , SearchInput.onInput HandleSearch
-- |   ]
-- |
-- | -- With clear button
-- | SearchInput.searchInput
-- |   [ SearchInput.value state.query
-- |   , SearchInput.showClear true
-- |   , SearchInput.onClear HandleClear
-- |   ]
-- |
-- | -- Submit on enter
-- | SearchInput.searchInput
-- |   [ SearchInput.value state.query
-- |   , SearchInput.onSubmit HandleSubmit
-- |   ]
-- | ```
module Hydrogen.Component.SearchInput
  ( -- * SearchInput Component
    searchInput
    -- * Props
  , SearchInputProps
  , SearchInputProp
  , defaultProps
    -- * Prop Builders
  , value
  , placeholder
  , disabled
  , loading
  , showClear
  , showSubmit
  , size
  , className
  , id
  , name
  , ariaLabel
  , onInput
  , onChange
  , onClear
  , onSubmit
  , onFocus
  , onBlur
    -- * Types
  , Size(..)
  ) where

import Prelude

import Data.Array (foldl)
import Data.Maybe (Maybe(..))
import Data.String as String
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)
import Web.Event.Event (Event)
import Web.UIEvent.FocusEvent (FocusEvent)
import Web.UIEvent.KeyboardEvent as KE

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Size variants
data Size
  = Small
  | Medium
  | Large

derive instance eqSize :: Eq Size

-- | Get size classes
sizeClasses :: Size -> { container :: String, input :: String, icon :: String }
sizeClasses = case _ of
  Small ->
    { container: "h-8"
    , input: "h-8 text-xs pl-8 pr-8"
    , icon: "h-3.5 w-3.5"
    }
  Medium ->
    { container: "h-10"
    , input: "h-10 text-sm pl-10 pr-10"
    , icon: "h-4 w-4"
    }
  Large ->
    { container: "h-12"
    , input: "h-12 text-base pl-12 pr-12"
    , icon: "h-5 w-5"
    }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | SearchInput properties
type SearchInputProps i =
  { value :: String
  , placeholder :: String
  , disabled :: Boolean
  , loading :: Boolean
  , showClear :: Boolean
  , showSubmit :: Boolean
  , size :: Size
  , className :: String
  , id :: Maybe String
  , name :: Maybe String
  , ariaLabel :: Maybe String
  , onInput :: Maybe (String -> i)
  , onChange :: Maybe (Event -> i)
  , onClear :: Maybe i
  , onSubmit :: Maybe (String -> i)
  , onFocus :: Maybe (FocusEvent -> i)
  , onBlur :: Maybe (FocusEvent -> i)
  }

-- | Property modifier
type SearchInputProp i = SearchInputProps i -> SearchInputProps i

-- | Default properties
defaultProps :: forall i. SearchInputProps i
defaultProps =
  { value: ""
  , placeholder: "Search..."
  , disabled: false
  , loading: false
  , showClear: true
  , showSubmit: false
  , size: Medium
  , className: ""
  , id: Nothing
  , name: Nothing
  , ariaLabel: Nothing
  , onInput: Nothing
  , onChange: Nothing
  , onClear: Nothing
  , onSubmit: Nothing
  , onFocus: Nothing
  , onBlur: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set current value
value :: forall i. String -> SearchInputProp i
value v props = props { value = v }

-- | Set placeholder text
placeholder :: forall i. String -> SearchInputProp i
placeholder p props = props { placeholder = p }

-- | Set disabled state
disabled :: forall i. Boolean -> SearchInputProp i
disabled d props = props { disabled = d }

-- | Set loading state
loading :: forall i. Boolean -> SearchInputProp i
loading l props = props { loading = l }

-- | Show clear button
showClear :: forall i. Boolean -> SearchInputProp i
showClear s props = props { showClear = s }

-- | Show submit button
showSubmit :: forall i. Boolean -> SearchInputProp i
showSubmit s props = props { showSubmit = s }

-- | Set size
size :: forall i. Size -> SearchInputProp i
size s props = props { size = s }

-- | Add custom class
className :: forall i. String -> SearchInputProp i
className c props = props { className = props.className <> " " <> c }

-- | Set id
id :: forall i. String -> SearchInputProp i
id i props = props { id = Just i }

-- | Set name
name :: forall i. String -> SearchInputProp i
name n props = props { name = Just n }

-- | Set aria label
ariaLabel :: forall i. String -> SearchInputProp i
ariaLabel l props = props { ariaLabel = Just l }

-- | Set input handler
onInput :: forall i. (String -> i) -> SearchInputProp i
onInput handler props = props { onInput = Just handler }

-- | Set change handler
onChange :: forall i. (Event -> i) -> SearchInputProp i
onChange handler props = props { onChange = Just handler }

-- | Set clear handler
onClear :: forall i. i -> SearchInputProp i
onClear handler props = props { onClear = Just handler }

-- | Set submit handler
onSubmit :: forall i. (String -> i) -> SearchInputProp i
onSubmit handler props = props { onSubmit = Just handler }

-- | Set focus handler
onFocus :: forall i. (FocusEvent -> i) -> SearchInputProp i
onFocus handler props = props { onFocus = Just handler }

-- | Set blur handler
onBlur :: forall i. (FocusEvent -> i) -> SearchInputProp i
onBlur handler props = props { onBlur = Just handler }

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
  "w-full rounded-md border border-input bg-background ring-offset-background placeholder:text-muted-foreground focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2 disabled:cursor-not-allowed disabled:opacity-50"

-- | Icon container classes (left side)
iconContainerClasses :: String
iconContainerClasses =
  "absolute left-0 flex items-center justify-center text-muted-foreground pointer-events-none"

-- | Button container classes (right side)
buttonContainerClasses :: String
buttonContainerClasses =
  "absolute right-0 flex items-center"

-- | Clear/submit button classes
buttonClasses :: String
buttonClasses =
  "flex items-center justify-center text-muted-foreground hover:text-foreground focus:outline-none transition-colors"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Full search input component
searchInput :: forall w i. Array (SearchInputProp i) -> HH.HTML w i
searchInput propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    sizes = sizeClasses props.size
    
    -- Has value for showing clear button
    hasValue = String.length props.value > 0
    
    -- Input handlers
    inputHandlers = case props.onInput of
      Just handler -> [ HE.onValueInput handler ]
      Nothing -> []
    
    changeHandlers = case props.onChange of
      Just handler -> [ HE.onChange handler ]
      Nothing -> []
    
    focusHandlers = case props.onFocus of
      Just handler -> [ HE.onFocus handler ]
      Nothing -> []
    
    blurHandlers = case props.onBlur of
      Just handler -> [ HE.onBlur handler ]
      Nothing -> []
    
    keyHandlers = case props.onSubmit of
      Just handler -> 
        [ HE.onKeyDown (\e -> 
            if KE.key e == "Enter"
              then handler props.value
              else handler ""
          )
        ]
      Nothing -> []
    
    -- Clear handler
    clearHandler = case props.onClear of
      Just handler -> [ HE.onClick (\_ -> handler) ]
      Nothing -> []
    
    -- Submit handler
    submitHandler = case props.onSubmit of
      Just handler -> [ HE.onClick (\_ -> handler props.value) ]
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
      Nothing -> [ ARIA.label "Search" ]
    
    -- Icon sizing based on size
    iconContainerSize = case props.size of
      Small -> "w-8"
      Medium -> "w-10"
      Large -> "w-12"
    
    buttonSize = case props.size of
      Small -> "w-8 h-8"
      Medium -> "w-10 h-10"
      Large -> "w-12 h-12"
  in
    HH.div
      [ cls [ containerClasses, sizes.container, props.className ]
      , ARIA.role "search"
      ]
      [ -- Search icon or loading spinner
        HH.div
          [ cls [ iconContainerClasses, iconContainerSize, sizes.container ] ]
          [ if props.loading
              then spinnerIcon sizes.icon
              else searchIcon sizes.icon
          ]
      -- Input field
      , HH.input
          ( [ cls [ inputClasses, sizes.input ]
            , HP.type_ HP.InputSearch
            , HP.value props.value
            , HP.placeholder props.placeholder
            , HP.disabled props.disabled
            ] 
            <> idAttr 
            <> nameAttr 
            <> ariaLabelAttr
            <> inputHandlers 
            <> changeHandlers
            <> focusHandlers
            <> blurHandlers
            <> keyHandlers
          )
      -- Right side buttons
      , HH.div
          [ cls [ buttonContainerClasses ] ]
          ( -- Clear button
            ( if props.showClear && hasValue && not props.disabled
                then 
                  [ HH.button
                      ( [ cls [ buttonClasses, buttonSize ]
                        , HP.type_ HP.ButtonButton
                        , ARIA.label "Clear search"
                        ] <> clearHandler
                      )
                      [ clearIcon sizes.icon ]
                  ]
                else []
            )
            <>
            -- Submit button
            ( if props.showSubmit && not props.disabled
                then
                  [ HH.button
                      ( [ cls [ buttonClasses, buttonSize ]
                        , HP.type_ HP.ButtonButton
                        , ARIA.label "Submit search"
                        ] <> submitHandler
                      )
                      [ arrowRightIcon sizes.icon ]
                  ]
                else []
            )
          )
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // icons
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Search (magnifying glass) icon
searchIcon :: forall w i. String -> HH.HTML w i
searchIcon sizeClass =
  HH.element (HH.ElemName "svg")
    [ cls [ sizeClass ]
    , HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , HP.attr (HH.AttrName "stroke-linejoin") "round"
    ]
    [ HH.element (HH.ElemName "circle")
        [ HP.attr (HH.AttrName "cx") "11"
        , HP.attr (HH.AttrName "cy") "11"
        , HP.attr (HH.AttrName "r") "8"
        ]
        []
    , HH.element (HH.ElemName "line")
        [ HP.attr (HH.AttrName "x1") "21"
        , HP.attr (HH.AttrName "y1") "21"
        , HP.attr (HH.AttrName "x2") "16.65"
        , HP.attr (HH.AttrName "y2") "16.65"
        ]
        []
    ]

-- | Clear (X) icon
clearIcon :: forall w i. String -> HH.HTML w i
clearIcon sizeClass =
  HH.element (HH.ElemName "svg")
    [ cls [ sizeClass ]
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

-- | Arrow right icon
arrowRightIcon :: forall w i. String -> HH.HTML w i
arrowRightIcon sizeClass =
  HH.element (HH.ElemName "svg")
    [ cls [ sizeClass ]
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
    , HH.element (HH.ElemName "polyline")
        [ HP.attr (HH.AttrName "points") "12 5 19 12 12 19" ]
        []
    ]

-- | Loading spinner icon
spinnerIcon :: forall w i. String -> HH.HTML w i
spinnerIcon sizeClass =
  HH.element (HH.ElemName "svg")
    [ cls [ sizeClass, "animate-spin" ]
    , HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    ]
    [ HH.element (HH.ElemName "circle")
        [ cls [ "opacity-25" ]
        , HP.attr (HH.AttrName "cx") "12"
        , HP.attr (HH.AttrName "cy") "12"
        , HP.attr (HH.AttrName "r") "10"
        , HP.attr (HH.AttrName "stroke") "currentColor"
        , HP.attr (HH.AttrName "stroke-width") "4"
        ]
        []
    , HH.element (HH.ElemName "path")
        [ cls [ "opacity-75" ]
        , HP.attr (HH.AttrName "fill") "currentColor"
        , HP.attr (HH.AttrName "d") "M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4zm2 5.291A7.962 7.962 0 014 12H0c0 3.042 1.135 5.824 3 7.938l3-2.647z"
        ]
        []
    ]
