-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // hydrogen // autocomplete
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | AutoComplete/Combobox component
-- |
-- | A text input with autocomplete suggestions dropdown.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.AutoComplete as AC
-- |
-- | -- Basic autocomplete
-- | AC.autoComplete
-- |   [ AC.suggestions [ "Apple", "Apricot", "Avocado", "Banana" ]
-- |   , AC.value state.query
-- |   , AC.onInput HandleInput
-- |   , AC.onSelect HandleSelect
-- |   ]
-- |
-- | -- With custom suggestion rendering
-- | AC.autoComplete
-- |   [ AC.suggestionsWithData users
-- |   , AC.renderSuggestion \user -> HH.div_ [ HH.text user.name ]
-- |   , AC.onSelectData HandleUserSelect
-- |   ]
-- |
-- | -- Async loading
-- | AC.autoComplete
-- |   [ AC.suggestions filteredResults
-- |   , AC.loading isSearching
-- |   , AC.onInput HandleSearch
-- |   ]
-- | ```
module Hydrogen.Component.AutoComplete
  ( -- * AutoComplete Component
    autoComplete
  , autoCompleteInput
  , suggestionsList
  , suggestionItem
    -- * Suggestion Types
  , Suggestion
  , suggestion
  , suggestionWithMeta
    -- * Props
  , AutoCompleteProps
  , AutoCompleteProp
  , defaultProps
    -- * Prop Builders
  , suggestions
  , suggestionsWithData
  , value
  , placeholder
  , disabled
  , loading
  , open
  , highlightedIndex
  , minChars
  , maxSuggestions
  , debounceMs
  , clearOnSelect
  , className
  , onInput
  , onSelect
  , onSelectData
  , onOpenChange
  , onHighlightChange
  , renderSuggestion
  , noResultsText
  , loadingText
  ) where

import Prelude

import Data.Array (foldl, take, mapWithIndex)
import Data.Array as Array
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String as String
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // suggestion types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A suggestion with value, label, and optional metadata
type Suggestion a =
  { value :: String
  , label :: String
  , data :: Maybe a
  , disabled :: Boolean
  }

-- | Create a simple string suggestion
suggestion :: String -> Suggestion Unit
suggestion s = { value: s, label: s, data: Nothing, disabled: false }

-- | Create a suggestion with attached data
suggestionWithMeta :: forall a. String -> String -> a -> Suggestion a
suggestionWithMeta val lbl d = 
  { value: val, label: lbl, data: Just d, disabled: false }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | AutoComplete properties
type AutoCompleteProps a i =
  { suggestions :: Array (Suggestion a)
  , value :: String
  , placeholder :: String
  , disabled :: Boolean
  , loading :: Boolean
  , open :: Maybe Boolean
  , highlightedIndex :: Int
  , minChars :: Int
  , maxSuggestions :: Int
  , debounceMs :: Int
  , clearOnSelect :: Boolean
  , className :: String
  , onInput :: Maybe (String -> i)
  , onSelect :: Maybe (String -> i)
  , onSelectData :: Maybe (Suggestion a -> i)
  , onOpenChange :: Maybe (Boolean -> i)
  , onHighlightChange :: Maybe (Int -> i)
  , renderSuggestion :: Maybe (Suggestion a -> forall w. HH.HTML w i)
  , noResultsText :: String
  , loadingText :: String
  }

-- | Property modifier
type AutoCompleteProp a i = AutoCompleteProps a i -> AutoCompleteProps a i

-- | Default autocomplete properties
defaultProps :: forall a i. AutoCompleteProps a i
defaultProps =
  { suggestions: []
  , value: ""
  , placeholder: "Search..."
  , disabled: false
  , loading: false
  , open: Nothing
  , highlightedIndex: 0
  , minChars: 1
  , maxSuggestions: 10
  , debounceMs: 150
  , clearOnSelect: false
  , className: ""
  , onInput: Nothing
  , onSelect: Nothing
  , onSelectData: Nothing
  , onOpenChange: Nothing
  , onHighlightChange: Nothing
  , renderSuggestion: Nothing
  , noResultsText: "No results found"
  , loadingText: "Loading..."
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set suggestions from simple strings
suggestions :: forall a i. Array String -> AutoCompleteProp a i
suggestions strs props = props 
  { suggestions = map (\s -> { value: s, label: s, data: Nothing, disabled: false }) strs }

-- | Set suggestions with custom data
suggestionsWithData :: forall a i. Array (Suggestion a) -> AutoCompleteProp a i
suggestionsWithData sugs props = props { suggestions = sugs }

-- | Set current input value
value :: forall a i. String -> AutoCompleteProp a i
value v props = props { value = v }

-- | Set placeholder text
placeholder :: forall a i. String -> AutoCompleteProp a i
placeholder p props = props { placeholder = p }

-- | Set disabled state
disabled :: forall a i. Boolean -> AutoCompleteProp a i
disabled d props = props { disabled = d }

-- | Set loading state
loading :: forall a i. Boolean -> AutoCompleteProp a i
loading l props = props { loading = l }

-- | Control open state (controlled mode)
open :: forall a i. Boolean -> AutoCompleteProp a i
open o props = props { open = Just o }

-- | Set highlighted suggestion index
highlightedIndex :: forall a i. Int -> AutoCompleteProp a i
highlightedIndex idx props = props { highlightedIndex = idx }

-- | Set minimum characters before showing suggestions
minChars :: forall a i. Int -> AutoCompleteProp a i
minChars n props = props { minChars = n }

-- | Set maximum suggestions to display
maxSuggestions :: forall a i. Int -> AutoCompleteProp a i
maxSuggestions n props = props { maxSuggestions = n }

-- | Set debounce delay in milliseconds
debounceMs :: forall a i. Int -> AutoCompleteProp a i
debounceMs ms props = props { debounceMs = ms }

-- | Clear input on selection
clearOnSelect :: forall a i. Boolean -> AutoCompleteProp a i
clearOnSelect c props = props { clearOnSelect = c }

-- | Add custom class
className :: forall a i. String -> AutoCompleteProp a i
className c props = props { className = props.className <> " " <> c }

-- | Set input change handler
onInput :: forall a i. (String -> i) -> AutoCompleteProp a i
onInput handler props = props { onInput = Just handler }

-- | Set selection handler (value only)
onSelect :: forall a i. (String -> i) -> AutoCompleteProp a i
onSelect handler props = props { onSelect = Just handler }

-- | Set selection handler (full suggestion with data)
onSelectData :: forall a i. (Suggestion a -> i) -> AutoCompleteProp a i
onSelectData handler props = props { onSelectData = Just handler }

-- | Set open state change handler
onOpenChange :: forall a i. (Boolean -> i) -> AutoCompleteProp a i
onOpenChange handler props = props { onOpenChange = Just handler }

-- | Set highlight change handler (for keyboard navigation)
onHighlightChange :: forall a i. (Int -> i) -> AutoCompleteProp a i
onHighlightChange handler props = props { onHighlightChange = Just handler }

-- | Set custom suggestion renderer
renderSuggestion :: forall a i. (Suggestion a -> forall w. HH.HTML w i) -> AutoCompleteProp a i
renderSuggestion renderer props = props { renderSuggestion = Just renderer }

-- | Set text shown when no results
noResultsText :: forall a i. String -> AutoCompleteProp a i
noResultsText t props = props { noResultsText = t }

-- | Set text shown while loading
loadingText :: forall a i. String -> AutoCompleteProp a i
loadingText t props = props { loadingText = t }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // styling
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Input base classes
inputClasses :: String
inputClasses =
  "flex h-10 w-full rounded-md border border-input bg-background px-3 py-2 text-sm ring-offset-background placeholder:text-muted-foreground focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2 disabled:cursor-not-allowed disabled:opacity-50"

-- | Dropdown container classes
dropdownClasses :: String
dropdownClasses =
  "absolute z-50 mt-1 w-full max-h-60 overflow-auto rounded-md border bg-popover text-popover-foreground shadow-md animate-in fade-in-0 zoom-in-95"

-- | Suggestion item classes
itemClasses :: String
itemClasses =
  "relative flex cursor-default select-none items-center rounded-sm px-2 py-1.5 text-sm outline-none"

-- | Highlighted item classes
highlightedClasses :: String
highlightedClasses =
  "bg-accent text-accent-foreground"

-- | Disabled item classes  
disabledClasses :: String
disabledClasses =
  "pointer-events-none opacity-50"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | AutoComplete input field (standalone)
autoCompleteInput :: forall w a i. Array (AutoCompleteProp a i) -> HH.HTML w i
autoCompleteInput propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    inputHandler = case props.onInput of
      Just handler -> [ HE.onValueInput handler ]
      Nothing -> []
  in
    HH.input
      ( [ cls [ inputClasses, props.className ]
        , HP.type_ HP.InputText
        , HP.placeholder props.placeholder
        , HP.value props.value
        , HP.disabled props.disabled
        , HP.autocomplete HP.AutocompleteOff
        , ARIA.role "combobox"
        , ARIA.expanded (show (fromMaybe false props.open))
        , ARIA.hasPopup "listbox"
        , ARIA.autoComplete "list"
        ] <> inputHandler
      )

-- | Suggestions list (standalone)
suggestionsList :: forall w i. Array (HH.HTML w i) -> HH.HTML w i
suggestionsList children =
  HH.ul
    [ cls [ dropdownClasses ]
    , ARIA.role "listbox"
    ]
    children

-- | Individual suggestion item (standalone)
suggestionItem :: forall w i. 
  { highlighted :: Boolean, disabled :: Boolean } -> 
  Array (HH.HTML w i) -> 
  HH.HTML w i
suggestionItem opts children =
  let
    stateClasses = 
      (if opts.highlighted then highlightedClasses else "") <>
      (if opts.disabled then " " <> disabledClasses else "")
  in
    HH.li
      [ cls [ itemClasses, stateClasses ]
      , ARIA.role "option"
      , ARIA.selected (show opts.highlighted)
      , HP.tabIndex (-1)
      ]
      children

-- | Full AutoComplete component
autoComplete :: forall w a i. Array (AutoCompleteProp a i) -> HH.HTML w i
autoComplete propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    isOpen = fromMaybe false props.open
    
    -- Filter suggestions based on value
    filteredSuggestions = 
      take props.maxSuggestions props.suggestions
    
    -- Determine if dropdown should show
    shouldShowDropdown = 
      isOpen && 
      String.length props.value >= props.minChars &&
      not props.disabled
    
    -- Default suggestion renderer
    defaultRenderer :: Suggestion a -> HH.HTML w i
    defaultRenderer sug = HH.text sug.label
    
    -- Render a suggestion
    renderSug :: Int -> Suggestion a -> HH.HTML w i
    renderSug idx sug =
      let
        isHighlighted = idx == props.highlightedIndex
        clickHandler = case props.onSelectData of
          Just handler -> [ HE.onClick (\_ -> handler sug) ]
          Nothing -> case props.onSelect of
            Just handler -> [ HE.onClick (\_ -> handler sug.value) ]
            Nothing -> []
      in
        HH.li
          ( [ cls 
                [ itemClasses
                , if isHighlighted then highlightedClasses else ""
                , if sug.disabled then disabledClasses else ""
                ]
            , ARIA.role "option"
            , ARIA.selected (show isHighlighted)
            , HP.tabIndex (-1)
            ] <> clickHandler
          )
          [ defaultRenderer sug ]
    
    -- Input event handlers
    inputHandlers = 
      case props.onInput of
        Just handler -> [ HE.onValueInput handler ]
        Nothing -> []
    
    focusHandlers = case props.onOpenChange of
      Just handler -> 
        [ HE.onFocus (\_ -> handler true)
        , HE.onBlur (\_ -> handler false)
        ]
      Nothing -> []
    
    -- Loading indicator
    loadingIndicator :: HH.HTML w i
    loadingIndicator =
      HH.li
        [ cls [ "px-2 py-1.5 text-sm text-muted-foreground" ] ]
        [ HH.div
            [ cls [ "flex items-center gap-2" ] ]
            [ spinner
            , HH.text props.loadingText
            ]
        ]
    
    -- No results message
    noResults :: HH.HTML w i
    noResults =
      HH.li
        [ cls [ "px-2 py-1.5 text-sm text-muted-foreground text-center" ] ]
        [ HH.text props.noResultsText ]
    
    -- Dropdown content
    dropdownContent :: Array (HH.HTML w i)
    dropdownContent =
      if props.loading
        then [ loadingIndicator ]
        else if Array.length filteredSuggestions == 0
          then [ noResults ]
          else mapWithIndex renderSug filteredSuggestions
  in
    HH.div
      [ cls [ "relative", props.className ] ]
      [ -- Input field
        HH.input
          ( [ cls [ inputClasses ]
            , HP.type_ HP.InputText
            , HP.placeholder props.placeholder
            , HP.value props.value
            , HP.disabled props.disabled
            , HP.autocomplete HP.AutocompleteOff
            , ARIA.role "combobox"
            , ARIA.expanded (show shouldShowDropdown)
            , ARIA.hasPopup "listbox"
            , ARIA.autoComplete "list"
            ] <> inputHandlers <> focusHandlers
          )
      -- Dropdown
      , if shouldShowDropdown
          then 
            HH.ul
              [ cls [ dropdownClasses ]
              , ARIA.role "listbox"
              ]
              dropdownContent
          else HH.text ""
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Small loading spinner
spinner :: forall w i. HH.HTML w i
spinner =
  HH.element (HH.ElemName "svg")
    [ cls [ "animate-spin h-4 w-4" ]
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
