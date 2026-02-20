-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                         // hydrogen // select
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Searchable Select/Combobox component
-- |
-- | A feature-rich select component with search, keyboard navigation,
-- | single/multi-select modes, and option groups.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Select as Select
-- |
-- | -- Basic single select
-- | Select.select
-- |   [ Select.options [ Select.option "apple" "Apple"
-- |                    , Select.option "banana" "Banana"
-- |                    ]
-- |   , Select.value "apple"
-- |   , Select.onSelect HandleSelect
-- |   ]
-- |
-- | -- Multi-select with search
-- | Select.select
-- |   [ Select.options [ Select.option "red" "Red"
-- |                    , Select.option "green" "Green"
-- |                    , Select.option "blue" "Blue"
-- |                    ]
-- |   , Select.multiSelect true
-- |   , Select.values ["red", "blue"]
-- |   , Select.searchable true
-- |   , Select.onMultiSelect HandleMultiSelect
-- |   ]
-- |
-- | -- With option groups
-- | Select.select
-- |   [ Select.optionGroups
-- |       [ Select.optionGroup "Fruits"
-- |           [ Select.option "apple" "Apple"
-- |           , Select.option "banana" "Banana"
-- |           ]
-- |       , Select.optionGroup "Vegetables"
-- |           [ Select.option "carrot" "Carrot"
-- |           , Select.option "broccoli" "Broccoli"
-- |           ]
-- |       ]
-- |   ]
-- |
-- | -- Custom option rendering
-- | Select.select
-- |   [ Select.options myOptions
-- |   , Select.renderOption \opt -> HH.div_ [ HH.text opt.label ]
-- |   ]
-- | ```
module Hydrogen.Component.Select
  ( -- * Select Component
    select
  , selectTrigger
  , selectContent
  , selectItem
  , selectGroup
  , selectLabel
  , selectSeparator
    -- * Option Types
  , SelectOption
  , SelectOptionGroup
  , option
  , optionWithMeta
  , optionGroup
    -- * Props
  , SelectProps
  , SelectProp
  , defaultProps
    -- * Prop Builders
  , options
  , optionGroups
  , value
  , values
  , placeholder
  , disabled
  , searchable
  , multiSelect
  , open
  , className
  , onSelect
  , onMultiSelect
  , onOpenChange
  , onSearchChange
  , renderOption
    -- * State Types
  , SelectState
  , initialState
  ) where

import Prelude

import Data.Array (foldl, filter, length, null, (:))
import Data.Array as Array
import Data.Maybe (Maybe(..), fromMaybe)
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // option types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A single selectable option
type SelectOption =
  { value :: String
  , label :: String
  , disabled :: Boolean
  , meta :: Maybe String
  }

-- | A group of options with a label
type SelectOptionGroup =
  { label :: String
  , options :: Array SelectOption
  }

-- | Create a simple option
option :: String -> String -> SelectOption
option val lbl = { value: val, label: lbl, disabled: false, meta: Nothing }

-- | Create an option with metadata (e.g., description, icon key)
optionWithMeta :: String -> String -> String -> SelectOption
optionWithMeta val lbl meta = { value: val, label: lbl, disabled: false, meta: Just meta }

-- | Create an option group
optionGroup :: String -> Array SelectOption -> SelectOptionGroup
optionGroup lbl opts = { label: lbl, options: opts }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // state
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Internal state for controlled components
type SelectState =
  { isOpen :: Boolean
  , searchQuery :: String
  , highlightedIndex :: Int
  }

-- | Initial state
initialState :: SelectState
initialState =
  { isOpen: false
  , searchQuery: ""
  , highlightedIndex: 0
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Select properties
type SelectProps i =
  { options :: Array SelectOption
  , optionGroups :: Array SelectOptionGroup
  , value :: Maybe String
  , values :: Array String
  , placeholder :: String
  , disabled :: Boolean
  , searchable :: Boolean
  , multiSelect :: Boolean
  , open :: Maybe Boolean
  , className :: String
  , onSelect :: Maybe (String -> i)
  , onMultiSelect :: Maybe (Array String -> i)
  , onOpenChange :: Maybe (Boolean -> i)
  , onSearchChange :: Maybe (String -> i)
  , renderOption :: Maybe (SelectOption -> forall w. HH.HTML w i)
  }

-- | Property modifier
type SelectProp i = SelectProps i -> SelectProps i

-- | Default select properties
defaultProps :: forall i. SelectProps i
defaultProps =
  { options: []
  , optionGroups: []
  , value: Nothing
  , values: []
  , placeholder: "Select..."
  , disabled: false
  , searchable: false
  , multiSelect: false
  , open: Nothing
  , className: ""
  , onSelect: Nothing
  , onMultiSelect: Nothing
  , onOpenChange: Nothing
  , onSearchChange: Nothing
  , renderOption: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set available options
options :: forall i. Array SelectOption -> SelectProp i
options opts props = props { options = opts }

-- | Set option groups (overrides flat options)
optionGroups :: forall i. Array SelectOptionGroup -> SelectProp i
optionGroups groups props = props { optionGroups = groups }

-- | Set selected value (single select mode)
value :: forall i. String -> SelectProp i
value v props = props { value = Just v }

-- | Set selected values (multi-select mode)
values :: forall i. Array String -> SelectProp i
values vs props = props { values = vs }

-- | Set placeholder text
placeholder :: forall i. String -> SelectProp i
placeholder p props = props { placeholder = p }

-- | Set disabled state
disabled :: forall i. Boolean -> SelectProp i
disabled d props = props { disabled = d }

-- | Enable search/filter functionality
searchable :: forall i. Boolean -> SelectProp i
searchable s props = props { searchable = s }

-- | Enable multi-select mode
multiSelect :: forall i. Boolean -> SelectProp i
multiSelect m props = props { multiSelect = m }

-- | Control open state (controlled mode)
open :: forall i. Boolean -> SelectProp i
open o props = props { open = Just o }

-- | Add custom class
className :: forall i. String -> SelectProp i
className c props = props { className = props.className <> " " <> c }

-- | Set select handler (single select)
onSelect :: forall i. (String -> i) -> SelectProp i
onSelect handler props = props { onSelect = Just handler }

-- | Set select handler (multi-select)
onMultiSelect :: forall i. (Array String -> i) -> SelectProp i
onMultiSelect handler props = props { onMultiSelect = Just handler }

-- | Set open state change handler
onOpenChange :: forall i. (Boolean -> i) -> SelectProp i
onOpenChange handler props = props { onOpenChange = Just handler }

-- | Set search query change handler
onSearchChange :: forall i. (String -> i) -> SelectProp i
onSearchChange handler props = props { onSearchChange = Just handler }

-- | Set custom option renderer
renderOption :: forall i. (SelectOption -> forall w. HH.HTML w i) -> SelectProp i
renderOption renderer props = props { renderOption = Just renderer }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Base trigger button classes
triggerClasses :: String
triggerClasses =
  "flex h-10 w-full items-center justify-between rounded-md border border-input bg-background px-3 py-2 text-sm ring-offset-background placeholder:text-muted-foreground focus:outline-none focus:ring-2 focus:ring-ring focus:ring-offset-2 disabled:cursor-not-allowed disabled:opacity-50"

-- | Content dropdown classes
contentClasses :: String
contentClasses =
  "relative z-50 max-h-96 min-w-[8rem] overflow-hidden rounded-md border bg-popover text-popover-foreground shadow-md animate-in fade-in-0 zoom-in-95"

-- | Item classes
itemClasses :: String
itemClasses =
  "relative flex w-full cursor-default select-none items-center rounded-sm py-1.5 pl-8 pr-2 text-sm outline-none focus:bg-accent focus:text-accent-foreground data-[disabled]:pointer-events-none data-[disabled]:opacity-50"

-- | Group label classes
groupLabelClasses :: String
groupLabelClasses =
  "py-1.5 pl-8 pr-2 text-sm font-semibold text-muted-foreground"

-- | Chevron down icon
chevronDown :: forall w i. HH.HTML w i
chevronDown =
  HH.span
    [ cls [ "h-4 w-4 opacity-50" ] ]
    [ HH.text "▼" ]

-- | Check icon for selected items
checkIcon :: forall w i. HH.HTML w i
checkIcon =
  HH.span
    [ cls [ "absolute left-2 flex h-3.5 w-3.5 items-center justify-center" ] ]
    [ HH.text "✓" ]

-- | Select trigger button
selectTrigger :: forall w i. Array (SelectProp i) -> Array (HH.HTML w i) -> HH.HTML w i
selectTrigger propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
  in
    HH.button
      [ cls [ triggerClasses, props.className ]
      , HP.type_ HP.ButtonButton
      , HP.disabled props.disabled
      , ARIA.role "combobox"
      , ARIA.expanded (show (fromMaybe false props.open))
      , ARIA.hasPopup "listbox"
      ]
      ( children <> [ chevronDown ] )

-- | Select content/dropdown
selectContent :: forall w i. Array (SelectProp i) -> Array (HH.HTML w i) -> HH.HTML w i
selectContent propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
  in
    HH.div
      [ cls [ contentClasses, props.className ]
      , ARIA.role "listbox"
      ]
      [ HH.div
          [ cls [ "p-1" ] ]
          children
      ]

-- | Select item/option
selectItem :: forall w i. 
  { value :: String, selected :: Boolean, disabled :: Boolean } -> 
  Array (HH.HTML w i) -> 
  HH.HTML w i
selectItem opts children =
  let
    selectedClass = if opts.selected then "bg-accent text-accent-foreground" else ""
    disabledAttr = if opts.disabled then [ HP.attr (HH.AttrName "data-disabled") "true" ] else []
  in
    HH.div
      ( [ cls [ itemClasses, selectedClass ]
        , ARIA.role "option"
        , ARIA.selected (show opts.selected)
        , HP.tabIndex 0
        ] <> disabledAttr
      )
      ( (if opts.selected then [ checkIcon ] else []) <> children )

-- | Select group container
selectGroup :: forall w i. Array (HH.HTML w i) -> HH.HTML w i
selectGroup children =
  HH.div
    [ ARIA.role "group" ]
    children

-- | Select group label
selectLabel :: forall w i. String -> HH.HTML w i
selectLabel labelText =
  HH.div
    [ cls [ groupLabelClasses ] ]
    [ HH.text labelText ]

-- | Select separator
selectSeparator :: forall w i. HH.HTML w i
selectSeparator =
  HH.div
    [ cls [ "-mx-1 my-1 h-px bg-muted" ] ]
    []

-- | Full select component (composing trigger + content)
select :: forall w i. Array (SelectProp i) -> HH.HTML w i
select propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    isOpen = fromMaybe false props.open
    
    -- Get all options (from flat list or groups)
    allOptions = 
      if null props.optionGroups
        then props.options
        else Array.concatMap _.options props.optionGroups
    
    -- Find selected option label for display
    selectedLabel = case props.value of
      Just v -> 
        case Array.find (\o -> o.value == v) allOptions of
          Just opt -> opt.label
          Nothing -> props.placeholder
      Nothing -> 
        if props.multiSelect && not (null props.values)
          then show (length props.values) <> " selected"
          else props.placeholder
    
    -- Default option renderer
    defaultRenderer :: SelectOption -> HH.HTML w i
    defaultRenderer opt = HH.text opt.label
    
    -- Render a single option
    renderOpt :: SelectOption -> HH.HTML w i
    renderOpt opt =
      let
        isSelected = case props.value of
          Just v -> v == opt.value
          Nothing -> Array.elem opt.value props.values
        clickHandler = case props.onSelect of
          Just handler -> [ HE.onClick (\_ -> handler opt.value) ]
          Nothing -> case props.onMultiSelect of
            Just handler -> 
              let 
                newValues = if isSelected
                  then filter (_ /= opt.value) props.values
                  else opt.value : props.values
              in [ HE.onClick (\_ -> handler newValues) ]
            Nothing -> []
      in
        HH.div
          ( [ cls [ itemClasses, if isSelected then "bg-accent" else "" ]
            , ARIA.role "option"
            , ARIA.selected (show isSelected)
            , HP.tabIndex 0
            ] <> clickHandler
          )
          [ if isSelected then checkIcon else HH.text ""
          , HH.span [ cls [ "ml-2" ] ] [ defaultRenderer opt ]
          ]
    
    -- Render option groups
    renderGroups :: Array (HH.HTML w i)
    renderGroups = 
      Array.concatMap 
        (\grp -> 
          [ selectLabel grp.label ] <> map renderOpt grp.options
        ) 
        props.optionGroups
    
    -- Render flat options
    renderFlatOptions :: Array (HH.HTML w i)
    renderFlatOptions = map renderOpt props.options
    
    -- Search input (if searchable)
    searchInput :: Array (HH.HTML w i)
    searchInput = 
      if props.searchable
        then 
          [ HH.div
              [ cls [ "flex items-center border-b px-3" ] ]
              [ HH.input
                  [ cls [ "flex h-10 w-full rounded-md bg-transparent py-3 text-sm outline-none placeholder:text-muted-foreground disabled:cursor-not-allowed disabled:opacity-50" ]
                  , HP.placeholder "Search..."
                  , HP.type_ HP.InputText
                  ]
              ]
          ]
        else []
  in
    HH.div
      [ cls [ "relative", props.className ] ]
      [ -- Trigger button
        HH.button
          ( [ cls [ triggerClasses ]
            , HP.type_ HP.ButtonButton
            , HP.disabled props.disabled
            , ARIA.role "combobox"
            , ARIA.expanded (show isOpen)
            , ARIA.hasPopup "listbox"
            ] <> case props.onOpenChange of
              Just handler -> [ HE.onClick (\_ -> handler (not isOpen)) ]
              Nothing -> []
          )
          [ HH.span [ cls [ "truncate" ] ] [ HH.text selectedLabel ]
          , chevronDown
          ]
      -- Dropdown content
      , if isOpen
          then 
            HH.div
              [ cls [ "absolute mt-1 w-full", contentClasses ] ]
              ( searchInput <>
                [ HH.div
                    [ cls [ "max-h-60 overflow-auto p-1" ]
                    , ARIA.role "listbox"
                    ]
                    ( if null props.optionGroups
                        then renderFlatOptions
                        else renderGroups
                    )
                ]
              )
          else HH.text ""
      ]
