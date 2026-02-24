-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                        // hydrogen // command
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Command Palette component (⌘K)
-- |
-- | Accessible command palette with fuzzy search, keyboard navigation,
-- | command groups, and nested pages. Follows the ARIA combobox pattern.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Primitive.Command as Command
-- |
-- | Command.commandPalette [ Command.open state.isOpen ]
-- |   [ Command.commandInput
-- |       [ Command.placeholder "Type a command..."
-- |       , Command.onInput HandleInput
-- |       , Command.value state.search
-- |       ]
-- |   , Command.commandList []
-- |       [ Command.commandGroup [ Command.heading "Recent" ]
-- |           [ Command.commandItem
-- |               [ Command.onSelect (HandleCommand "open-file")
-- |               , Command.icon fileIcon
-- |               , Command.shortcut "⌘O"
-- |               ]
-- |               [ HH.text "Open File" ]
-- |           ]
-- |       , Command.commandGroup [ Command.heading "Actions" ]
-- |           [ Command.commandItem [ Command.onSelect (HandleCommand "save") ]
-- |               [ HH.text "Save" ]
-- |           , Command.commandItem [ Command.disabled true ]
-- |               [ HH.text "Delete" ]
-- |           ]
-- |       , Command.commandEmpty []
-- |           [ HH.text "No results found." ]
-- |       ]
-- |   ]
-- | ```
-- |
-- | ## Keyboard Navigation
-- |
-- | - `↑/↓` - Navigate between items
-- | - `Enter` - Select focused item
-- | - `Escape` - Close palette
-- | - `⌘K` / `Ctrl+K` - Global shortcut to open
-- |
-- | ## Nested Pages
-- |
-- | ```purescript
-- | Command.commandItem [ Command.onSelect (NavigateTo "theme") ]
-- |   [ HH.text "Change Theme →" ]
-- |
-- | -- In your state, track current page and render appropriate items
-- | ```
-- |
-- | ## Loading State
-- |
-- | ```purescript
-- | Command.commandLoading []
-- |   [ HH.text "Searching..." ]
-- | ```
module Hydrogen.Primitive.Command
  ( -- * Command Palette Components
    commandPalette
  , commandDialog
  , commandInput
  , commandList
  , commandEmpty
  , commandLoading
  , commandGroup
  , commandSeparator
  , commandItem
  , commandShortcut
    -- * Props
  , CommandProps
  , CommandProp
  , open
  , onClose
  , onInput
  , onSelect
  , onKeyDown
  , value
  , placeholder
  , heading
  , hasIcon
  , shortcut
  , description
  , disabled
  , selected
  , className
    -- * Keyboard Handler FFI
  , registerGlobalShortcut
  , unregisterGlobalShortcut
    -- * Fuzzy Search
  , fuzzyMatch
  , fuzzyScore
  ) where

import Prelude

import Data.Array (foldl)
import Data.Maybe (Maybe(Just, Nothing))
import Data.String as String
import Data.String.Pattern (Pattern(Pattern))
import Effect (Effect)
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)
import Web.UIEvent.MouseEvent (MouseEvent)
import Web.UIEvent.KeyboardEvent (KeyboardEvent)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Command palette properties
type CommandProps i =
  { open :: Boolean
  , onClose :: Maybe (MouseEvent -> i)
  , onInput :: Maybe (String -> i)
  , onSelect :: Maybe (MouseEvent -> i)
  , onKeyDown :: Maybe (KeyboardEvent -> i)
  , value :: String
  , placeholder :: String
  , heading :: String
  , hasIcon :: Boolean
  , shortcut :: String
  , description :: String
  , disabled :: Boolean
  , selected :: Boolean
  , className :: String
  }

type CommandProp i = CommandProps i -> CommandProps i

defaultProps :: forall i. CommandProps i
defaultProps =
  { open: false
  , onClose: Nothing
  , onInput: Nothing
  , onSelect: Nothing
  , onKeyDown: Nothing
  , value: ""
  , placeholder: "Type a command or search..."
  , heading: ""
  , hasIcon: false
  , shortcut: ""
  , description: ""
  , disabled: false
  , selected: false
  , className: ""
  }

-- | Set open state
open :: forall i. Boolean -> CommandProp i
open o props = props { open = o }

-- | Set close handler
onClose :: forall i. (MouseEvent -> i) -> CommandProp i
onClose handler props = props { onClose = Just handler }

-- | Set input change handler
onInput :: forall i. (String -> i) -> CommandProp i
onInput handler props = props { onInput = Just handler }

-- | Set item select handler
onSelect :: forall i. (MouseEvent -> i) -> CommandProp i
onSelect handler props = props { onSelect = Just handler }

-- | Set keyboard handler (exported for keyboard navigation)
onKeyDown :: forall i. (KeyboardEvent -> i) -> CommandProp i
onKeyDown handler props = props { onKeyDown = Just handler }

-- | Set input value
value :: forall i. String -> CommandProp i
value v props = props { value = v }

-- | Set input placeholder
placeholder :: forall i. String -> CommandProp i
placeholder p props = props { placeholder = p }

-- | Set group heading
heading :: forall i. String -> CommandProp i
heading h props = props { heading = h }

-- | Mark item as having an icon (icon provided as first child)
hasIcon :: forall i. Boolean -> CommandProp i
hasIcon b props = props { hasIcon = b }

-- | Set keyboard shortcut badge
shortcut :: forall i. String -> CommandProp i
shortcut s props = props { shortcut = s }

-- | Set item description
description :: forall i. String -> CommandProp i
description d props = props { description = d }

-- | Set disabled state
disabled :: forall i. Boolean -> CommandProp i
disabled d props = props { disabled = d }

-- | Set selected/highlighted state
selected :: forall i. Boolean -> CommandProp i
selected s props = props { selected = s }

-- | Add custom class
className :: forall i. String -> CommandProp i
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Command palette root container
-- |
-- | This is the main container that renders the palette in a fixed overlay.
-- | Use `commandDialog` for the inner content area.
commandPalette :: forall w i. Array (CommandProp i) -> Array (HH.HTML w i) -> HH.HTML w i
commandPalette propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in if props.open
    then HH.div
      [ cls [ "fixed inset-0 z-50", props.className ]
      , ARIA.role "dialog"
      , ARIA.modal "true"
      , HP.attr (HH.AttrName "data-state") "open"
      ]
      [ -- Backdrop
        HH.div
          ( [ cls [ "fixed inset-0 bg-black/50 backdrop-blur-sm animate-in fade-in-0" ] ]
            <> case props.onClose of
              Just handler -> [ HE.onClick handler ]
              Nothing -> []
          )
          []
      , -- Dialog container (centered)
        HH.div
          [ cls [ "fixed inset-0 flex items-start justify-center pt-[15vh]" ] ]
          children
      ]
    else HH.text ""

-- | Command dialog content panel
-- |
-- | The floating dialog containing the search input and command list.
commandDialog :: forall w i. Array (CommandProp i) -> Array (HH.HTML w i) -> HH.HTML w i
commandDialog propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "relative w-full max-w-lg overflow-hidden rounded-xl border bg-popover shadow-2xl animate-in fade-in-0 zoom-in-95 slide-in-from-top-2", props.className ]
    , ARIA.role "combobox"
    , ARIA.expanded "true"
    , ARIA.hasPopup "listbox"
    ]
    children

-- | Command search input
-- |
-- | The search field at the top of the palette.
commandInput :: forall w i. Array (CommandProp i) -> HH.HTML w i
commandInput propMods =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "flex items-center border-b px-3", props.className ] ]
    [ -- Search icon
      searchIcon
    , HH.input
        ( [ cls [ "flex h-12 w-full rounded-md bg-transparent py-3 text-sm outline-none placeholder:text-muted-foreground disabled:cursor-not-allowed disabled:opacity-50" ]
          , HP.type_ HP.InputText
          , HP.placeholder props.placeholder
          , HP.value props.value
          , HP.attr (HH.AttrName "autocomplete") "off"
          , HP.attr (HH.AttrName "autocorrect") "off"
          , HP.attr (HH.AttrName "spellcheck") "false"
          , ARIA.role "combobox"
          , ARIA.expanded "true"
          , ARIA.controls "command-list"
          , ARIA.autoComplete "list"
          ] <> case props.onInput of
            Just handler -> [ HE.onValueInput handler ]
            Nothing -> []
        )
    ]

-- | Command list container
-- |
-- | Wraps all command groups and items. Provides scrolling for long lists.
commandList :: forall w i. Array (CommandProp i) -> Array (HH.HTML w i) -> HH.HTML w i
commandList propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "max-h-[300px] overflow-y-auto overflow-x-hidden p-2", props.className ]
    , HP.id "command-list"
    , ARIA.role "listbox"
    ]
    children

-- | Empty state when no results found
commandEmpty :: forall w i. Array (CommandProp i) -> Array (HH.HTML w i) -> HH.HTML w i
commandEmpty propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "py-6 text-center text-sm text-muted-foreground", props.className ] ]
    children

-- | Loading state for async commands
commandLoading :: forall w i. Array (CommandProp i) -> Array (HH.HTML w i) -> HH.HTML w i
commandLoading propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "flex items-center justify-center py-6 gap-2 text-sm text-muted-foreground", props.className ] ]
    [ spinnerIcon
    , HH.span_ children
    ]

-- | Command group with heading
-- |
-- | Groups related commands under a heading.
commandGroup :: forall w i. Array (CommandProp i) -> Array (HH.HTML w i) -> HH.HTML w i
commandGroup propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "overflow-hidden py-2", props.className ]
    , ARIA.role "group"
    ]
    ( (if props.heading /= ""
        then [ HH.div
                [ cls [ "px-2 py-1.5 text-xs font-medium text-muted-foreground" ] ]
                [ HH.text props.heading ]
             ]
        else [])
      <> children
    )

-- | Separator between groups
commandSeparator :: forall w i. Array (CommandProp i) -> HH.HTML w i
commandSeparator propMods =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "-mx-2 h-px bg-border", props.className ]
    , ARIA.role "separator"
    ]
    []

-- | Command item
-- |
-- | An individual selectable command with optional icon, shortcut, and description.
-- | If `hasIcon true` is set, the first child is treated as the icon and wrapped
-- | in an icon container.
commandItem :: forall w i. Array (CommandProp i) -> Array (HH.HTML w i) -> HH.HTML w i
commandItem propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    disabledClasses = if props.disabled
      then "opacity-50 pointer-events-none"
      else "cursor-pointer"
    selectedClasses = if props.selected
      then "bg-accent text-accent-foreground"
      else ""
  in
    HH.div
      ( [ cls [ "relative flex cursor-default select-none items-center rounded-sm px-2 py-1.5 text-sm outline-none transition-colors hover:bg-accent hover:text-accent-foreground aria-selected:bg-accent aria-selected:text-accent-foreground", disabledClasses, selectedClasses, props.className ]
        , ARIA.role "option"
        , ARIA.selected (if props.selected then "true" else "false")
        , ARIA.disabled (if props.disabled then "true" else "false")
        , HP.attr (HH.AttrName "data-disabled") (if props.disabled then "true" else "false")
        ] <> case props.onSelect of
          Just handler | not props.disabled -> [ HE.onClick handler ]
          _ -> []
      )
      ( -- Content: children directly (icon can be passed as first child)
        [ HH.span [ cls [ "flex items-center flex-1 gap-2" ] ]
            ( children
              <> if props.description /= ""
                then [ HH.span
                        [ cls [ "ml-2 text-muted-foreground text-xs" ] ]
                        [ HH.text props.description ]
                     ]
                else []
            )
        ]
        -- Shortcut badge (if provided)
        <> if props.shortcut /= ""
          then [ commandShortcut [] [ HH.text props.shortcut ] ]
          else []
      )

-- | Keyboard shortcut badge
-- |
-- | Displays keyboard shortcuts inline with command items.
commandShortcut :: forall w i. Array (CommandProp i) -> Array (HH.HTML w i) -> HH.HTML w i
commandShortcut propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.kbd
    [ cls [ "pointer-events-none ml-auto inline-flex h-5 select-none items-center gap-1 rounded border bg-muted px-1.5 font-mono text-[10px] font-medium text-muted-foreground opacity-100", props.className ] ]
    children

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // icons
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Search icon for input
searchIcon :: forall w i. HH.HTML w i
searchIcon =
  HH.elementNS
    (HH.Namespace "http://www.w3.org/2000/svg")
    (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "class") "mr-2 h-4 w-4 shrink-0 opacity-50"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , HP.attr (HH.AttrName "stroke-linejoin") "round"
    ]
    [ HH.elementNS
        (HH.Namespace "http://www.w3.org/2000/svg")
        (HH.ElemName "circle")
        [ HP.attr (HH.AttrName "cx") "11"
        , HP.attr (HH.AttrName "cy") "11"
        , HP.attr (HH.AttrName "r") "8"
        ]
        []
    , HH.elementNS
        (HH.Namespace "http://www.w3.org/2000/svg")
        (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "m21 21-4.3-4.3" ]
        []
    ]

-- | Spinner icon for loading state
spinnerIcon :: forall w i. HH.HTML w i
spinnerIcon =
  HH.elementNS
    (HH.Namespace "http://www.w3.org/2000/svg")
    (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "class") "h-4 w-4 animate-spin"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    ]
    [ HH.elementNS
        (HH.Namespace "http://www.w3.org/2000/svg")
        (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M21 12a9 9 0 1 1-6.219-8.56" ]
        []
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // keyboard handler
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Register global keyboard shortcut (⌘K / Ctrl+K)
-- |
-- | Returns a cleanup function to unregister the shortcut.
foreign import registerGlobalShortcut :: (Effect Unit) -> Effect (Effect Unit)

-- | Unregister global keyboard shortcut
foreign import unregisterGlobalShortcut :: Effect Unit -> Effect Unit

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // fuzzy search
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Check if query fuzzy matches target string
-- |
-- | ```purescript
-- | fuzzyMatch "ofi" "Open File" == true
-- | fuzzyMatch "xyz" "Open File" == false
-- | ```
fuzzyMatch :: String -> String -> Boolean
fuzzyMatch query target =
  let
    q = String.toLower query
    t = String.toLower target
  in
    String.contains (Pattern q) t || matchChars q t 0 0
  where
  matchChars :: String -> String -> Int -> Int -> Boolean
  matchChars q' t' qi ti
    | qi >= String.length q' = true
    | ti >= String.length t' = false
    | otherwise = 
        let qc = String.codePointAt qi q'
            tc = String.codePointAt ti t'
        in case qc, tc of
          Just qcp, Just tcp | qcp == tcp -> matchChars q' t' (qi + 1) (ti + 1)
          _, _ -> matchChars q' t' qi (ti + 1)

-- | Calculate fuzzy match score (higher is better)
-- |
-- | Scoring factors:
-- | - Sequential character matches
-- | - Word boundary matches
-- | - Early matches in string
foreign import fuzzyScore :: String -> String -> Int
