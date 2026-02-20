-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                        // hydrogen // menubar
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Application Menu Bar component
-- |
-- | Horizontal menu bar with dropdown menus, following the ARIA menubar pattern.
-- | Supports keyboard navigation with arrow keys between menu items and within
-- | dropdown menus.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Primitive.Menubar as Menubar
-- |
-- | Menubar.menubar []
-- |   [ Menubar.menubarMenu [ Menubar.open (state.activeMenu == "file") ]
-- |       [ Menubar.menubarTrigger
-- |           [ Menubar.onToggle (ToggleMenu "file") ]
-- |           [ HH.text "File" ]
-- |       , Menubar.menubarContent []
-- |           [ Menubar.menubarItem
-- |               [ Menubar.onSelect HandleNew
-- |               , Menubar.shortcut "⌘N"
-- |               ]
-- |               [ HH.text "New" ]
-- |           , Menubar.menubarItem
-- |               [ Menubar.onSelect HandleOpen
-- |               , Menubar.shortcut "⌘O"
-- |               ]
-- |               [ HH.text "Open" ]
-- |           , Menubar.menubarSeparator []
-- |           , Menubar.menubarItem [ Menubar.onSelect HandleQuit ]
-- |               [ HH.text "Quit" ]
-- |           ]
-- |       ]
-- |   , Menubar.menubarMenu [ Menubar.open (state.activeMenu == "edit") ]
-- |       [ Menubar.menubarTrigger
-- |           [ Menubar.onToggle (ToggleMenu "edit") ]
-- |           [ HH.text "Edit" ]
-- |       , Menubar.menubarContent []
-- |           [ Menubar.menubarItem [ Menubar.shortcut "⌘Z" ]
-- |               [ HH.text "Undo" ]
-- |           , Menubar.menubarItem [ Menubar.shortcut "⌘Y" ]
-- |               [ HH.text "Redo" ]
-- |           ]
-- |       ]
-- |   ]
-- | ```
-- |
-- | ## Keyboard Navigation
-- |
-- | - `←/→` - Navigate between menu bar items
-- | - `↓` - Open dropdown menu
-- | - `↑/↓` - Navigate within dropdown menu
-- | - `Enter` - Select item / Open menu
-- | - `Escape` - Close menu
-- |
-- | ## Checkbox and Radio Items
-- |
-- | ```purescript
-- | Menubar.menubarCheckboxItem
-- |   [ Menubar.checked state.wordWrap
-- |   , Menubar.onCheckedChange ToggleWordWrap
-- |   ]
-- |   [ HH.text "Word Wrap" ]
-- |
-- | Menubar.menubarRadioGroup [ Menubar.value state.fontSize ]
-- |   [ Menubar.menubarRadioItem [ Menubar.value "small" ]
-- |       [ HH.text "Small" ]
-- |   , Menubar.menubarRadioItem [ Menubar.value "medium" ]
-- |       [ HH.text "Medium" ]
-- |   , Menubar.menubarRadioItem [ Menubar.value "large" ]
-- |       [ HH.text "Large" ]
-- |   ]
-- | ```
module Hydrogen.Primitive.Menubar
  ( -- * Menubar Components
    menubar
  , menubarMenu
  , menubarTrigger
  , menubarContent
  , menubarItem
  , menubarCheckboxItem
  , menubarRadioGroup
  , menubarRadioItem
  , menubarSeparator
  , menubarLabel
  , menubarGroup
  , menubarSub
  , menubarSubTrigger
  , menubarSubContent
  , menubarShortcut
    -- * Props
  , MenubarProps
  , MenubarProp
  , open
  , disabled
  , checked
  , value
  , onToggle
  , onSelect
  , onCheckedChange
  , onValueChange
  , shortcut
  , className
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
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Menubar properties
type MenubarProps i =
  { open :: Boolean
  , disabled :: Boolean
  , checked :: Boolean
  , value :: String
  , onToggle :: Maybe (MouseEvent -> i)
  , onSelect :: Maybe (MouseEvent -> i)
  , onCheckedChange :: Maybe (Boolean -> i)
  , onValueChange :: Maybe (String -> i)
  , shortcut :: String
  , className :: String
  }

type MenubarProp i = MenubarProps i -> MenubarProps i

defaultProps :: forall i. MenubarProps i
defaultProps =
  { open: false
  , disabled: false
  , checked: false
  , value: ""
  , onToggle: Nothing
  , onSelect: Nothing
  , onCheckedChange: Nothing
  , onValueChange: Nothing
  , shortcut: ""
  , className: ""
  }

-- | Set open state
open :: forall i. Boolean -> MenubarProp i
open o props = props { open = o }

-- | Set disabled state
disabled :: forall i. Boolean -> MenubarProp i
disabled d props = props { disabled = d }

-- | Set checked state
checked :: forall i. Boolean -> MenubarProp i
checked c props = props { checked = c }

-- | Set value
value :: forall i. String -> MenubarProp i
value v props = props { value = v }

-- | Set toggle handler
onToggle :: forall i. (MouseEvent -> i) -> MenubarProp i
onToggle handler props = props { onToggle = Just handler }

-- | Set select handler
onSelect :: forall i. (MouseEvent -> i) -> MenubarProp i
onSelect handler props = props { onSelect = Just handler }

-- | Set checked change handler
onCheckedChange :: forall i. (Boolean -> i) -> MenubarProp i
onCheckedChange handler props = props { onCheckedChange = Just handler }

-- | Set value change handler
onValueChange :: forall i. (String -> i) -> MenubarProp i
onValueChange handler props = props { onValueChange = Just handler }

-- | Set keyboard shortcut
shortcut :: forall i. String -> MenubarProp i
shortcut s props = props { shortcut = s }

-- | Add custom class
className :: forall i. String -> MenubarProp i
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Menubar root container
-- |
-- | The horizontal menu bar that contains menu triggers.
menubar :: forall w i. Array (MenubarProp i) -> Array (HH.HTML w i) -> HH.HTML w i
menubar propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "flex h-10 items-center space-x-1 rounded-md border bg-background p-1", props.className ]
    , ARIA.role "menubar"
    ]
    children

-- | Menubar menu container
-- |
-- | Wraps a trigger and its associated dropdown content.
menubarMenu :: forall w i. Array (MenubarProp i) -> Array (HH.HTML w i) -> HH.HTML w i
menubarMenu propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "relative", props.className ] ]
    children

-- | Menubar trigger button
-- |
-- | The button in the menu bar that opens a dropdown.
menubarTrigger :: forall w i. Array (MenubarProp i) -> Array (HH.HTML w i) -> HH.HTML w i
menubarTrigger propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    activeClasses = if props.open
      then "bg-accent text-accent-foreground"
      else ""
  in
    HH.button
      ( [ cls [ "flex cursor-default select-none items-center rounded-sm px-3 py-1.5 text-sm font-medium outline-none focus:bg-accent focus:text-accent-foreground hover:bg-accent hover:text-accent-foreground", activeClasses, props.className ]
        , HP.type_ HP.ButtonButton
        , ARIA.role "menuitem"
        , ARIA.hasPopup "menu"
        , ARIA.expanded (if props.open then "true" else "false")
        , HP.attr (HH.AttrName "data-state") (if props.open then "open" else "closed")
        ] <> case props.onToggle of
          Just handler -> [ HE.onClick handler ]
          Nothing -> []
      )
      children

-- | Menubar dropdown content
-- |
-- | The dropdown panel that appears when a menu is opened.
menubarContent :: forall w i. Array (MenubarProp i) -> Array (HH.HTML w i) -> HH.HTML w i
menubarContent propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    visibilityClass = if props.open then "" else "hidden"
  in
    HH.div
      [ cls [ "absolute left-0 top-full z-50 mt-1 min-w-[12rem] overflow-hidden rounded-md border bg-popover p-1 text-popover-foreground shadow-md animate-in fade-in-0 zoom-in-95", visibilityClass, props.className ]
      , ARIA.role "menu"
      , HP.attr (HH.AttrName "data-state") (if props.open then "open" else "closed")
      ]
      children

-- | Menubar item
menubarItem :: forall w i. Array (MenubarProp i) -> Array (HH.HTML w i) -> HH.HTML w i
menubarItem propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    disabledClasses = if props.disabled
      then "opacity-50 pointer-events-none"
      else "cursor-pointer"
  in
    HH.div
      ( [ cls [ "relative flex cursor-default select-none items-center rounded-sm px-2 py-1.5 text-sm outline-none focus:bg-accent focus:text-accent-foreground hover:bg-accent hover:text-accent-foreground", disabledClasses, props.className ]
        , ARIA.role "menuitem"
        , HP.attr (HH.AttrName "data-disabled") (if props.disabled then "true" else "false")
        ] <> case props.onSelect of
          Just handler | not props.disabled -> [ HE.onClick handler ]
          _ -> []
      )
      [ HH.span [ cls [ "flex-1" ] ] children
      , if props.shortcut /= ""
          then menubarShortcut [] [ HH.text props.shortcut ]
          else HH.text ""
      ]

-- | Menubar checkbox item
menubarCheckboxItem :: forall w i. Array (MenubarProp i) -> Array (HH.HTML w i) -> HH.HTML w i
menubarCheckboxItem propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    disabledClasses = if props.disabled
      then "opacity-50 pointer-events-none"
      else "cursor-pointer"
  in
    HH.div
      ( [ cls [ "relative flex cursor-default select-none items-center rounded-sm py-1.5 pl-8 pr-2 text-sm outline-none focus:bg-accent focus:text-accent-foreground hover:bg-accent hover:text-accent-foreground", disabledClasses, props.className ]
        , ARIA.role "menuitemcheckbox"
        , ARIA.checked (if props.checked then "true" else "false")
        , HP.attr (HH.AttrName "data-state") (if props.checked then "checked" else "unchecked")
        ] <> case props.onCheckedChange of
          Just handler | not props.disabled -> [ HE.onClick (\_ -> handler (not props.checked)) ]
          _ -> []
      )
      [ HH.span
          [ cls [ "absolute left-2 flex h-3.5 w-3.5 items-center justify-center" ] ]
          [ if props.checked then checkIcon else HH.text "" ]
      , HH.span [ cls [ "flex-1" ] ] children
      ]

-- | Menubar radio group
menubarRadioGroup :: forall w i. Array (MenubarProp i) -> Array (HH.HTML w i) -> HH.HTML w i
menubarRadioGroup propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ props.className ]
    , ARIA.role "group"
    , HP.attr (HH.AttrName "data-value") props.value
    ]
    children

-- | Menubar radio item
menubarRadioItem :: forall w i. Array (MenubarProp i) -> Array (HH.HTML w i) -> HH.HTML w i
menubarRadioItem propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    disabledClasses = if props.disabled
      then "opacity-50 pointer-events-none"
      else "cursor-pointer"
  in
    HH.div
      ( [ cls [ "relative flex cursor-default select-none items-center rounded-sm py-1.5 pl-8 pr-2 text-sm outline-none focus:bg-accent focus:text-accent-foreground hover:bg-accent hover:text-accent-foreground", disabledClasses, props.className ]
        , ARIA.role "menuitemradio"
        , ARIA.checked (if props.checked then "true" else "false")
        , HP.attr (HH.AttrName "data-state") (if props.checked then "checked" else "unchecked")
        , HP.attr (HH.AttrName "data-value") props.value
        ] <> case props.onValueChange of
          Just handler | not props.disabled -> [ HE.onClick (\_ -> handler props.value) ]
          _ -> []
      )
      [ HH.span
          [ cls [ "absolute left-2 flex h-3.5 w-3.5 items-center justify-center" ] ]
          [ if props.checked then radioIcon else HH.text "" ]
      , HH.span [ cls [ "flex-1" ] ] children
      ]

-- | Menubar separator
menubarSeparator :: forall w i. Array (MenubarProp i) -> HH.HTML w i
menubarSeparator propMods =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "-mx-1 my-1 h-px bg-muted", props.className ]
    , ARIA.role "separator"
    ]
    []

-- | Menubar label (non-interactive heading)
menubarLabel :: forall w i. Array (MenubarProp i) -> Array (HH.HTML w i) -> HH.HTML w i
menubarLabel propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "px-2 py-1.5 text-sm font-semibold", props.className ] ]
    children

-- | Menubar group
menubarGroup :: forall w i. Array (MenubarProp i) -> Array (HH.HTML w i) -> HH.HTML w i
menubarGroup propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ props.className ]
    , ARIA.role "group"
    ]
    children

-- | Submenu container
menubarSub :: forall w i. Array (MenubarProp i) -> Array (HH.HTML w i) -> HH.HTML w i
menubarSub propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "relative group/submenu", props.className ] ]
    children

-- | Submenu trigger
menubarSubTrigger :: forall w i. Array (MenubarProp i) -> Array (HH.HTML w i) -> HH.HTML w i
menubarSubTrigger propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "flex cursor-default select-none items-center rounded-sm px-2 py-1.5 text-sm outline-none hover:bg-accent focus:bg-accent", props.className ]
    , ARIA.hasPopup "menu"
    ]
    [ HH.span [ cls [ "flex-1" ] ] children
    , chevronRightIcon
    ]

-- | Submenu content
menubarSubContent :: forall w i. Array (MenubarProp i) -> Array (HH.HTML w i) -> HH.HTML w i
menubarSubContent propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "absolute left-full top-0 z-50 min-w-[8rem] overflow-hidden rounded-md border bg-popover p-1 text-popover-foreground shadow-lg invisible opacity-0 group-hover/submenu:visible group-hover/submenu:opacity-100 transition-all", props.className ]
    , ARIA.role "menu"
    ]
    children

-- | Keyboard shortcut display
menubarShortcut :: forall w i. Array (MenubarProp i) -> Array (HH.HTML w i) -> HH.HTML w i
menubarShortcut propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.span
    [ cls [ "ml-auto text-xs tracking-widest text-muted-foreground", props.className ] ]
    children

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // icons
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Check icon for checkbox items
checkIcon :: forall w i. HH.HTML w i
checkIcon =
  HH.elementNS
    (HH.Namespace "http://www.w3.org/2000/svg")
    (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "class") "h-4 w-4"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , HP.attr (HH.AttrName "stroke-linejoin") "round"
    ]
    [ HH.elementNS
        (HH.Namespace "http://www.w3.org/2000/svg")
        (HH.ElemName "polyline")
        [ HP.attr (HH.AttrName "points") "20 6 9 17 4 12" ]
        []
    ]

-- | Radio dot icon
radioIcon :: forall w i. HH.HTML w i
radioIcon =
  HH.elementNS
    (HH.Namespace "http://www.w3.org/2000/svg")
    (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "class") "h-2 w-2 fill-current"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    ]
    [ HH.elementNS
        (HH.Namespace "http://www.w3.org/2000/svg")
        (HH.ElemName "circle")
        [ HP.attr (HH.AttrName "cx") "12"
        , HP.attr (HH.AttrName "cy") "12"
        , HP.attr (HH.AttrName "r") "12"
        ]
        []
    ]

-- | Chevron right icon for submenus
chevronRightIcon :: forall w i. HH.HTML w i
chevronRightIcon =
  HH.elementNS
    (HH.Namespace "http://www.w3.org/2000/svg")
    (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "class") "ml-auto h-4 w-4"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , HP.attr (HH.AttrName "stroke-linejoin") "round"
    ]
    [ HH.elementNS
        (HH.Namespace "http://www.w3.org/2000/svg")
        (HH.ElemName "polyline")
        [ HP.attr (HH.AttrName "points") "9 18 15 12 9 6" ]
        []
    ]
