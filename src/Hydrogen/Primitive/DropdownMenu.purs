-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // hydrogen // dropdownmenu
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Cascading Dropdown Menu component
-- |
-- | Accessible dropdown menus with submenus, checkboxes, radio items,
-- | and keyboard navigation. Follows the ARIA menu pattern.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Primitive.DropdownMenu as DropdownMenu
-- |
-- | DropdownMenu.dropdownMenu [ DropdownMenu.open state.isOpen ]
-- |   [ DropdownMenu.dropdownMenuTrigger [ DropdownMenu.onToggle ToggleMenu ]
-- |       [ Button.button [] [ HH.text "Options" ] ]
-- |   , DropdownMenu.dropdownMenuContent []
-- |       [ DropdownMenu.dropdownMenuLabel [] [ HH.text "My Account" ]
-- |       , DropdownMenu.dropdownMenuSeparator []
-- |       , DropdownMenu.dropdownMenuItem
-- |           [ DropdownMenu.onSelect HandleProfile
-- |           , DropdownMenu.icon userIcon
-- |           , DropdownMenu.shortcut "⌘P"
-- |           ]
-- |           [ HH.text "Profile" ]
-- |       , DropdownMenu.dropdownMenuItem
-- |           [ DropdownMenu.onSelect HandleSettings
-- |           , DropdownMenu.shortcut "⌘,"
-- |           ]
-- |           [ HH.text "Settings" ]
-- |       , DropdownMenu.dropdownMenuSeparator []
-- |       , DropdownMenu.dropdownMenuCheckboxItem
-- |           [ DropdownMenu.checked state.showToolbar
-- |           , DropdownMenu.onCheckedChange ToggleToolbar
-- |           ]
-- |           [ HH.text "Show Toolbar" ]
-- |       , DropdownMenu.dropdownMenuSeparator []
-- |       , DropdownMenu.dropdownMenuSub []
-- |           [ DropdownMenu.dropdownMenuSubTrigger []
-- |               [ HH.text "More Options →" ]
-- |           , DropdownMenu.dropdownMenuSubContent []
-- |               [ DropdownMenu.dropdownMenuItem [] [ HH.text "Option 1" ]
-- |               , DropdownMenu.dropdownMenuItem [] [ HH.text "Option 2" ]
-- |               ]
-- |           ]
-- |       ]
-- |   ]
-- | ```
-- |
-- | ## Radio Groups
-- |
-- | ```purescript
-- | DropdownMenu.dropdownMenuRadioGroup [ DropdownMenu.value state.theme ]
-- |   [ DropdownMenu.dropdownMenuRadioItem [ DropdownMenu.value "light" ]
-- |       [ HH.text "Light" ]
-- |   , DropdownMenu.dropdownMenuRadioItem [ DropdownMenu.value "dark" ]
-- |       [ HH.text "Dark" ]
-- |   , DropdownMenu.dropdownMenuRadioItem [ DropdownMenu.value "system" ]
-- |       [ HH.text "System" ]
-- |   ]
-- | ```
module Hydrogen.Primitive.DropdownMenu
  ( -- * Dropdown Menu Components
    dropdownMenu
  , dropdownMenuTrigger
  , dropdownMenuContent
  , dropdownMenuItem
  , dropdownMenuCheckboxItem
  , dropdownMenuRadioGroup
  , dropdownMenuRadioItem
  , dropdownMenuLabel
  , dropdownMenuSeparator
  , dropdownMenuGroup
  , dropdownMenuSub
  , dropdownMenuSubTrigger
  , dropdownMenuSubContent
  , dropdownMenuShortcut
    -- * Props
  , DropdownMenuProps
  , DropdownMenuProp
  , open
  , disabled
  , checked
  , value
  , side
  , align
  , onToggle
  , onSelect
  , onCheckedChange
  , onValueChange
  , shortcut
  , className
    -- * Positioning
  , Side(..)
  , Align(..)
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
--                                                                 // positioning
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Menu side positioning relative to trigger
data Side
  = Top
  | Right
  | Bottom
  | Left

derive instance eqSide :: Eq Side

-- | Menu alignment relative to trigger
data Align
  = Start
  | Center
  | End

derive instance eqAlign :: Eq Align

-- | Get positioning classes based on side and alignment
positionClasses :: Side -> Align -> String
positionClasses side' align' = case side' of
  Top -> "bottom-full mb-2 " <> alignClasses align'
  Right -> "left-full ml-2 top-0"
  Bottom -> "top-full mt-2 " <> alignClasses align'
  Left -> "right-full mr-2 top-0"
  where
  alignClasses :: Align -> String
  alignClasses = case _ of
    Start -> "left-0"
    Center -> "left-1/2 -translate-x-1/2"
    End -> "right-0"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Dropdown menu properties
type DropdownMenuProps i =
  { open :: Boolean
  , disabled :: Boolean
  , checked :: Boolean
  , value :: String
  , side :: Side
  , align :: Align
  , onToggle :: Maybe (MouseEvent -> i)
  , onSelect :: Maybe (MouseEvent -> i)
  , onCheckedChange :: Maybe (Boolean -> i)
  , onValueChange :: Maybe (String -> i)
  , shortcut :: String
  , className :: String
  }

type DropdownMenuProp i = DropdownMenuProps i -> DropdownMenuProps i

defaultProps :: forall i. DropdownMenuProps i
defaultProps =
  { open: false
  , disabled: false
  , checked: false
  , value: ""
  , side: Bottom
  , align: Start
  , onToggle: Nothing
  , onSelect: Nothing
  , onCheckedChange: Nothing
  , onValueChange: Nothing
  , shortcut: ""
  , className: ""
  }

-- | Set open state
open :: forall i. Boolean -> DropdownMenuProp i
open o props = props { open = o }

-- | Set disabled state
disabled :: forall i. Boolean -> DropdownMenuProp i
disabled d props = props { disabled = d }

-- | Set checked state (for checkbox items)
checked :: forall i. Boolean -> DropdownMenuProp i
checked c props = props { checked = c }

-- | Set value (for radio items)
value :: forall i. String -> DropdownMenuProp i
value v props = props { value = v }

-- | Set menu side positioning
side :: forall i. Side -> DropdownMenuProp i
side s props = props { side = s }

-- | Set menu alignment
align :: forall i. Align -> DropdownMenuProp i
align a props = props { align = a }

-- | Set toggle handler
onToggle :: forall i. (MouseEvent -> i) -> DropdownMenuProp i
onToggle handler props = props { onToggle = Just handler }

-- | Set select handler
onSelect :: forall i. (MouseEvent -> i) -> DropdownMenuProp i
onSelect handler props = props { onSelect = Just handler }

-- | Set checked change handler
onCheckedChange :: forall i. (Boolean -> i) -> DropdownMenuProp i
onCheckedChange handler props = props { onCheckedChange = Just handler }

-- | Set value change handler (for radio groups)
onValueChange :: forall i. (String -> i) -> DropdownMenuProp i
onValueChange handler props = props { onValueChange = Just handler }

-- | Set keyboard shortcut
shortcut :: forall i. String -> DropdownMenuProp i
shortcut s props = props { shortcut = s }

-- | Add custom class
className :: forall i. String -> DropdownMenuProp i
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Dropdown menu root container
dropdownMenu :: forall w i. Array (DropdownMenuProp i) -> Array (HH.HTML w i) -> HH.HTML w i
dropdownMenu propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "relative inline-block text-left", props.className ] ]
    children

-- | Dropdown menu trigger button
dropdownMenuTrigger :: forall w i. Array (DropdownMenuProp i) -> Array (HH.HTML w i) -> HH.HTML w i
dropdownMenuTrigger propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    ( [ cls [ props.className ]
      , ARIA.hasPopup "menu"
      , ARIA.expanded (if props.open then "true" else "false")
      ] <> case props.onToggle of
        Just handler -> [ HE.onClick handler ]
        Nothing -> []
    )
    children

-- | Dropdown menu content panel
dropdownMenuContent :: forall w i. Array (DropdownMenuProp i) -> Array (HH.HTML w i) -> HH.HTML w i
dropdownMenuContent propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    visibilityClass = if props.open then "" else "hidden"
    posClass = positionClasses props.side props.align
  in
    HH.div
      [ cls [ "absolute z-50 min-w-[8rem] overflow-hidden rounded-md border bg-popover p-1 text-popover-foreground shadow-md", posClass, visibilityClass, props.className ]
      , cls [ "animate-in fade-in-0 zoom-in-95" ]
      , ARIA.role "menu"
      , HP.attr (HH.AttrName "data-state") (if props.open then "open" else "closed")
      , HP.attr (HH.AttrName "data-side") (sideToString props.side)
      , HP.attr (HH.AttrName "data-align") (alignToString props.align)
      ]
      children
  where
  sideToString :: Side -> String
  sideToString = case _ of
    Top -> "top"
    Right -> "right"
    Bottom -> "bottom"
    Left -> "left"

  alignToString :: Align -> String
  alignToString = case _ of
    Start -> "start"
    Center -> "center"
    End -> "end"

-- | Dropdown menu item
-- | 
-- | Children can include icons and labels. Pass icons as the first children.
dropdownMenuItem :: forall w i. Array (DropdownMenuProp i) -> Array (HH.HTML w i) -> HH.HTML w i
dropdownMenuItem propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    disabledClasses = if props.disabled
      then "opacity-50 pointer-events-none"
      else "cursor-pointer"
  in
    HH.div
      ( [ cls [ "relative flex cursor-default select-none items-center gap-2 rounded-sm px-2 py-1.5 text-sm outline-none transition-colors focus:bg-accent focus:text-accent-foreground hover:bg-accent hover:text-accent-foreground", disabledClasses, props.className ]
        , ARIA.role "menuitem"
        , HP.attr (HH.AttrName "data-disabled") (if props.disabled then "true" else "false")
        ] <> case props.onSelect of
          Just handler | not props.disabled -> [ HE.onClick handler ]
          _ -> []
      )
      ( -- Content (children include icon + label)
        [ HH.span [ cls [ "flex items-center gap-2 flex-1" ] ] children ]
        -- Shortcut (if provided)
        <> if props.shortcut /= ""
          then [ dropdownMenuShortcut [] [ HH.text props.shortcut ] ]
          else []
      )

-- | Dropdown menu checkbox item
dropdownMenuCheckboxItem :: forall w i. Array (DropdownMenuProp i) -> Array (HH.HTML w i) -> HH.HTML w i
dropdownMenuCheckboxItem propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    disabledClasses = if props.disabled
      then "opacity-50 pointer-events-none"
      else "cursor-pointer"
  in
    HH.div
      ( [ cls [ "relative flex cursor-default select-none items-center rounded-sm py-1.5 pl-8 pr-2 text-sm outline-none transition-colors focus:bg-accent focus:text-accent-foreground hover:bg-accent hover:text-accent-foreground", disabledClasses, props.className ]
        , ARIA.role "menuitemcheckbox"
        , ARIA.checked (if props.checked then "true" else "false")
        , HP.attr (HH.AttrName "data-state") (if props.checked then "checked" else "unchecked")
        ] <> case props.onCheckedChange of
          Just handler | not props.disabled -> [ HE.onClick (\_ -> handler (not props.checked)) ]
          _ -> []
      )
      [ -- Checkbox indicator
        HH.span
          [ cls [ "absolute left-2 flex h-3.5 w-3.5 items-center justify-center" ] ]
          [ if props.checked then checkIcon else HH.text "" ]
      , HH.span [ cls [ "flex-1" ] ] children
      ]

-- | Dropdown menu radio group
dropdownMenuRadioGroup :: forall w i. Array (DropdownMenuProp i) -> Array (HH.HTML w i) -> HH.HTML w i
dropdownMenuRadioGroup propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ props.className ]
    , ARIA.role "group"
    , HP.attr (HH.AttrName "data-value") props.value
    ]
    children

-- | Dropdown menu radio item
dropdownMenuRadioItem :: forall w i. Array (DropdownMenuProp i) -> Array (HH.HTML w i) -> HH.HTML w i
dropdownMenuRadioItem propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    disabledClasses = if props.disabled
      then "opacity-50 pointer-events-none"
      else "cursor-pointer"
  in
    HH.div
      ( [ cls [ "relative flex cursor-default select-none items-center rounded-sm py-1.5 pl-8 pr-2 text-sm outline-none transition-colors focus:bg-accent focus:text-accent-foreground hover:bg-accent hover:text-accent-foreground", disabledClasses, props.className ]
        , ARIA.role "menuitemradio"
        , ARIA.checked (if props.checked then "true" else "false")
        , HP.attr (HH.AttrName "data-state") (if props.checked then "checked" else "unchecked")
        , HP.attr (HH.AttrName "data-value") props.value
        ] <> case props.onValueChange of
          Just handler | not props.disabled -> [ HE.onClick (\_ -> handler props.value) ]
          _ -> []
      )
      [ -- Radio indicator
        HH.span
          [ cls [ "absolute left-2 flex h-3.5 w-3.5 items-center justify-center" ] ]
          [ if props.checked then radioIcon else HH.text "" ]
      , HH.span [ cls [ "flex-1" ] ] children
      ]

-- | Dropdown menu label (non-interactive heading)
dropdownMenuLabel :: forall w i. Array (DropdownMenuProp i) -> Array (HH.HTML w i) -> HH.HTML w i
dropdownMenuLabel propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "px-2 py-1.5 text-sm font-semibold", props.className ] ]
    children

-- | Dropdown menu separator
dropdownMenuSeparator :: forall w i. Array (DropdownMenuProp i) -> HH.HTML w i
dropdownMenuSeparator propMods =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "-mx-1 my-1 h-px bg-muted", props.className ]
    , ARIA.role "separator"
    ]
    []

-- | Dropdown menu group
dropdownMenuGroup :: forall w i. Array (DropdownMenuProp i) -> Array (HH.HTML w i) -> HH.HTML w i
dropdownMenuGroup propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ props.className ]
    , ARIA.role "group"
    ]
    children

-- | Submenu container
dropdownMenuSub :: forall w i. Array (DropdownMenuProp i) -> Array (HH.HTML w i) -> HH.HTML w i
dropdownMenuSub propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "relative group/submenu", props.className ] ]
    children

-- | Submenu trigger (hover to open)
dropdownMenuSubTrigger :: forall w i. Array (DropdownMenuProp i) -> Array (HH.HTML w i) -> HH.HTML w i
dropdownMenuSubTrigger propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "flex cursor-default select-none items-center rounded-sm px-2 py-1.5 text-sm outline-none hover:bg-accent focus:bg-accent", props.className ]
    , ARIA.hasPopup "menu"
    ]
    [ HH.span [ cls [ "flex-1" ] ] children
    , chevronRightIcon
    ]

-- | Submenu content (appears on hover)
dropdownMenuSubContent :: forall w i. Array (DropdownMenuProp i) -> Array (HH.HTML w i) -> HH.HTML w i
dropdownMenuSubContent propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "absolute left-full top-0 z-50 min-w-[8rem] overflow-hidden rounded-md border bg-popover p-1 text-popover-foreground shadow-lg invisible opacity-0 group-hover/submenu:visible group-hover/submenu:opacity-100 transition-all", props.className ]
    , ARIA.role "menu"
    ]
    children

-- | Keyboard shortcut display
dropdownMenuShortcut :: forall w i. Array (DropdownMenuProp i) -> Array (HH.HTML w i) -> HH.HTML w i
dropdownMenuShortcut propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.span
    [ cls [ "ml-auto text-xs tracking-widest opacity-60", props.className ] ]
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

-- | Radio dot icon for radio items
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
