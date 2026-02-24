-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                           // hydrogen // menu
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Dropdown Menu component
-- |
-- | Accessible dropdown menus with keyboard navigation.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Primitive.Menu as Menu
-- |
-- | Menu.menu [ Menu.open state.isOpen ]
-- |   [ Menu.menuTrigger [ Menu.onToggle ToggleMenu ]
-- |       [ Button.button [] [ HH.text "Menu" ] ]
-- |   , Menu.menuContent []
-- |       [ Menu.menuItem [ Menu.onSelect SelectEdit ] [ HH.text "Edit" ]
-- |       , Menu.menuItem [ Menu.onSelect SelectDelete ] [ HH.text "Delete" ]
-- |       , Menu.menuSeparator []
-- |       , Menu.menuItem [ Menu.disabled true ] [ HH.text "Disabled" ]
-- |       ]
-- |   ]
-- | ```
module Hydrogen.Primitive.Menu
  ( -- * Menu Components
    menu
  , menuTrigger
  , menuContent
  , menuItem
  , menuSeparator
  , menuLabel
  , menuGroup
    -- * Props
  , MenuProps
  , MenuProp
  , open
  , disabled
  , onToggle
  , onSelect
  , className
  ) where

import Prelude

import Data.Array (foldl)
import Data.Maybe (Maybe(Just, Nothing))
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)
import Web.UIEvent.MouseEvent (MouseEvent)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

type MenuProps i =
  { open :: Boolean
  , disabled :: Boolean
  , onToggle :: Maybe (MouseEvent -> i)
  , onSelect :: Maybe (MouseEvent -> i)
  , className :: String
  }

type MenuProp i = MenuProps i -> MenuProps i

defaultProps :: forall i. MenuProps i
defaultProps =
  { open: false
  , disabled: false
  , onToggle: Nothing
  , onSelect: Nothing
  , className: ""
  }

-- | Set open state
open :: forall i. Boolean -> MenuProp i
open o props = props { open = o }

-- | Set disabled state
disabled :: forall i. Boolean -> MenuProp i
disabled d props = props { disabled = d }

-- | Set toggle handler
onToggle :: forall i. (MouseEvent -> i) -> MenuProp i
onToggle handler props = props { onToggle = Just handler }

-- | Set select handler
onSelect :: forall i. (MouseEvent -> i) -> MenuProp i
onSelect handler props = props { onSelect = Just handler }

-- | Add custom class
className :: forall i. String -> MenuProp i
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Menu container
menu :: forall w i. Array (MenuProp i) -> Array (HH.HTML w i) -> HH.HTML w i
menu propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "relative inline-block text-left", props.className ] ]
    children

-- | Menu trigger
menuTrigger :: forall w i. Array (MenuProp i) -> Array (HH.HTML w i) -> HH.HTML w i
menuTrigger propMods children =
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

-- | Menu content panel
menuContent :: forall w i. Array (MenuProp i) -> Array (HH.HTML w i) -> HH.HTML w i
menuContent propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    visibilityClass = if props.open then "" else "hidden"
  in
    HH.div
      [ cls [ "absolute right-0 z-50 mt-2 min-w-[8rem] overflow-hidden rounded-md border bg-popover p-1 text-popover-foreground shadow-md animate-in fade-in-0 zoom-in-95", visibilityClass, props.className ]
      , ARIA.role "menu"
      ]
      children

-- | Menu item
menuItem :: forall w i. Array (MenuProp i) -> Array (HH.HTML w i) -> HH.HTML w i
menuItem propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    disabledClasses = if props.disabled
      then "opacity-50 pointer-events-none"
      else "cursor-pointer"
  in
    HH.div
      ( [ cls [ "relative flex select-none items-center rounded-sm px-2 py-1.5 text-sm outline-none transition-colors focus:bg-accent focus:text-accent-foreground hover:bg-accent hover:text-accent-foreground", disabledClasses, props.className ]
        , ARIA.role "menuitem"
        , HP.attr (HH.AttrName "data-disabled") (if props.disabled then "true" else "false")
        ] <> case props.onSelect of
          Just handler | not props.disabled -> [ HE.onClick handler ]
          _ -> []
      )
      children

-- | Menu separator
menuSeparator :: forall w i. Array (MenuProp i) -> HH.HTML w i
menuSeparator propMods =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "-mx-1 my-1 h-px bg-muted", props.className ]
    , ARIA.role "separator"
    ]
    []

-- | Menu label (non-interactive heading)
menuLabel :: forall w i. Array (MenuProp i) -> Array (HH.HTML w i) -> HH.HTML w i
menuLabel propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "px-2 py-1.5 text-sm font-semibold", props.className ] ]
    children

-- | Menu group (for grouping items)
menuGroup :: forall w i. Array (MenuProp i) -> Array (HH.HTML w i) -> HH.HTML w i
menuGroup propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ props.className ]
    , ARIA.role "group"
    ]
    children
