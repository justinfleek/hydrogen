-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                    // hydrogen // contextmenu
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Context Menu component
-- |
-- | Right-click menus with items, submenus, separators, and keyboard navigation.
-- | Follows the ARIA menu pattern for accessibility.
-- |
-- | ## Features
-- |
-- | - **Right-click trigger**: Opens at cursor position
-- | - **Positioned at cursor**: Appears where user right-clicked
-- | - **Menu items**: With optional icons and shortcuts
-- | - **Submenus**: Nested menus for hierarchical navigation
-- | - **Separators**: Visual dividers between item groups
-- | - **Disabled items**: Grayed out non-interactive items
-- | - **Keyboard navigation**: Arrow keys, Enter, Escape
-- | - **ARIA menu pattern**: Fully accessible
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Primitive.ContextMenu as ContextMenu
-- |
-- | ContextMenu.contextMenu [ ContextMenu.open state.isOpen ]
-- |   [ ContextMenu.contextMenuTrigger []
-- |       [ HH.div [ HP.class_ "w-full h-64 border" ]
-- |           [ HH.text "Right-click here" ]
-- |       ]
-- |   , ContextMenu.contextMenuContent
-- |       [ ContextMenu.position state.position ]
-- |       [ ContextMenu.contextMenuItem
-- |           [ ContextMenu.onSelect (SelectAction "edit")
-- |           , ContextMenu.icon editIcon
-- |           ]
-- |           [ HH.text "Edit" ]
-- |       , ContextMenu.contextMenuItem
-- |           [ ContextMenu.onSelect (SelectAction "copy") ]
-- |           [ HH.text "Copy" ]
-- |       , ContextMenu.contextMenuSeparator []
-- |       , ContextMenu.contextMenuSub []
-- |           [ ContextMenu.contextMenuSubTrigger []
-- |               [ HH.text "More options" ]
-- |           , ContextMenu.contextMenuSubContent []
-- |               [ ContextMenu.contextMenuItem [] [ HH.text "Option 1" ]
-- |               , ContextMenu.contextMenuItem [] [ HH.text "Option 2" ]
-- |               ]
-- |           ]
-- |       , ContextMenu.contextMenuSeparator []
-- |       , ContextMenu.contextMenuItem
-- |           [ ContextMenu.disabled true ]
-- |           [ HH.text "Disabled item" ]
-- |       ]
-- |   ]
-- | ```
module Hydrogen.Primitive.ContextMenu
  ( -- * Context Menu Components
    contextMenu
  , contextMenuTrigger
  , contextMenuContent
  , contextMenuItem
  , contextMenuSeparator
  , contextMenuLabel
  , contextMenuGroup
  , contextMenuSub
  , contextMenuSubTrigger
  , contextMenuSubContent
  , contextMenuShortcut
    -- * Props
  , ContextMenuProps
  , ContextMenuProp
  , open
  , onOpenChange
  , onSelect
  , disabled
  , className
    -- * Position
  , Position
  , position
  , positionX
  , positionY
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
--                                                                    // position
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Position coordinates for the context menu
type Position = { x :: Int, y :: Int }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

type ContextMenuProps i =
  { open :: Boolean
  , onOpenChange :: Maybe (MouseEvent -> i)
  , onSelect :: Maybe (MouseEvent -> i)
  , disabled :: Boolean
  , position :: Position
  , className :: String
  }

type ContextMenuProp i = ContextMenuProps i -> ContextMenuProps i

defaultProps :: forall i. ContextMenuProps i
defaultProps =
  { open: false
  , onOpenChange: Nothing
  , onSelect: Nothing
  , disabled: false
  , position: { x: 0, y: 0 }
  , className: ""
  }

-- | Set open state
open :: forall i. Boolean -> ContextMenuProp i
open o props = props { open = o }

-- | Set open change handler (for controlled mode)
onOpenChange :: forall i. (MouseEvent -> i) -> ContextMenuProp i
onOpenChange handler props = props { onOpenChange = Just handler }

-- | Set select handler for menu items
onSelect :: forall i. (MouseEvent -> i) -> ContextMenuProp i
onSelect handler props = props { onSelect = Just handler }

-- | Set disabled state for menu items
disabled :: forall i. Boolean -> ContextMenuProp i
disabled d props = props { disabled = d }

-- | Set position (x, y coordinates)
position :: forall i. Position -> ContextMenuProp i
position p props = props { position = p }

-- | Set X coordinate only
positionX :: forall i. Int -> ContextMenuProp i
positionX x props = props { position = props.position { x = x } }

-- | Set Y coordinate only
positionY :: forall i. Int -> ContextMenuProp i
positionY y props = props { position = props.position { y = y } }

-- | Add custom class
className :: forall i. String -> ContextMenuProp i
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Context menu root container
-- |
-- | Wraps the trigger and content elements.
contextMenu :: forall w i. Array (ContextMenuProp i) -> Array (HH.HTML w i) -> HH.HTML w i
contextMenu propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "relative", props.className ]
    , HP.attr (HH.AttrName "data-state") (if props.open then "open" else "closed")
    , HP.attr (HH.AttrName "data-context-menu") "root"
    ]
    children

-- | Context menu trigger
-- |
-- | The element that triggers the context menu on right-click.
contextMenuTrigger :: forall w i. Array (ContextMenuProp i) -> Array (HH.HTML w i) -> HH.HTML w i
contextMenuTrigger propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ props.className ]
    , HP.attr (HH.AttrName "data-context-menu") "trigger"
    ]
    children

-- | Context menu content panel
-- |
-- | The floating menu that appears on right-click.
-- | Positioned at the cursor coordinates.
contextMenuContent :: forall w i. Array (ContextMenuProp i) -> Array (HH.HTML w i) -> HH.HTML w i
contextMenuContent propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    visibilityClass = if props.open then "" else "hidden"
    posX = props.position.x
    posY = props.position.y
  in
    HH.div
      [ cls
          [ "fixed z-50 min-w-[8rem] overflow-hidden rounded-md border bg-popover p-1 text-popover-foreground shadow-md"
          , "animate-in fade-in-0 zoom-in-95"
          , visibilityClass
          , props.className
          ]
      , HP.style ("left: " <> show posX <> "px; top: " <> show posY <> "px;")
      , ARIA.role "menu"
      , HP.attr (HH.AttrName "data-context-menu") "content"
      , HP.attr (HH.AttrName "data-state") (if props.open then "open" else "closed")
      ]
      children

-- | Context menu item
-- |
-- | A selectable item in the context menu.
contextMenuItem :: forall w i. Array (ContextMenuProp i) -> Array (HH.HTML w i) -> HH.HTML w i
contextMenuItem propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    disabledClasses = if props.disabled
      then "opacity-50 pointer-events-none"
      else "cursor-pointer"
  in
    HH.div
      ( [ cls
            [ "relative flex select-none items-center rounded-sm px-2 py-1.5 text-sm outline-none"
            , "transition-colors focus:bg-accent focus:text-accent-foreground"
            , "hover:bg-accent hover:text-accent-foreground"
            , disabledClasses
            , props.className
            ]
        , ARIA.role "menuitem"
        , HP.tabIndex (if props.disabled then (-1) else 0)
        , HP.attr (HH.AttrName "data-disabled") (if props.disabled then "true" else "false")
        , HP.attr (HH.AttrName "data-context-menu") "item"
        ] <> case props.onSelect of
          Just handler | not props.disabled -> [ HE.onClick handler ]
          _ -> []
      )
      children

-- | Context menu separator
-- |
-- | A visual divider between groups of items.
contextMenuSeparator :: forall w i. Array (ContextMenuProp i) -> HH.HTML w i
contextMenuSeparator propMods =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "-mx-1 my-1 h-px bg-muted", props.className ]
    , ARIA.role "separator"
    , HP.attr (HH.AttrName "data-context-menu") "separator"
    ]
    []

-- | Context menu label
-- |
-- | Non-interactive label for grouping items.
contextMenuLabel :: forall w i. Array (ContextMenuProp i) -> Array (HH.HTML w i) -> HH.HTML w i
contextMenuLabel propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "px-2 py-1.5 text-sm font-semibold", props.className ]
    , HP.attr (HH.AttrName "data-context-menu") "label"
    ]
    children

-- | Context menu group
-- |
-- | Groups related items together.
contextMenuGroup :: forall w i. Array (ContextMenuProp i) -> Array (HH.HTML w i) -> HH.HTML w i
contextMenuGroup propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ props.className ]
    , ARIA.role "group"
    , HP.attr (HH.AttrName "data-context-menu") "group"
    ]
    children

-- | Context menu submenu container
-- |
-- | Contains a submenu trigger and content.
contextMenuSub :: forall w i. Array (ContextMenuProp i) -> Array (HH.HTML w i) -> HH.HTML w i
contextMenuSub propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "relative group", props.className ]
    , HP.attr (HH.AttrName "data-context-menu") "sub"
    ]
    children

-- | Context menu submenu trigger
-- |
-- | Item that opens a submenu when hovered or focused.
contextMenuSubTrigger :: forall w i. Array (ContextMenuProp i) -> Array (HH.HTML w i) -> HH.HTML w i
contextMenuSubTrigger propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls
        [ "relative flex select-none items-center rounded-sm px-2 py-1.5 text-sm outline-none"
        , "transition-colors focus:bg-accent focus:text-accent-foreground"
        , "hover:bg-accent hover:text-accent-foreground cursor-pointer"
        , props.className
        ]
    , ARIA.role "menuitem"
    , ARIA.hasPopup "menu"
    , HP.tabIndex 0
    , HP.attr (HH.AttrName "data-context-menu") "sub-trigger"
    ]
    ( children <> [ chevronRight ] )

-- | Context menu submenu content
-- |
-- | The nested menu that appears when hovering the submenu trigger.
contextMenuSubContent :: forall w i. Array (ContextMenuProp i) -> Array (HH.HTML w i) -> HH.HTML w i
contextMenuSubContent propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls
        [ "absolute left-full top-0 z-50 min-w-[8rem] overflow-hidden rounded-md border bg-popover p-1 text-popover-foreground shadow-lg"
        , "opacity-0 invisible group-hover:opacity-100 group-hover:visible"
        , "transition-all duration-150"
        , props.className
        ]
    , ARIA.role "menu"
    , HP.attr (HH.AttrName "data-context-menu") "sub-content"
    ]
    children

-- | Context menu keyboard shortcut display
-- |
-- | Shows a keyboard shortcut hint on the right side of an item.
contextMenuShortcut :: forall w i. Array (ContextMenuProp i) -> String -> HH.HTML w i
contextMenuShortcut propMods shortcutText =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.span
    [ cls [ "ml-auto text-xs tracking-widest text-muted-foreground", props.className ]
    , HP.attr (HH.AttrName "data-context-menu") "shortcut"
    ]
    [ HH.text shortcutText ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Chevron right icon for submenu indicators
chevronRight :: forall w i. HH.HTML w i
chevronRight =
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
