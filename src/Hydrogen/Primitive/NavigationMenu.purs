-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                 // hydrogen // navigationmenu
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Mega Navigation Menu component
-- |
-- | Horizontal navigation with rich dropdown panels supporting grids,
-- | featured items, and complex layouts. Viewport-aware positioning
-- | with mobile collapse support.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Primitive.NavigationMenu as NavMenu
-- |
-- | NavMenu.navigationMenu []
-- |   [ NavMenu.navigationMenuList []
-- |       [ NavMenu.navigationMenuItem []
-- |           [ NavMenu.navigationMenuTrigger
-- |               [ NavMenu.active (state.activeNav == "products") ]
-- |               [ HH.text "Products" ]
-- |           , NavMenu.navigationMenuContent []
-- |               [ NavMenu.navigationMenuGrid []
-- |                   [ NavMenu.navigationMenuCard
-- |                       [ NavMenu.href "/product-1"
-- |                       , NavMenu.title "Product One"
-- |                       , NavMenu.description "Description of product"
-- |                       ]
-- |                       []
-- |                   , NavMenu.navigationMenuCard
-- |                       [ NavMenu.href "/product-2" ]
-- |                       [ HH.text "Product Two" ]
-- |                   ]
-- |               ]
-- |           ]
-- |       , NavMenu.navigationMenuItem []
-- |           [ NavMenu.navigationMenuLink
-- |               [ NavMenu.href "/about"
-- |               , NavMenu.active (state.currentPath == "/about")
-- |               ]
-- |               [ HH.text "About" ]
-- |           ]
-- |       ]
-- |   ]
-- | ```
-- |
-- | ## Rich Content Panels
-- |
-- | ```purescript
-- | NavMenu.navigationMenuContent []
-- |   [ HH.div [ cls [ "grid grid-cols-3 gap-4 p-4" ] ]
-- |       [ -- Featured section
-- |         HH.div [ cls [ "col-span-2 row-span-2" ] ]
-- |           [ NavMenu.navigationMenuFeatured
-- |               [ NavMenu.href "/featured"
-- |               , NavMenu.title "Featured Item"
-- |               , NavMenu.description "Highlighted content"
-- |               , NavMenu.image "/featured.jpg"
-- |               ]
-- |               []
-- |           ]
-- |       , -- Regular links
-- |         NavMenu.navigationMenuLink [ NavMenu.href "/link-1" ]
-- |           [ HH.text "Link 1" ]
-- |       , NavMenu.navigationMenuLink [ NavMenu.href "/link-2" ]
-- |           [ HH.text "Link 2" ]
-- |       ]
-- |   ]
-- | ```
-- |
-- | ## Mobile Support
-- |
-- | ```purescript
-- | -- Mobile hamburger menu trigger
-- | NavMenu.navigationMenuMobileTrigger
-- |   [ NavMenu.open state.mobileMenuOpen
-- |   , NavMenu.onToggle ToggleMobileMenu
-- |   ]
-- |   []
-- |
-- | -- Collapsible content for mobile
-- | NavMenu.navigationMenuMobileContent
-- |   [ NavMenu.open state.mobileMenuOpen ]
-- |   [ -- Mobile menu items
-- |   ]
-- | ```
module Hydrogen.Primitive.NavigationMenu
  ( -- * Navigation Menu Components
    navigationMenu
  , navigationMenuList
  , navigationMenuItem
  , navigationMenuTrigger
  , navigationMenuContent
  , navigationMenuLink
  , navigationMenuGrid
  , navigationMenuCard
  , navigationMenuFeatured
  , navigationMenuIndicator
  , navigationMenuViewport
    -- * Mobile Components
  , navigationMenuMobileTrigger
  , navigationMenuMobileContent
    -- * Props
  , NavigationMenuProps
  , NavigationMenuProp
  , open
  , active
  , disabled
  , href
  , title
  , description
  , image
  , onToggle
  , onSelect
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

-- | Navigation menu properties
type NavigationMenuProps i =
  { open :: Boolean
  , active :: Boolean
  , disabled :: Boolean
  , href :: String
  , title :: String
  , description :: String
  , image :: String
  , onToggle :: Maybe (MouseEvent -> i)
  , onSelect :: Maybe (MouseEvent -> i)
  , className :: String
  }

type NavigationMenuProp i = NavigationMenuProps i -> NavigationMenuProps i

defaultProps :: forall i. NavigationMenuProps i
defaultProps =
  { open: false
  , active: false
  , disabled: false
  , href: ""
  , title: ""
  , description: ""
  , image: ""
  , onToggle: Nothing
  , onSelect: Nothing
  , className: ""
  }

-- | Set open state
open :: forall i. Boolean -> NavigationMenuProp i
open o props = props { open = o }

-- | Set active state
active :: forall i. Boolean -> NavigationMenuProp i
active a props = props { active = a }

-- | Set disabled state
disabled :: forall i. Boolean -> NavigationMenuProp i
disabled d props = props { disabled = d }

-- | Set href
href :: forall i. String -> NavigationMenuProp i
href h props = props { href = h }

-- | Set title
title :: forall i. String -> NavigationMenuProp i
title t props = props { title = t }

-- | Set description
description :: forall i. String -> NavigationMenuProp i
description d props = props { description = d }

-- | Set image URL
image :: forall i. String -> NavigationMenuProp i
image img props = props { image = img }

-- | Set toggle handler
onToggle :: forall i. (MouseEvent -> i) -> NavigationMenuProp i
onToggle handler props = props { onToggle = Just handler }

-- | Set select handler
onSelect :: forall i. (MouseEvent -> i) -> NavigationMenuProp i
onSelect handler props = props { onSelect = Just handler }

-- | Add custom class
className :: forall i. String -> NavigationMenuProp i
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Navigation menu root container
-- |
-- | The main container for the entire navigation system.
navigationMenu :: forall w i. Array (NavigationMenuProp i) -> Array (HH.HTML w i) -> HH.HTML w i
navigationMenu propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.nav
    [ cls [ "relative z-10", props.className ]
    , ARIA.label "Main"
    ]
    children

-- | Navigation menu list
-- |
-- | The horizontal list of navigation items.
navigationMenuList :: forall w i. Array (NavigationMenuProp i) -> Array (HH.HTML w i) -> HH.HTML w i
navigationMenuList propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.ul
    [ cls [ "group flex flex-1 list-none items-center justify-center space-x-1", props.className ]
    , ARIA.role "menubar"
    ]
    children

-- | Navigation menu item
-- |
-- | A single item in the navigation menu (can contain trigger + content or just a link).
navigationMenuItem :: forall w i. Array (NavigationMenuProp i) -> Array (HH.HTML w i) -> HH.HTML w i
navigationMenuItem propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.li
    [ cls [ "relative group/item", props.className ]
    , ARIA.role "none"
    ]
    children

-- | Navigation menu trigger
-- |
-- | Button that opens a dropdown panel. Use for items with submenus.
navigationMenuTrigger :: forall w i. Array (NavigationMenuProp i) -> Array (HH.HTML w i) -> HH.HTML w i
navigationMenuTrigger propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    activeClasses = if props.active
      then "text-accent-foreground"
      else ""
    openClasses = if props.open
      then "bg-accent/50"
      else ""
  in
    HH.button
      ( [ cls [ "group inline-flex h-10 w-max items-center justify-center rounded-md bg-background px-4 py-2 text-sm font-medium transition-colors hover:bg-accent hover:text-accent-foreground focus:bg-accent focus:text-accent-foreground focus:outline-none disabled:pointer-events-none disabled:opacity-50", activeClasses, openClasses, props.className ]
        , HP.type_ HP.ButtonButton
        , ARIA.role "menuitem"
        , ARIA.hasPopup "menu"
        , ARIA.expanded (if props.open then "true" else "false")
        , HP.attr (HH.AttrName "data-state") (if props.open then "open" else "closed")
        ] <> case props.onToggle of
          Just handler -> [ HE.onClick handler ]
          Nothing -> []
      )
      [ HH.span_ children
      , chevronDownIcon props.open
      ]

-- | Navigation menu content
-- |
-- | The dropdown panel containing rich content, grids, or links.
navigationMenuContent :: forall w i. Array (NavigationMenuProp i) -> Array (HH.HTML w i) -> HH.HTML w i
navigationMenuContent propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    visibilityClasses = if props.open
      then "opacity-100 visible translate-y-0"
      else "opacity-0 invisible -translate-y-2 group-hover/item:opacity-100 group-hover/item:visible group-hover/item:translate-y-0"
  in
    HH.div
      [ cls [ "absolute left-0 top-full z-50 w-screen max-w-md transform transition-all duration-200 ease-out md:w-auto", visibilityClasses, props.className ]
      , ARIA.role "menu"
      , HP.attr (HH.AttrName "data-state") (if props.open then "open" else "closed")
      ]
      [ HH.div
          [ cls [ "mt-2 rounded-md border bg-popover p-4 text-popover-foreground shadow-lg" ] ]
          children
      ]

-- | Navigation menu link
-- |
-- | A simple navigation link without dropdown.
navigationMenuLink :: forall w i. Array (NavigationMenuProp i) -> Array (HH.HTML w i) -> HH.HTML w i
navigationMenuLink propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    activeClasses = if props.active
      then "text-accent-foreground bg-accent/50"
      else ""
    disabledClasses = if props.disabled
      then "opacity-50 pointer-events-none"
      else ""
  in
    HH.a
      ( [ cls [ "group inline-flex h-10 w-max items-center justify-center rounded-md bg-background px-4 py-2 text-sm font-medium transition-colors hover:bg-accent hover:text-accent-foreground focus:bg-accent focus:text-accent-foreground focus:outline-none", activeClasses, disabledClasses, props.className ]
        , ARIA.role "menuitem"
        ] <> (if props.href /= "" then [ HP.href props.href ] else [])
          <> case props.onSelect of
            Just handler | not props.disabled -> [ HE.onClick handler ]
            _ -> []
      )
      children

-- | Navigation menu grid
-- |
-- | Grid layout for organizing content within dropdown panels.
navigationMenuGrid :: forall w i. Array (NavigationMenuProp i) -> Array (HH.HTML w i) -> HH.HTML w i
navigationMenuGrid propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "grid gap-3 md:grid-cols-2 lg:w-[500px]", props.className ] ]
    children

-- | Navigation menu card
-- |
-- | A card-style link within a dropdown panel.
navigationMenuCard :: forall w i. Array (NavigationMenuProp i) -> Array (HH.HTML w i) -> HH.HTML w i
navigationMenuCard propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.a
    ( [ cls [ "block select-none space-y-1 rounded-md p-3 leading-none no-underline outline-none transition-colors hover:bg-accent hover:text-accent-foreground focus:bg-accent focus:text-accent-foreground", props.className ]
      ] <> (if props.href /= "" then [ HP.href props.href ] else [])
    )
    ( [ if props.title /= ""
          then HH.div
            [ cls [ "text-sm font-medium leading-none" ] ]
            [ HH.text props.title ]
          else HH.text ""
      , if props.description /= ""
          then HH.p
            [ cls [ "line-clamp-2 text-sm leading-snug text-muted-foreground" ] ]
            [ HH.text props.description ]
          else HH.text ""
      ] <> children
    )

-- | Navigation menu featured item
-- |
-- | A larger featured card with optional image background.
navigationMenuFeatured :: forall w i. Array (NavigationMenuProp i) -> Array (HH.HTML w i) -> HH.HTML w i
navigationMenuFeatured propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    bgStyle = if props.image /= ""
      then [ HP.attr (HH.AttrName "style") ("background-image: url(" <> props.image <> "); background-size: cover; background-position: center;") ]
      else []
  in
    HH.a
      ( [ cls [ "flex h-full w-full select-none flex-col justify-end rounded-md bg-gradient-to-b from-muted/50 to-muted p-6 no-underline outline-none focus:shadow-md", props.className ]
        ] <> bgStyle
          <> (if props.href /= "" then [ HP.href props.href ] else [])
    )
    [ if props.title /= ""
        then HH.div
          [ cls [ "mb-2 mt-4 text-lg font-medium" ] ]
          [ HH.text props.title ]
        else HH.text ""
    , if props.description /= ""
        then HH.p
          [ cls [ "text-sm leading-tight text-muted-foreground" ] ]
          [ HH.text props.description ]
        else HH.text ""
    , HH.div_ children
    ]

-- | Navigation menu indicator
-- |
-- | Visual indicator showing which menu is active (animated underline).
navigationMenuIndicator :: forall w i. Array (NavigationMenuProp i) -> HH.HTML w i
navigationMenuIndicator propMods =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "absolute bottom-0 left-0 h-0.5 w-full origin-left bg-primary transition-transform duration-200", props.className ]
    , HP.attr (HH.AttrName "data-state") (if props.active then "visible" else "hidden")
    ]
    []

-- | Navigation menu viewport
-- |
-- | Container for dropdown content that handles viewport-aware positioning.
navigationMenuViewport :: forall w i. Array (NavigationMenuProp i) -> Array (HH.HTML w i) -> HH.HTML w i
navigationMenuViewport propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "absolute left-0 top-full flex justify-center", props.className ] ]
    [ HH.div
        [ cls [ "relative mt-1.5 h-[var(--radix-navigation-menu-viewport-height)] w-full overflow-hidden rounded-md border bg-popover text-popover-foreground shadow-lg md:w-[var(--radix-navigation-menu-viewport-width)] origin-top-center transition-[width,height] duration-200" ]
        , HP.attr (HH.AttrName "data-state") (if props.open then "open" else "closed")
        ]
        children
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // mobile components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Mobile hamburger menu trigger
navigationMenuMobileTrigger :: forall w i. Array (NavigationMenuProp i) -> Array (HH.HTML w i) -> HH.HTML w i
navigationMenuMobileTrigger propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.button
    ( [ cls [ "inline-flex items-center justify-center rounded-md p-2.5 text-muted-foreground hover:bg-accent hover:text-accent-foreground focus:outline-none focus:ring-2 focus:ring-ring md:hidden", props.className ]
      , HP.type_ HP.ButtonButton
      , ARIA.label (if props.open then "Close menu" else "Open menu")
      , ARIA.expanded (if props.open then "true" else "false")
      , ARIA.controls "mobile-menu"
      ] <> case props.onToggle of
        Just handler -> [ HE.onClick handler ]
        Nothing -> []
    )
    ( if props.open then [ closeIcon ] else [ hamburgerIcon ] )

-- | Mobile menu content
navigationMenuMobileContent :: forall w i. Array (NavigationMenuProp i) -> Array (HH.HTML w i) -> HH.HTML w i
navigationMenuMobileContent propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    visibilityClasses = if props.open
      then "block"
      else "hidden"
  in
    HH.div
      [ cls [ "md:hidden", visibilityClasses, props.className ]
      , HP.id "mobile-menu"
      ]
      [ HH.div
          [ cls [ "space-y-1 px-2 pb-3 pt-2" ] ]
          children
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // icons
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Chevron down icon (rotates when open)
chevronDownIcon :: forall w i. Boolean -> HH.HTML w i
chevronDownIcon isOpen =
  let rotateClass = if isOpen then "rotate-180" else ""
  in HH.elementNS
    (HH.Namespace "http://www.w3.org/2000/svg")
    (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "class") ("relative top-[1px] ml-1 h-3 w-3 transition duration-200 " <> rotateClass)
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , HP.attr (HH.AttrName "stroke-linejoin") "round"
    , HP.attr (HH.AttrName "aria-hidden") "true"
    ]
    [ HH.elementNS
        (HH.Namespace "http://www.w3.org/2000/svg")
        (HH.ElemName "polyline")
        [ HP.attr (HH.AttrName "points") "6 9 12 15 18 9" ]
        []
    ]

-- | Hamburger menu icon
hamburgerIcon :: forall w i. HH.HTML w i
hamburgerIcon =
  HH.elementNS
    (HH.Namespace "http://www.w3.org/2000/svg")
    (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "class") "h-6 w-6"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , HP.attr (HH.AttrName "stroke-linejoin") "round"
    , HP.attr (HH.AttrName "aria-hidden") "true"
    ]
    [ HH.elementNS
        (HH.Namespace "http://www.w3.org/2000/svg")
        (HH.ElemName "line")
        [ HP.attr (HH.AttrName "x1") "3"
        , HP.attr (HH.AttrName "y1") "12"
        , HP.attr (HH.AttrName "x2") "21"
        , HP.attr (HH.AttrName "y2") "12"
        ]
        []
    , HH.elementNS
        (HH.Namespace "http://www.w3.org/2000/svg")
        (HH.ElemName "line")
        [ HP.attr (HH.AttrName "x1") "3"
        , HP.attr (HH.AttrName "y1") "6"
        , HP.attr (HH.AttrName "x2") "21"
        , HP.attr (HH.AttrName "y2") "6"
        ]
        []
    , HH.elementNS
        (HH.Namespace "http://www.w3.org/2000/svg")
        (HH.ElemName "line")
        [ HP.attr (HH.AttrName "x1") "3"
        , HP.attr (HH.AttrName "y1") "18"
        , HP.attr (HH.AttrName "x2") "21"
        , HP.attr (HH.AttrName "y2") "18"
        ]
        []
    ]

-- | Close (X) icon
closeIcon :: forall w i. HH.HTML w i
closeIcon =
  HH.elementNS
    (HH.Namespace "http://www.w3.org/2000/svg")
    (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "class") "h-6 w-6"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , HP.attr (HH.AttrName "stroke-linejoin") "round"
    , HP.attr (HH.AttrName "aria-hidden") "true"
    ]
    [ HH.elementNS
        (HH.Namespace "http://www.w3.org/2000/svg")
        (HH.ElemName "line")
        [ HP.attr (HH.AttrName "x1") "18"
        , HP.attr (HH.AttrName "y1") "6"
        , HP.attr (HH.AttrName "x2") "6"
        , HP.attr (HH.AttrName "y2") "18"
        ]
        []
    , HH.elementNS
        (HH.Namespace "http://www.w3.org/2000/svg")
        (HH.ElemName "line")
        [ HP.attr (HH.AttrName "x1") "6"
        , HP.attr (HH.AttrName "y1") "6"
        , HP.attr (HH.AttrName "x2") "18"
        , HP.attr (HH.AttrName "y2") "18"
        ]
        []
    ]
