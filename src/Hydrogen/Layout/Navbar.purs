-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                         // hydrogen // navbar
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Navbar component
-- |
-- | A responsive navigation bar with logo, nav items, and actions.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Layout.Navbar as Navbar
-- |
-- | -- Basic navbar
-- | Navbar.navbar []
-- |   { brand: Just (HH.text "MyApp")
-- |   , items: 
-- |       [ Navbar.navItem { label: "Home", href: "/", active: true }
-- |       , Navbar.navItem { label: "About", href: "/about", active: false }
-- |       ]
-- |   , actions: Just userMenu
-- |   }
-- |
-- | -- Transparent navbar (for hero sections)
-- | Navbar.navbar
-- |   [ Navbar.variant Navbar.Transparent
-- |   , Navbar.sticky true
-- |   ]
-- |   slots
-- |
-- | -- With mobile menu
-- | Navbar.navbar
-- |   [ Navbar.mobileMenuOpen state.menuOpen
-- |   , Navbar.onMobileMenuToggle HandleToggle
-- |   ]
-- |   slots
-- | ```
module Hydrogen.Layout.Navbar
  ( -- * Navbar Components
    navbar
  , navItem
  , navGroup
  , navBrand
  , navActions
  , mobileMenuButton
    -- * Slots
  , NavbarSlots
    -- * NavItem Types
  , NavItemConfig
  , NavGroupConfig
    -- * Props
  , NavbarProps
  , NavbarProp
  , defaultProps
    -- * Prop Builders
  , variant
  , sticky
  , bordered
  , blur
  , height
  , maxWidth
  , mobileMenuOpen
  , mobileBreakpoint
  , className
  , onMobileMenuToggle
    -- * Variants
  , NavbarVariant(..)
  ) where

import Prelude

import Data.Array (foldl)
import Data.Maybe (Maybe(..))
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Navbar variants
data NavbarVariant
  = Default
  | Transparent
  | Blurred
  | Bordered

derive instance eqNavbarVariant :: Eq NavbarVariant

-- | Get variant classes
variantClasses :: NavbarVariant -> String
variantClasses = case _ of
  Default -> "bg-background border-b"
  Transparent -> "bg-transparent"
  Blurred -> "bg-background/80 backdrop-blur-md border-b"
  Bordered -> "bg-background border-b-2 border-primary"

-- | Navbar content slots
type NavbarSlots w i =
  { brand :: Maybe (HH.HTML w i)
  , items :: Array (HH.HTML w i)
  , actions :: Maybe (HH.HTML w i)
  }

-- | NavItem configuration
type NavItemConfig =
  { label :: String
  , href :: String
  , active :: Boolean
  , disabled :: Boolean
  }

-- | NavGroup configuration (dropdown)
type NavGroupConfig w i =
  { label :: String
  , items :: Array (HH.HTML w i)
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Navbar properties
type NavbarProps i =
  { variant :: NavbarVariant
  , sticky :: Boolean
  , bordered :: Boolean
  , blur :: Boolean
  , height :: String
  , maxWidth :: String
  , mobileMenuOpen :: Boolean
  , mobileBreakpoint :: String
  , className :: String
  , onMobileMenuToggle :: Maybe i
  }

-- | Property modifier
type NavbarProp i = NavbarProps i -> NavbarProps i

-- | Default properties
defaultProps :: forall i. NavbarProps i
defaultProps =
  { variant: Default
  , sticky: false
  , bordered: true
  , blur: false
  , height: "h-16"
  , maxWidth: "max-w-7xl"
  , mobileMenuOpen: false
  , mobileBreakpoint: "md"
  , className: ""
  , onMobileMenuToggle: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set variant
variant :: forall i. NavbarVariant -> NavbarProp i
variant v props = props { variant = v }

-- | Make sticky
sticky :: forall i. Boolean -> NavbarProp i
sticky s props = props { sticky = s }

-- | Show border
bordered :: forall i. Boolean -> NavbarProp i
bordered b props = props { bordered = b }

-- | Enable backdrop blur
blur :: forall i. Boolean -> NavbarProp i
blur b props = props { blur = b }

-- | Set height (Tailwind class)
height :: forall i. String -> NavbarProp i
height h props = props { height = h }

-- | Set max width (Tailwind class)
maxWidth :: forall i. String -> NavbarProp i
maxWidth m props = props { maxWidth = m }

-- | Set mobile menu open state
mobileMenuOpen :: forall i. Boolean -> NavbarProp i
mobileMenuOpen o props = props { mobileMenuOpen = o }

-- | Set mobile breakpoint
mobileBreakpoint :: forall i. String -> NavbarProp i
mobileBreakpoint b props = props { mobileBreakpoint = b }

-- | Add custom class
className :: forall i. String -> NavbarProp i
className c props = props { className = props.className <> " " <> c }

-- | Set mobile menu toggle handler
onMobileMenuToggle :: forall i. i -> NavbarProp i
onMobileMenuToggle handler props = props { onMobileMenuToggle = Just handler }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // styling
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Container classes
containerClasses :: String
containerClasses =
  "w-full z-40"

-- | Inner wrapper classes
wrapperClasses :: String
wrapperClasses =
  "mx-auto px-4 sm:px-6 lg:px-8"

-- | Flex container classes
flexClasses :: String
flexClasses =
  "flex items-center justify-between"

-- | Brand area classes
brandClasses :: String
brandClasses =
  "flex-shrink-0"

-- | Nav items container classes (desktop)
navItemsClasses :: String
navItemsClasses =
  "hidden md:flex md:items-center md:space-x-4"

-- | Actions area classes
actionsClasses :: String
actionsClasses =
  "hidden md:flex md:items-center md:space-x-4"

-- | Mobile menu button classes
menuButtonClasses :: String
menuButtonClasses =
  "inline-flex items-center justify-center p-2 rounded-md text-muted-foreground hover:text-foreground hover:bg-accent focus:outline-none focus:ring-2 focus:ring-ring md:hidden"

-- | Mobile menu panel classes
mobileMenuClasses :: String
mobileMenuClasses =
  "md:hidden border-t bg-background"

-- | Nav item classes
navItemBaseClasses :: String
navItemBaseClasses =
  "inline-flex items-center px-3 py-2 text-sm font-medium rounded-md transition-colors"

-- | Active nav item classes
navItemActiveClasses :: String
navItemActiveClasses =
  "text-foreground bg-accent"

-- | Inactive nav item classes
navItemInactiveClasses :: String
navItemInactiveClasses =
  "text-muted-foreground hover:text-foreground hover:bg-accent"

-- | Disabled nav item classes
navItemDisabledClasses :: String
navItemDisabledClasses =
  "text-muted-foreground/50 cursor-not-allowed"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create a nav item
navItem :: forall w i. NavItemConfig -> HH.HTML w i
navItem config =
  let
    stateClasses = 
      if config.disabled then navItemDisabledClasses
      else if config.active then navItemActiveClasses
      else navItemInactiveClasses
    
    ariaCurrent = if config.active then [ HP.attr (HH.AttrName "aria-current") "page" ] else []
  in
    HH.a
      ( [ cls [ navItemBaseClasses, stateClasses ]
        , HP.href config.href
        ] <> ariaCurrent
      )
      [ HH.text config.label ]

-- | Create a nav group (for dropdowns)
navGroup :: forall w i. NavGroupConfig w i -> HH.HTML w i
navGroup config =
  HH.div
    [ cls [ "relative" ] ]
    [ HH.button
        [ cls [ navItemBaseClasses, navItemInactiveClasses ]
        , HP.type_ HP.ButtonButton
        ]
        [ HH.text config.label
        , chevronDownIcon
        ]
    -- Dropdown content would be rendered here based on state
    ]

-- | Brand/logo area wrapper
navBrand :: forall w i. Array (HH.HTML w i) -> HH.HTML w i
navBrand children =
  HH.div
    [ cls [ brandClasses ] ]
    children

-- | Actions area wrapper
navActions :: forall w i. Array (HH.HTML w i) -> HH.HTML w i
navActions children =
  HH.div
    [ cls [ actionsClasses ] ]
    children

-- | Mobile menu toggle button
mobileMenuButton :: forall w i. { open :: Boolean, onClick :: Maybe i } -> HH.HTML w i
mobileMenuButton config =
  let
    clickHandler = case config.onClick of
      Just handler -> [ HE.onClick (\_ -> handler) ]
      Nothing -> []
  in
    HH.button
      ( [ cls [ menuButtonClasses ]
        , HP.type_ HP.ButtonButton
        , ARIA.expanded (show config.open)
        , ARIA.controls "mobile-menu"
        , ARIA.label (if config.open then "Close menu" else "Open menu")
        ] <> clickHandler
      )
      [ if config.open then closeIcon else menuIcon ]

-- | Full navbar component
navbar :: forall w i. Array (NavbarProp i) -> NavbarSlots w i -> HH.HTML w i
navbar propMods slots =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    -- Container classes
    containerCls = 
      containerClasses 
      <> " " <> variantClasses props.variant
      <> (if props.sticky then " sticky top-0" else "")
      <> " " <> props.className
  in
    HH.nav
      [ cls [ containerCls ]
      , ARIA.label "Main navigation"
      ]
      [ -- Desktop navbar
        HH.div
          [ cls [ wrapperClasses, props.maxWidth ] ]
          [ HH.div
              [ cls [ flexClasses, props.height ] ]
              [ -- Brand
                case slots.brand of
                  Just brand -> navBrand [ brand ]
                  Nothing -> HH.text ""
              -- Desktop nav items
              , HH.div
                  [ cls [ navItemsClasses ] ]
                  slots.items
              -- Desktop actions
              , case slots.actions of
                  Just actions -> 
                    HH.div 
                      [ cls [ actionsClasses ] ] 
                      [ actions ]
                  Nothing -> HH.text ""
              -- Mobile menu button
              , mobileMenuButton 
                  { open: props.mobileMenuOpen
                  , onClick: props.onMobileMenuToggle
                  }
              ]
          ]
      -- Mobile menu panel
      , if props.mobileMenuOpen
          then 
            HH.div
              [ cls [ mobileMenuClasses ]
              , HP.id "mobile-menu"
              ]
              [ HH.div
                  [ cls [ "px-2 pt-2 pb-3 space-y-1" ] ]
                  slots.items
              , case slots.actions of
                  Just actions ->
                    HH.div
                      [ cls [ "pt-4 pb-3 border-t" ] ]
                      [ actions ]
                  Nothing -> HH.text ""
              ]
          else HH.text ""
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // icons
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Menu (hamburger) icon
menuIcon :: forall w i. HH.HTML w i
menuIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "h-6 w-6" ]
    , HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "stroke-linecap") "round"
        , HP.attr (HH.AttrName "stroke-linejoin") "round"
        , HP.attr (HH.AttrName "d") "M4 6h16M4 12h16M4 18h16"
        ]
        []
    ]

-- | Close (X) icon
closeIcon :: forall w i. HH.HTML w i
closeIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "h-6 w-6" ]
    , HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "stroke-linecap") "round"
        , HP.attr (HH.AttrName "stroke-linejoin") "round"
        , HP.attr (HH.AttrName "d") "M6 18L18 6M6 6l12 12"
        ]
        []
    ]

-- | Chevron down icon (for dropdowns)
chevronDownIcon :: forall w i. HH.HTML w i
chevronDownIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "ml-1 h-4 w-4" ]
    , HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "stroke-linecap") "round"
        , HP.attr (HH.AttrName "stroke-linejoin") "round"
        , HP.attr (HH.AttrName "d") "M19 9l-7 7-7-7"
        ]
        []
    ]
