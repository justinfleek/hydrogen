-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                        // hydrogen // sidebar
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Sidebar layout component
-- |
-- | Fixed sidebar with scrollable content area. Supports collapsible,
-- | mobile drawer mode, and mini (icons-only) mode.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Layout.Sidebar as Sidebar
-- |
-- | -- Basic sidebar layout
-- | Sidebar.sidebar []
-- |   { sidebar: navigationMenu
-- |   , content: mainContent
-- |   }
-- |
-- | -- Collapsible sidebar
-- | Sidebar.sidebar
-- |   [ Sidebar.collapsible true
-- |   , Sidebar.collapsed state.sidebarCollapsed
-- |   , Sidebar.onCollapse \c -> setState { sidebarCollapsed: c }
-- |   ]
-- |   { sidebar: nav, content: main }
-- |
-- | -- Right-positioned sidebar
-- | Sidebar.sidebar [ Sidebar.position Sidebar.Right ]
-- |   { sidebar: detailsPanel, content: list }
-- |
-- | -- Mini mode (icons only when collapsed)
-- | Sidebar.sidebar
-- |   [ Sidebar.miniMode true
-- |   , Sidebar.collapsed true
-- |   ]
-- |   { sidebar: iconNav, content: main }
-- | ```
module Hydrogen.Layout.Sidebar
  ( -- * Component
    sidebar
    -- * Props
  , SidebarProps
  , SidebarProp
  , SidebarContent
  , position
  , width
  , miniWidth
  , collapsible
  , collapsed
  , miniMode
  , mobileBreakpoint
  , mobileDrawer
  , overlay
  , onCollapse
  , className
  , sidebarClassName
  , contentClassName
    -- * Position
  , Position(..)
    -- * Breakpoint
  , Breakpoint(..)
  ) where

import Prelude

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just))
import Effect (Effect)
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // position
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Sidebar position
data Position
  = Left
  | Right

derive instance eqPosition :: Eq Position

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // breakpoint
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Mobile breakpoint
data Breakpoint
  = Sm    -- ^ 640px
  | Md    -- ^ 768px
  | Lg    -- ^ 1024px
  | Xl    -- ^ 1280px

derive instance eqBreakpoint :: Eq Breakpoint

breakpointClass :: Breakpoint -> String
breakpointClass = case _ of
  Sm -> "sm"
  Md -> "md"
  Lg -> "lg"
  Xl -> "xl"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Content for sidebar layout
type SidebarContent w i =
  { sidebar :: HH.HTML w i
  , content :: HH.HTML w i
  }

type SidebarProps =
  { position :: Position
  , width :: String            -- CSS width value
  , miniWidth :: String        -- Width when in mini mode
  , collapsible :: Boolean
  , collapsed :: Boolean
  , miniMode :: Boolean
  , mobileBreakpoint :: Breakpoint
  , mobileDrawer :: Boolean    -- Show as drawer on mobile
  , overlay :: Boolean         -- Show overlay when mobile drawer open
  , onCollapse :: Maybe (Boolean -> Effect Unit)
  , className :: String
  , sidebarClassName :: String
  , contentClassName :: String
  }

type SidebarProp = SidebarProps -> SidebarProps

defaultProps :: SidebarProps
defaultProps =
  { position: Left
  , width: "256px"
  , miniWidth: "64px"
  , collapsible: false
  , collapsed: false
  , miniMode: false
  , mobileBreakpoint: Lg
  , mobileDrawer: true
  , overlay: true
  , onCollapse: Nothing
  , className: ""
  , sidebarClassName: ""
  , contentClassName: ""
  }

-- | Set sidebar position
position :: Position -> SidebarProp
position p props = props { position = p }

-- | Set sidebar width
width :: String -> SidebarProp
width w props = props { width = w }

-- | Set mini mode width
miniWidth :: String -> SidebarProp
miniWidth w props = props { miniWidth = w }

-- | Enable collapsible sidebar
collapsible :: Boolean -> SidebarProp
collapsible c props = props { collapsible = c }

-- | Set collapsed state
collapsed :: Boolean -> SidebarProp
collapsed c props = props { collapsed = c }

-- | Enable mini mode (icons only when collapsed)
miniMode :: Boolean -> SidebarProp
miniMode m props = props { miniMode = m }

-- | Set mobile breakpoint
mobileBreakpoint :: Breakpoint -> SidebarProp
mobileBreakpoint b props = props { mobileBreakpoint = b }

-- | Enable mobile drawer mode
mobileDrawer :: Boolean -> SidebarProp
mobileDrawer d props = props { mobileDrawer = d }

-- | Enable overlay when drawer is open
overlay :: Boolean -> SidebarProp
overlay o props = props { overlay = o }

-- | Handle collapse events
onCollapse :: (Boolean -> Effect Unit) -> SidebarProp
onCollapse f props = props { onCollapse = Just f }

-- | Add custom class to container
className :: String -> SidebarProp
className c props = props { className = props.className <> " " <> c }

-- | Add custom class to sidebar
sidebarClassName :: String -> SidebarProp
sidebarClassName c props = props { sidebarClassName = props.sidebarClassName <> " " <> c }

-- | Add custom class to content
contentClassName :: String -> SidebarProp
contentClassName c props = props { contentClassName = props.contentClassName <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // component
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Sidebar layout container
-- |
-- | Creates a fixed sidebar with scrollable main content.
-- | Supports responsive behavior, collapsible states, and mobile drawer mode.
sidebar :: forall w i. Array SidebarProp -> SidebarContent w i -> HH.HTML w i
sidebar propMods content =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    bp = breakpointClass props.mobileBreakpoint
    
    -- Calculate effective width
    effectiveWidth = 
      if props.collapsed 
        then if props.miniMode then props.miniWidth else "0px"
        else props.width
    
    -- Container layout direction
    containerDirection = case props.position of
      Left -> "flex-row"
      Right -> "flex-row-reverse"
    
    -- Sidebar visibility classes for responsive
    sidebarVisibility = 
      if props.mobileDrawer 
        then bp <> ":translate-x-0 " <> 
             (if props.collapsed 
                then "translate-x-full" 
                else "translate-x-0")
        else ""
    
    -- Sidebar position classes
    sidebarPosition = case props.position of
      Left -> "left-0"
      Right -> "right-0"
    
    -- Mobile drawer styles
    mobileStyles = 
      if props.mobileDrawer
        then "fixed " <> bp <> ":relative z-40 " <> bp <> ":z-auto top-0 bottom-0 transition-transform duration-300"
        else "relative"
  in
    HH.div
      [ cls [ "flex h-full w-full overflow-hidden", containerDirection, props.className ]
      , HP.attr (HH.AttrName "data-sidebar") "true"
      ]
      [ -- Overlay for mobile drawer
        if props.mobileDrawer && props.overlay && not props.collapsed
          then HH.div
            [ cls [ bp <> ":hidden fixed inset-0 bg-black/50 z-30 transition-opacity" ] 
            ]
            []
          else HH.text ""
        -- Sidebar
      , HH.aside
          [ cls [ "flex flex-col bg-background border-border shrink-0 overflow-y-auto overflow-x-hidden"
                , sidebarPosition, mobileStyles, sidebarVisibility
                , case props.position of
                    Left -> "border-r"
                    Right -> "border-l"
                , props.sidebarClassName
                ]
          , HP.style ("width: " <> effectiveWidth <> "; min-width: " <> effectiveWidth)
          , HP.attr (HH.AttrName "data-sidebar-panel") "true"
          , HP.attr (HH.AttrName "data-collapsed") (if props.collapsed then "true" else "false")
          ]
          [ content.sidebar ]
        -- Main content
      , HH.div
          [ cls [ "flex-1 overflow-auto min-w-0", props.contentClassName ]
          , HP.attr (HH.AttrName "data-sidebar-content") "true"
          , HP.attr (HH.AttrName "role") "main"
          ]
          [ content.content ]
      ]
