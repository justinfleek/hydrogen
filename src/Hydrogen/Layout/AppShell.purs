-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // hydrogen // appshell
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Application shell layout component
-- |
-- | Complete application layout with header, sidebar, main content,
-- | and footer slots. Handles responsive behavior and scroll management.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Layout.AppShell as AppShell
-- |
-- | -- Basic app shell
-- | AppShell.appShell []
-- |   { header: Just navbar
-- |   , sidebar: Just navigation
-- |   , content: mainContent
-- |   , footer: Just footerContent
-- |   }
-- |
-- | -- Without sidebar
-- | AppShell.appShell [ AppShell.layout AppShell.Stacked ]
-- |   { header: Just header
-- |   , sidebar: Nothing
-- |   , content: landingPage
-- |   , footer: Just footer
-- |   }
-- |
-- | -- Fixed header, scrollable content
-- | AppShell.appShell
-- |   [ AppShell.fixedHeader true
-- |   , AppShell.scrollBehavior AppShell.ContentOnly
-- |   ]
-- |   { header: Just stickyNav
-- |   , sidebar: Just sidebar
-- |   , content: longContent
-- |   , footer: Nothing
-- |   }
-- |
-- | -- Collapsible sidebar shell
-- | AppShell.appShell
-- |   [ AppShell.sidebarCollapsed state.collapsed
-- |   , AppShell.sidebarCollapsible true
-- |   , AppShell.onSidebarCollapse \c -> setState { collapsed: c }
-- |   ]
-- |   slots
-- | ```
module Hydrogen.Layout.AppShell
  ( -- * Component
    appShell
    -- * Slot Types
  , AppShellSlots
    -- * Props
  , AppShellProps
  , AppShellProp
  , layout
  , fixedHeader
  , fixedSidebar
  , fixedFooter
  , headerHeight
  , footerHeight
  , sidebarWidth
  , sidebarMiniWidth
  , sidebarPosition
  , sidebarCollapsible
  , sidebarCollapsed
  , sidebarMiniMode
  , scrollBehavior
  , mobileBreakpoint
  , onSidebarCollapse
  , className
  , headerClassName
  , sidebarClassName
  , contentClassName
  , footerClassName
    -- * Layout Types
  , Layout(..)
    -- * Scroll Behavior
  , ScrollBehavior(..)
    -- * Position
  , Position(..)
    -- * Breakpoint
  , Breakpoint(..)
  ) where

import Prelude

import Data.Array (foldl)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // layout
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Layout variants
data Layout
  = SidebarFirst    -- ^ Sidebar beside header, content below both
  | HeaderFirst     -- ^ Header above all, sidebar beside content
  | Stacked         -- ^ No sidebar, header -> content -> footer

derive instance eqLayout :: Eq Layout

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // scroll behavior
-- ═══════════════════════════════════════════════════════════════════════════════

-- | How scrolling is handled
data ScrollBehavior
  = PageScroll      -- ^ Entire page scrolls
  | ContentOnly     -- ^ Only content area scrolls
  | IndependentScroll  -- ^ Sidebar and content scroll independently

derive instance eqScrollBehavior :: Eq ScrollBehavior

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
--                                                                       // slots
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Content slots for the app shell
type AppShellSlots w i =
  { header :: Maybe (HH.HTML w i)
  , sidebar :: Maybe (HH.HTML w i)
  , content :: HH.HTML w i
  , footer :: Maybe (HH.HTML w i)
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

type AppShellProps =
  { layout :: Layout
  , fixedHeader :: Boolean
  , fixedSidebar :: Boolean
  , fixedFooter :: Boolean
  , headerHeight :: String
  , footerHeight :: String
  , sidebarWidth :: String
  , sidebarMiniWidth :: String
  , sidebarPosition :: Position
  , sidebarCollapsible :: Boolean
  , sidebarCollapsed :: Boolean
  , sidebarMiniMode :: Boolean
  , scrollBehavior :: ScrollBehavior
  , mobileBreakpoint :: Breakpoint
  , onSidebarCollapse :: Maybe (Boolean -> Effect Unit)
  , className :: String
  , headerClassName :: String
  , sidebarClassName :: String
  , contentClassName :: String
  , footerClassName :: String
  }

type AppShellProp = AppShellProps -> AppShellProps

defaultProps :: AppShellProps
defaultProps =
  { layout: HeaderFirst
  , fixedHeader: true
  , fixedSidebar: true
  , fixedFooter: false
  , headerHeight: "64px"
  , footerHeight: "auto"
  , sidebarWidth: "256px"
  , sidebarMiniWidth: "64px"
  , sidebarPosition: Left
  , sidebarCollapsible: false
  , sidebarCollapsed: false
  , sidebarMiniMode: false
  , scrollBehavior: ContentOnly
  , mobileBreakpoint: Lg
  , onSidebarCollapse: Nothing
  , className: ""
  , headerClassName: ""
  , sidebarClassName: ""
  , contentClassName: ""
  , footerClassName: ""
  }

-- | Set layout type
layout :: Layout -> AppShellProp
layout l props = props { layout = l }

-- | Set header as fixed
fixedHeader :: Boolean -> AppShellProp
fixedHeader f props = props { fixedHeader = f }

-- | Set sidebar as fixed
fixedSidebar :: Boolean -> AppShellProp
fixedSidebar f props = props { fixedSidebar = f }

-- | Set footer as fixed
fixedFooter :: Boolean -> AppShellProp
fixedFooter f props = props { fixedFooter = f }

-- | Set header height
headerHeight :: String -> AppShellProp
headerHeight h props = props { headerHeight = h }

-- | Set footer height
footerHeight :: String -> AppShellProp
footerHeight h props = props { footerHeight = h }

-- | Set sidebar width
sidebarWidth :: String -> AppShellProp
sidebarWidth w props = props { sidebarWidth = w }

-- | Set mini sidebar width
sidebarMiniWidth :: String -> AppShellProp
sidebarMiniWidth w props = props { sidebarMiniWidth = w }

-- | Set sidebar position
sidebarPosition :: Position -> AppShellProp
sidebarPosition p props = props { sidebarPosition = p }

-- | Enable collapsible sidebar
sidebarCollapsible :: Boolean -> AppShellProp
sidebarCollapsible c props = props { sidebarCollapsible = c }

-- | Set sidebar collapsed state
sidebarCollapsed :: Boolean -> AppShellProp
sidebarCollapsed c props = props { sidebarCollapsed = c }

-- | Enable mini mode for collapsed sidebar
sidebarMiniMode :: Boolean -> AppShellProp
sidebarMiniMode m props = props { sidebarMiniMode = m }

-- | Set scroll behavior
scrollBehavior :: ScrollBehavior -> AppShellProp
scrollBehavior s props = props { scrollBehavior = s }

-- | Set mobile breakpoint
mobileBreakpoint :: Breakpoint -> AppShellProp
mobileBreakpoint b props = props { mobileBreakpoint = b }

-- | Handle sidebar collapse
onSidebarCollapse :: (Boolean -> Effect Unit) -> AppShellProp
onSidebarCollapse f props = props { onSidebarCollapse = Just f }

-- | Add custom class to container
className :: String -> AppShellProp
className c props = props { className = props.className <> " " <> c }

-- | Add custom class to header
headerClassName :: String -> AppShellProp
headerClassName c props = props { headerClassName = props.headerClassName <> " " <> c }

-- | Add custom class to sidebar
sidebarClassName :: String -> AppShellProp
sidebarClassName c props = props { sidebarClassName = props.sidebarClassName <> " " <> c }

-- | Add custom class to content
contentClassName :: String -> AppShellProp
contentClassName c props = props { contentClassName = props.contentClassName <> " " <> c }

-- | Add custom class to footer
footerClassName :: String -> AppShellProp
footerClassName c props = props { footerClassName = props.footerClassName <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // component
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Application shell layout
-- |
-- | Provides a complete application layout with configurable header,
-- | sidebar, content, and footer slots. Handles responsive behavior,
-- | fixed positioning, and scroll management.
appShell :: forall w i. Array AppShellProp -> AppShellSlots w i -> HH.HTML w i
appShell propMods slots =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    bp = breakpointClass props.mobileBreakpoint
    
    -- Calculate effective sidebar width
    effectiveSidebarWidth = 
      if props.sidebarCollapsed 
        then if props.sidebarMiniMode then props.sidebarMiniWidth else "0px"
        else props.sidebarWidth
    
    -- Overflow handling based on scroll behavior
    containerOverflow = case props.scrollBehavior of
      PageScroll -> "overflow-auto"
      ContentOnly -> "overflow-hidden"
      IndependentScroll -> "overflow-hidden"
    
    contentOverflow = case props.scrollBehavior of
      PageScroll -> ""
      ContentOnly -> "overflow-auto"
      IndependentScroll -> "overflow-auto"
    
    sidebarOverflow = case props.scrollBehavior of
      PageScroll -> ""
      ContentOnly -> ""
      IndependentScroll -> "overflow-auto"
  in
    case props.layout of
      -- Header above everything, sidebar beside content
      HeaderFirst -> renderHeaderFirst props bp effectiveSidebarWidth 
                      containerOverflow contentOverflow sidebarOverflow slots
      
      -- Sidebar full height, header beside content
      SidebarFirst -> renderSidebarFirst props bp effectiveSidebarWidth
                       containerOverflow contentOverflow sidebarOverflow slots
      
      -- No sidebar, stacked layout
      Stacked -> renderStacked props containerOverflow contentOverflow slots

-- | Render HeaderFirst layout
renderHeaderFirst :: forall w i. 
  AppShellProps -> String -> String -> String -> String -> String -> 
  AppShellSlots w i -> HH.HTML w i
renderHeaderFirst props bp sidebarW containerOverflow contentOverflow sidebarOverflow slots =
  HH.div
    [ cls [ "flex flex-col h-screen w-screen", containerOverflow, props.className ]
    , HP.attr (HH.AttrName "data-appshell") "header-first"
    ]
    [ -- Header
      case slots.header of
        Just header -> HH.header
          [ cls [ "shrink-0 z-20 bg-background border-b border-border"
                , if props.fixedHeader then "sticky top-0" else ""
                , props.headerClassName
                ]
          , HP.style ("height: " <> props.headerHeight <> "; min-height: " <> props.headerHeight)
          ]
          [ header ]
        Nothing -> HH.text ""
      -- Body (sidebar + content)
    , HH.div
        [ cls [ "flex flex-1 min-h-0"
              , case props.sidebarPosition of
                  Left -> "flex-row"
                  Right -> "flex-row-reverse"
              ]
        ]
        [ -- Sidebar
          case slots.sidebar of
            Just sidebarContent -> HH.aside
              [ cls [ "shrink-0 bg-background border-border z-10"
                    , sidebarOverflow
                    , case props.sidebarPosition of
                        Left -> "border-r"
                        Right -> "border-l"
                    , "hidden " <> bp <> ":block"
                    , props.sidebarClassName
                    ]
              , HP.style ("width: " <> sidebarW)
              , HP.attr (HH.AttrName "data-appshell-sidebar") "true"
              ]
              [ sidebarContent ]
            Nothing -> HH.text ""
          -- Main content
        , HH.div
            [ cls [ "flex-1 flex flex-col min-w-0", contentOverflow, props.contentClassName ]
            , HP.attr (HH.AttrName "data-appshell-content") "true"
            , HP.attr (HH.AttrName "role") "main"
            ]
            [ slots.content
              -- Footer inside content if not fixed
            , case slots.footer of
                Just footer | not props.fixedFooter -> HH.footer
                  [ cls [ "shrink-0 bg-background border-t border-border", props.footerClassName ]
                  , HP.style ("min-height: " <> props.footerHeight)
                  ]
                  [ footer ]
                _ -> HH.text ""
            ]
        ]
      -- Fixed footer
    , case slots.footer of
        Just footer | props.fixedFooter -> HH.footer
          [ cls [ "shrink-0 z-20 bg-background border-t border-border"
                , "sticky bottom-0"
                , props.footerClassName
                ]
          , HP.style ("min-height: " <> props.footerHeight)
          ]
          [ footer ]
        _ -> HH.text ""
    ]

-- | Render SidebarFirst layout
renderSidebarFirst :: forall w i.
  AppShellProps -> String -> String -> String -> String -> String ->
  AppShellSlots w i -> HH.HTML w i
renderSidebarFirst props bp sidebarW containerOverflow contentOverflow sidebarOverflow slots =
  HH.div
    [ cls [ "flex h-screen w-screen", containerOverflow
          , case props.sidebarPosition of
              Left -> "flex-row"
              Right -> "flex-row-reverse"
          , props.className
          ]
    , HP.attr (HH.AttrName "data-appshell") "sidebar-first"
    ]
    [ -- Sidebar (full height)
      case slots.sidebar of
        Just sidebarContent -> HH.aside
          [ cls [ "shrink-0 flex flex-col bg-background border-border z-20"
                , sidebarOverflow
                , case props.sidebarPosition of
                    Left -> "border-r"
                    Right -> "border-l"
                , "hidden " <> bp <> ":flex"
                , props.sidebarClassName
                ]
          , HP.style ("width: " <> sidebarW)
          , HP.attr (HH.AttrName "data-appshell-sidebar") "true"
          ]
          [ sidebarContent ]
        Nothing -> HH.text ""
      -- Right side (header + content + footer)
    , HH.div
        [ cls [ "flex-1 flex flex-col min-w-0" ] ]
        [ -- Header
          case slots.header of
            Just header -> HH.header
              [ cls [ "shrink-0 z-10 bg-background border-b border-border"
                    , if props.fixedHeader then "sticky top-0" else ""
                    , props.headerClassName
                    ]
              , HP.style ("height: " <> props.headerHeight)
              ]
              [ header ]
            Nothing -> HH.text ""
          -- Main content
        , HH.div
            [ cls [ "flex-1 min-h-0", contentOverflow, props.contentClassName ]
            , HP.attr (HH.AttrName "data-appshell-content") "true"
            , HP.attr (HH.AttrName "role") "main"
            ]
            [ slots.content ]
          -- Footer
        , case slots.footer of
            Just footer -> HH.footer
              [ cls [ "shrink-0 bg-background border-t border-border"
                    , if props.fixedFooter then "sticky bottom-0" else ""
                    , props.footerClassName
                    ]
              , HP.style ("min-height: " <> props.footerHeight)
              ]
              [ footer ]
            Nothing -> HH.text ""
        ]
    ]

-- | Render Stacked layout (no sidebar)
renderStacked :: forall w i.
  AppShellProps -> String -> String ->
  AppShellSlots w i -> HH.HTML w i
renderStacked props containerOverflow contentOverflow slots =
  HH.div
    [ cls [ "flex flex-col h-screen w-screen", containerOverflow, props.className ]
    , HP.attr (HH.AttrName "data-appshell") "stacked"
    ]
    [ -- Header
      case slots.header of
        Just header -> HH.header
          [ cls [ "shrink-0 z-20 bg-background border-b border-border"
                , if props.fixedHeader then "sticky top-0" else ""
                , props.headerClassName
                ]
          , HP.style ("height: " <> props.headerHeight)
          ]
          [ header ]
        Nothing -> HH.text ""
      -- Main content
    , HH.div
        [ cls [ "flex-1 min-h-0", contentOverflow, props.contentClassName ]
        , HP.attr (HH.AttrName "data-appshell-content") "true"
        , HP.attr (HH.AttrName "role") "main"
        ]
        [ slots.content ]
      -- Footer
    , case slots.footer of
        Just footer -> HH.footer
          [ cls [ "shrink-0 bg-background border-t border-border"
                , if props.fixedFooter then "sticky bottom-0" else ""
                , props.footerClassName
                ]
          , HP.style ("min-height: " <> props.footerHeight)
          ]
          [ footer ]
        Nothing -> HH.text ""
    ]
