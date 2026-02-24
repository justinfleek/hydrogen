-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                         // hydrogen // drawer
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Drawer component
-- |
-- | Slide-out panels that appear from screen edges with overlay backdrop.
-- | Useful for navigation menus, settings panels, forms, and mobile layouts.
-- |
-- | ## Features
-- |
-- | - **Slide direction**: Left, right, top, or bottom edge
-- | - **Overlay backdrop**: Semi-transparent backdrop with click-to-close
-- | - **Sizes**: sm, md, lg, full width/height
-- | - **Close behaviors**: Backdrop click, escape key
-- | - **Focus trap**: Keep focus within drawer when open
-- | - **Scroll lock**: Prevent body scroll when drawer is open
-- | - **Smooth animations**: CSS-based slide and fade transitions
-- | - **Slots**: Header, body, and footer sections
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Primitive.Drawer as Drawer
-- |
-- | Drawer.drawer [ Drawer.open state.isOpen, Drawer.side Drawer.Right ]
-- |   [ Drawer.drawerOverlay [ Drawer.onClose CloseDrawer ]
-- |   , Drawer.drawerContent [ Drawer.size Drawer.Medium ]
-- |       [ Drawer.drawerHeader []
-- |           [ Drawer.drawerTitle [] [ HH.text "Settings" ]
-- |           , Drawer.drawerDescription [] [ HH.text "Configure app" ]
-- |           , Drawer.drawerClose [ Drawer.onClose CloseDrawer ]
-- |           ]
-- |       , Drawer.drawerBody []
-- |           [ HH.text "Drawer content goes here" ]
-- |       , Drawer.drawerFooter []
-- |           [ Button.button [] [ HH.text "Save" ]
-- |           , Button.button [] [ HH.text "Cancel" ]
-- |           ]
-- |       ]
-- |   ]
-- | ```
module Hydrogen.Primitive.Drawer
  ( -- * Drawer Components
    drawer
  , drawerOverlay
  , drawerContent
  , drawerHeader
  , drawerTitle
  , drawerDescription
  , drawerBody
  , drawerFooter
  , drawerClose
    -- * Props
  , DrawerProps
  , DrawerProp
  , open
  , onClose
  , className
    -- * Side
  , Side(Left, Right, Top, Bottom)
  , side
    -- * Size
  , Size(Small, Medium, Large, Full)
  , size
    -- * Options
  , closeOnEscape
  , closeOnBackdropClick
  , trapFocus
  , scrollLock
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
--                                                                        // side
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Side from which the drawer slides in
data Side
  = Left
  | Right
  | Top
  | Bottom

derive instance eqSide :: Eq Side

-- | CSS classes for positioning and animation based on side
sidePositionClasses :: Side -> String
sidePositionClasses = case _ of
  Left   -> "inset-y-0 left-0"
  Right  -> "inset-y-0 right-0"
  Top    -> "inset-x-0 top-0"
  Bottom -> "inset-x-0 bottom-0"

-- | Animation classes for slide-in effect
sideAnimationClasses :: Side -> Boolean -> String
sideAnimationClasses sd isOpen = case sd of
  Left   -> if isOpen then "translate-x-0" else "-translate-x-full"
  Right  -> if isOpen then "translate-x-0" else "translate-x-full"
  Top    -> if isOpen then "translate-y-0" else "-translate-y-full"
  Bottom -> if isOpen then "translate-y-0" else "translate-y-full"

-- | Data attribute value for side
sideToString :: Side -> String
sideToString = case _ of
  Left   -> "left"
  Right  -> "right"
  Top    -> "top"
  Bottom -> "bottom"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // size
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Drawer size options
data Size
  = Small   -- ^ 25% / 320px
  | Medium  -- ^ 50% / 480px
  | Large   -- ^ 75% / 640px
  | Full    -- ^ 100%

derive instance eqSize :: Eq Size

-- | Size classes for horizontal drawers (left/right)
sizeClassesHorizontal :: Size -> String
sizeClassesHorizontal = case _ of
  Small  -> "w-80 max-w-[25%]"
  Medium -> "w-[480px] max-w-[50%]"
  Large  -> "w-[640px] max-w-[75%]"
  Full   -> "w-full"

-- | Size classes for vertical drawers (top/bottom)
sizeClassesVertical :: Size -> String
sizeClassesVertical = case _ of
  Small  -> "h-40 max-h-[25%]"
  Medium -> "h-64 max-h-[50%]"
  Large  -> "h-96 max-h-[75%]"
  Full   -> "h-full"

-- | Get size classes based on drawer side
sizeClasses :: Side -> Size -> String
sizeClasses sd sz = case sd of
  Left   -> "h-full " <> sizeClassesHorizontal sz
  Right  -> "h-full " <> sizeClassesHorizontal sz
  Top    -> "w-full " <> sizeClassesVertical sz
  Bottom -> "w-full " <> sizeClassesVertical sz

-- | Data attribute value for size
sizeToString :: Size -> String
sizeToString = case _ of
  Small  -> "sm"
  Medium -> "md"
  Large  -> "lg"
  Full   -> "full"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

type DrawerProps i =
  { open :: Boolean
  , onClose :: Maybe (MouseEvent -> i)
  , side :: Side
  , size :: Size
  , closeOnEscape :: Boolean
  , closeOnBackdropClick :: Boolean
  , trapFocus :: Boolean
  , scrollLock :: Boolean
  , className :: String
  }

type DrawerProp i = DrawerProps i -> DrawerProps i

defaultProps :: forall i. DrawerProps i
defaultProps =
  { open: false
  , onClose: Nothing
  , side: Right
  , size: Medium
  , closeOnEscape: true
  , closeOnBackdropClick: true
  , trapFocus: true
  , scrollLock: true
  , className: ""
  }

-- | Set open state
open :: forall i. Boolean -> DrawerProp i
open o props = props { open = o }

-- | Set close handler
onClose :: forall i. (MouseEvent -> i) -> DrawerProp i
onClose handler props = props { onClose = Just handler }

-- | Set drawer side (where it slides from)
side :: forall i. Side -> DrawerProp i
side s props = props { side = s }

-- | Set drawer size
size :: forall i. Size -> DrawerProp i
size sz props = props { size = sz }

-- | Close drawer when Escape key is pressed
closeOnEscape :: forall i. Boolean -> DrawerProp i
closeOnEscape enabled props = props { closeOnEscape = enabled }

-- | Close drawer when clicking backdrop
closeOnBackdropClick :: forall i. Boolean -> DrawerProp i
closeOnBackdropClick enabled props = props { closeOnBackdropClick = enabled }

-- | Trap focus within drawer when open
trapFocus :: forall i. Boolean -> DrawerProp i
trapFocus enabled props = props { trapFocus = enabled }

-- | Lock body scroll when drawer is open
scrollLock :: forall i. Boolean -> DrawerProp i
scrollLock enabled props = props { scrollLock = enabled }

-- | Add custom class
className :: forall i. String -> DrawerProp i
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Drawer root container
-- |
-- | Creates a fixed overlay container for the drawer.
-- | Hidden when closed, visible when open.
drawer :: forall w i. Array (DrawerProp i) -> Array (HH.HTML w i) -> HH.HTML w i
drawer propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    visibilityClass = if props.open then "" else "invisible"
  in
    HH.div
      [ cls [ "fixed inset-0 z-50", visibilityClass, props.className ]
      , ARIA.role "dialog"
      , ARIA.modal "true"
      , HP.attr (HH.AttrName "data-state") (if props.open then "open" else "closed")
      , HP.attr (HH.AttrName "data-drawer") "root"
      , HP.attr (HH.AttrName "data-side") (sideToString props.side)
      , HP.attr (HH.AttrName "data-size") (sizeToString props.size)
      , HP.attr (HH.AttrName "data-close-on-escape") (if props.closeOnEscape then "true" else "false")
      , HP.attr (HH.AttrName "data-trap-focus") (if props.trapFocus then "true" else "false")
      , HP.attr (HH.AttrName "data-scroll-lock") (if props.scrollLock then "true" else "false")
      ]
      children

-- | Drawer overlay (backdrop)
-- |
-- | Semi-transparent backdrop behind the drawer.
-- | Clicking the overlay closes the drawer (if enabled).
drawerOverlay :: forall w i. Array (DrawerProp i) -> HH.HTML w i
drawerOverlay propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    visibilityClass = if props.open
      then "opacity-100"
      else "opacity-0 pointer-events-none"
  in
    HH.div
      ( [ cls
            [ "fixed inset-0 z-50 bg-black/80 transition-opacity duration-300"
            , visibilityClass
            , props.className
            ]
        , HP.attr (HH.AttrName "data-drawer") "overlay"
        ] <> case props.onClose of
          Just handler | props.closeOnBackdropClick -> [ HE.onClick handler ]
          _ -> []
      )
      []

-- | Drawer content panel
-- |
-- | The main drawer panel that slides in from the specified side.
-- | Contains header, body, and footer slots.
drawerContent :: forall w i. Array (DrawerProp i) -> Array (HH.HTML w i) -> HH.HTML w i
drawerContent propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    animClass = sideAnimationClasses props.side props.open
  in
    HH.div
      [ cls
          [ "fixed z-50 flex flex-col bg-background shadow-lg transition-transform duration-300 ease-out"
          , sidePositionClasses props.side
          , sizeClasses props.side props.size
          , animClass
          , props.className
          ]
      , HP.attr (HH.AttrName "data-drawer") "content"
      , HP.attr (HH.AttrName "data-state") (if props.open then "open" else "closed")
      ]
      children

-- | Drawer header
-- |
-- | Container for title, description, and close button.
drawerHeader :: forall w i. Array (DrawerProp i) -> Array (HH.HTML w i) -> HH.HTML w i
drawerHeader propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "flex flex-col space-y-2 p-6 border-b", props.className ]
    , HP.attr (HH.AttrName "data-drawer") "header"
    ]
    children

-- | Drawer title
drawerTitle :: forall w i. Array (DrawerProp i) -> Array (HH.HTML w i) -> HH.HTML w i
drawerTitle propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.h2
    [ cls [ "text-lg font-semibold leading-none tracking-tight", props.className ] ]
    children

-- | Drawer description
drawerDescription :: forall w i. Array (DrawerProp i) -> Array (HH.HTML w i) -> HH.HTML w i
drawerDescription propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.p
    [ cls [ "text-sm text-muted-foreground", props.className ] ]
    children

-- | Drawer body (main content area)
-- |
-- | Scrollable content area between header and footer.
drawerBody :: forall w i. Array (DrawerProp i) -> Array (HH.HTML w i) -> HH.HTML w i
drawerBody propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "flex-1 overflow-auto p-6", props.className ]
    , HP.attr (HH.AttrName "data-drawer") "body"
    ]
    children

-- | Drawer footer
-- |
-- | Fixed footer section for actions like save/cancel buttons.
drawerFooter :: forall w i. Array (DrawerProp i) -> Array (HH.HTML w i) -> HH.HTML w i
drawerFooter propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "flex flex-col-reverse sm:flex-row sm:justify-end gap-2 p-6 border-t", props.className ]
    , HP.attr (HH.AttrName "data-drawer") "footer"
    ]
    children

-- | Drawer close button
-- |
-- | Positioned close button (typically in header).
-- | Shows an X icon by default.
drawerClose :: forall w i. Array (DrawerProp i) -> HH.HTML w i
drawerClose propMods =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.button
    ( [ cls
          [ "absolute right-4 top-4 rounded-sm opacity-70 ring-offset-background"
          , "transition-opacity hover:opacity-100 focus:outline-none focus:ring-2"
          , "focus:ring-ring focus:ring-offset-2 disabled:pointer-events-none"
          , props.className
          ]
      , HP.type_ HP.ButtonButton
      , HP.attr (HH.AttrName "data-drawer") "close"
      ] <> case props.onClose of
        Just handler -> [ HE.onClick handler ]
        Nothing -> []
    )
    [ closeIcon ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Default close icon (X)
closeIcon :: forall w i. HH.HTML w i
closeIcon =
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
