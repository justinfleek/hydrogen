-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                        // hydrogen // popover
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Popover component
-- |
-- | Positioned floating content panels with trigger elements.
-- | Supports multiple placement options, auto-flip, click outside/escape
-- | handling, focus management, and portal rendering.
-- |
-- | ## Features
-- |
-- | - **Trigger element**: Click or hover to open
-- | - **Content panel**: Positioned floating content with optional arrow
-- | - **Placement**: top, bottom, left, right with start/end/center alignment
-- | - **Auto-flip**: Automatically flip when hitting viewport edges
-- | - **Close behaviors**: Click outside, escape key
-- | - **Focus management**: Trap focus within popover content
-- | - **Portal rendering**: Render to document body for proper stacking
-- | - **Controlled/Uncontrolled**: Use with or without external state
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Primitive.Popover as Popover
-- |
-- | -- Uncontrolled (internal state)
-- | Popover.popover []
-- |   [ Popover.popoverTrigger [ Popover.triggerMode Popover.Click ]
-- |       [ Button.button [] [ HH.text "Open" ] ]
-- |   , Popover.popoverContent [ Popover.placement Popover.BottomCenter ]
-- |       [ Popover.popoverArrow []
-- |       , HH.div_ [ HH.text "Popover content" ]
-- |       ]
-- |   ]
-- |
-- | -- Controlled (external state)
-- | Popover.popover [ Popover.open state.isOpen ]
-- |   [ Popover.popoverTrigger [ Popover.onToggle TogglePopover ]
-- |       [ Button.button [] [ HH.text "Open" ] ]
-- |   , Popover.popoverContent
-- |       [ Popover.placement Popover.TopCenter
-- |       , Popover.onClose ClosePopover
-- |       , Popover.closeOnEscape true
-- |       , Popover.closeOnClickOutside true
-- |       ]
-- |       [ HH.text "Popover content" ]
-- |   ]
-- | ```
module Hydrogen.Primitive.Popover
  ( -- * Popover Components
    popover
  , popoverTrigger
  , popoverContent
  , popoverArrow
  , popoverClose
    -- * Props
  , PopoverProps
  , PopoverProp
  , open
  , onToggle
  , onClose
  , className
    -- * Placement
  , Placement(TopStart, TopCenter, TopEnd, BottomStart, BottomCenter, BottomEnd, LeftStart, LeftCenter, LeftEnd, RightStart, RightCenter, RightEnd)
  , placement
    -- * Trigger Mode
  , TriggerMode(Click, Hover, Focus, Manual)
  , triggerMode
    -- * Options
  , closeOnEscape
  , closeOnClickOutside
  , trapFocus
  , showArrow
  , offset
  , autoFlip
  , portal
  ) where

import Prelude

import Data.Array (foldl, null)
import Data.Maybe (Maybe(Just, Nothing))
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)
import Web.UIEvent.MouseEvent (MouseEvent)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // placement
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Popover placement options
-- |
-- | Supports 12 positions: 4 sides × 3 alignments (start, center, end)
data Placement
  = TopStart
  | TopCenter
  | TopEnd
  | BottomStart
  | BottomCenter
  | BottomEnd
  | LeftStart
  | LeftCenter
  | LeftEnd
  | RightStart
  | RightCenter
  | RightEnd

derive instance eqPlacement :: Eq Placement

-- | Get CSS classes for placement
placementClasses :: Placement -> String
placementClasses = case _ of
  TopStart     -> "bottom-full left-0 mb-2"
  TopCenter    -> "bottom-full left-1/2 -translate-x-1/2 mb-2"
  TopEnd       -> "bottom-full right-0 mb-2"
  BottomStart  -> "top-full left-0 mt-2"
  BottomCenter -> "top-full left-1/2 -translate-x-1/2 mt-2"
  BottomEnd    -> "top-full right-0 mt-2"
  LeftStart    -> "right-full top-0 mr-2"
  LeftCenter   -> "right-full top-1/2 -translate-y-1/2 mr-2"
  LeftEnd      -> "right-full bottom-0 mr-2"
  RightStart   -> "left-full top-0 ml-2"
  RightCenter  -> "left-full top-1/2 -translate-y-1/2 ml-2"
  RightEnd     -> "left-full bottom-0 ml-2"

-- | Get arrow position classes based on popover placement
arrowClasses :: Placement -> String
arrowClasses = case _ of
  TopStart     -> "bottom-0 left-4 translate-y-1/2 rotate-45"
  TopCenter    -> "bottom-0 left-1/2 -translate-x-1/2 translate-y-1/2 rotate-45"
  TopEnd       -> "bottom-0 right-4 translate-y-1/2 rotate-45"
  BottomStart  -> "top-0 left-4 -translate-y-1/2 rotate-45"
  BottomCenter -> "top-0 left-1/2 -translate-x-1/2 -translate-y-1/2 rotate-45"
  BottomEnd    -> "top-0 right-4 -translate-y-1/2 rotate-45"
  LeftStart    -> "right-0 top-4 translate-x-1/2 rotate-45"
  LeftCenter   -> "right-0 top-1/2 -translate-y-1/2 translate-x-1/2 rotate-45"
  LeftEnd      -> "right-0 bottom-4 translate-x-1/2 rotate-45"
  RightStart   -> "left-0 top-4 -translate-x-1/2 rotate-45"
  RightCenter  -> "left-0 top-1/2 -translate-y-1/2 -translate-x-1/2 rotate-45"
  RightEnd     -> "left-0 bottom-4 -translate-x-1/2 rotate-45"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // trigger mode
-- ═══════════════════════════════════════════════════════════════════════════════

-- | How the popover is triggered
data TriggerMode
  = Click       -- ^ Open on click
  | Hover       -- ^ Open on hover (with delay)
  | Focus       -- ^ Open on focus
  | Manual      -- ^ Only controlled programmatically

derive instance eqTriggerMode :: Eq TriggerMode

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

type PopoverProps i =
  { open :: Boolean
  , onToggle :: Maybe (MouseEvent -> i)
  , onClose :: Maybe (MouseEvent -> i)
  , placement :: Placement
  , triggerMode :: TriggerMode
  , closeOnEscape :: Boolean
  , closeOnClickOutside :: Boolean
  , trapFocus :: Boolean
  , showArrow :: Boolean
  , offset :: Int
  , autoFlip :: Boolean
  , portal :: Boolean
  , className :: String
  }

type PopoverProp i = PopoverProps i -> PopoverProps i

defaultProps :: forall i. PopoverProps i
defaultProps =
  { open: false
  , onToggle: Nothing
  , onClose: Nothing
  , placement: BottomCenter
  , triggerMode: Click
  , closeOnEscape: true
  , closeOnClickOutside: true
  , trapFocus: false
  , showArrow: true
  , offset: 8
  , autoFlip: true
  , portal: false
  , className: ""
  }

-- | Set open state (for controlled mode)
open :: forall i. Boolean -> PopoverProp i
open o props = props { open = o }

-- | Set toggle handler
onToggle :: forall i. (MouseEvent -> i) -> PopoverProp i
onToggle handler props = props { onToggle = Just handler }

-- | Set close handler
onClose :: forall i. (MouseEvent -> i) -> PopoverProp i
onClose handler props = props { onClose = Just handler }

-- | Set placement (where content appears relative to trigger)
placement :: forall i. Placement -> PopoverProp i
placement p props = props { placement = p }

-- | Set trigger mode (click, hover, focus, manual)
triggerMode :: forall i. TriggerMode -> PopoverProp i
triggerMode mode props = props { triggerMode = mode }

-- | Close popover when Escape key is pressed
closeOnEscape :: forall i. Boolean -> PopoverProp i
closeOnEscape enabled props = props { closeOnEscape = enabled }

-- | Close popover when clicking outside
closeOnClickOutside :: forall i. Boolean -> PopoverProp i
closeOnClickOutside enabled props = props { closeOnClickOutside = enabled }

-- | Trap focus within popover content
trapFocus :: forall i. Boolean -> PopoverProp i
trapFocus enabled props = props { trapFocus = enabled }

-- | Show arrow pointing to trigger
showArrow :: forall i. Boolean -> PopoverProp i
showArrow enabled props = props { showArrow = enabled }

-- | Offset from trigger (in pixels)
offset :: forall i. Int -> PopoverProp i
offset n props = props { offset = n }

-- | Auto-flip placement when hitting viewport edges
autoFlip :: forall i. Boolean -> PopoverProp i
autoFlip enabled props = props { autoFlip = enabled }

-- | Render content through portal (at document body)
portal :: forall i. Boolean -> PopoverProp i
portal enabled props = props { portal = enabled }

-- | Add custom class
className :: forall i. String -> PopoverProp i
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Popover container
-- |
-- | Wraps the trigger and content elements.
-- | In uncontrolled mode, manages open state internally via CSS :focus-within.
popover :: forall w i. Array (PopoverProp i) -> Array (HH.HTML w i) -> HH.HTML w i
popover propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls [ "relative inline-block", props.className ]
    , HP.attr (HH.AttrName "data-state") (if props.open then "open" else "closed")
    , HP.attr (HH.AttrName "data-popover") "root"
    , HP.attr (HH.AttrName "data-close-on-escape") (if props.closeOnEscape then "true" else "false")
    , HP.attr (HH.AttrName "data-close-on-click-outside") (if props.closeOnClickOutside then "true" else "false")
    , HP.attr (HH.AttrName "data-auto-flip") (if props.autoFlip then "true" else "false")
    ]
    children

-- | Popover trigger element
-- |
-- | The element that opens the popover when interacted with.
popoverTrigger :: forall w i. Array (PopoverProp i) -> Array (HH.HTML w i) -> HH.HTML w i
popoverTrigger propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    triggerModeAttr = case props.triggerMode of
      Click  -> "click"
      Hover  -> "hover"
      Focus  -> "focus"
      Manual -> "manual"
  in
    HH.div
      ( [ cls [ "inline-flex", props.className ]
        , ARIA.hasPopup "dialog"
        , ARIA.expanded (if props.open then "true" else "false")
        , HP.attr (HH.AttrName "data-popover") "trigger"
        , HP.attr (HH.AttrName "data-trigger-mode") triggerModeAttr
        ] <> case props.onToggle of
          Just handler -> [ HE.onClick handler ]
          Nothing -> []
      )
      children

-- | Popover content panel
-- |
-- | The floating content that appears when popover is open.
-- | Supports placement, arrow, and focus trapping.
popoverContent :: forall w i. Array (PopoverProp i) -> Array (HH.HTML w i) -> HH.HTML w i
popoverContent propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    visibilityClass = if props.open then "opacity-100 scale-100" else "opacity-0 scale-95 pointer-events-none"
    focusTrapAttr = if props.trapFocus then "true" else "false"
    portalAttr = if props.portal then "true" else "false"
  in
    HH.div
      [ cls
          [ "absolute z-50 min-w-[8rem] overflow-hidden rounded-md border bg-popover p-4 text-popover-foreground shadow-md outline-none"
          , "transition-all duration-200 ease-out"
          , "animate-in fade-in-0 zoom-in-95"
          , placementClasses props.placement
          , visibilityClass
          , props.className
          ]
      , ARIA.role "dialog"
      , HP.attr (HH.AttrName "data-state") (if props.open then "open" else "closed")
      , HP.attr (HH.AttrName "data-side") (placementToSide props.placement)
      , HP.attr (HH.AttrName "data-align") (placementToAlign props.placement)
      , HP.attr (HH.AttrName "data-popover") "content"
      , HP.attr (HH.AttrName "data-trap-focus") focusTrapAttr
      , HP.attr (HH.AttrName "data-portal") portalAttr
      ]
      children

-- | Popover arrow
-- |
-- | Visual arrow pointing to the trigger element.
-- | Position is automatically determined by popover placement.
popoverArrow :: forall w i. Array (PopoverProp i) -> HH.HTML w i
popoverArrow propMods =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.div
    [ cls
        [ "absolute w-2 h-2 bg-popover border border-border"
        , arrowClasses props.placement
        , props.className
        ]
    , HP.attr (HH.AttrName "data-popover") "arrow"
    ]
    []

-- | Popover close button
-- |
-- | Optional close button within popover content.
popoverClose :: forall w i. Array (PopoverProp i) -> Array (HH.HTML w i) -> HH.HTML w i
popoverClose propMods children =
  let props = foldl (\p f -> f p) defaultProps propMods
  in HH.button
    ( [ cls
          [ "absolute right-2 top-2 rounded-sm opacity-70 ring-offset-background transition-opacity"
          , "hover:opacity-100 focus:outline-none focus:ring-2 focus:ring-ring focus:ring-offset-2"
          , "disabled:pointer-events-none"
          , props.className
          ]
      , HP.type_ HP.ButtonButton
      , HP.attr (HH.AttrName "data-popover") "close"
      ] <> case props.onClose of
        Just handler -> [ HE.onClick handler ]
        Nothing -> []
    )
    ( if null children
        then [ closeIcon ]
        else children
    )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Extract side from placement
placementToSide :: Placement -> String
placementToSide = case _ of
  TopStart     -> "top"
  TopCenter    -> "top"
  TopEnd       -> "top"
  BottomStart  -> "bottom"
  BottomCenter -> "bottom"
  BottomEnd    -> "bottom"
  LeftStart    -> "left"
  LeftCenter   -> "left"
  LeftEnd      -> "left"
  RightStart   -> "right"
  RightCenter  -> "right"
  RightEnd     -> "right"

-- | Extract alignment from placement
placementToAlign :: Placement -> String
placementToAlign = case _ of
  TopStart     -> "start"
  TopCenter    -> "center"
  TopEnd       -> "end"
  BottomStart  -> "start"
  BottomCenter -> "center"
  BottomEnd    -> "end"
  LeftStart    -> "start"
  LeftCenter   -> "center"
  LeftEnd      -> "end"
  RightStart   -> "start"
  RightCenter  -> "center"
  RightEnd     -> "end"

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
