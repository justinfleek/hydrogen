-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                     // hydrogen // collapsible
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Collapsible/expandable content component
-- |
-- | Animated expand/collapse panels with trigger elements.
-- |
-- | ## Features
-- |
-- | - Trigger element (clickable)
-- | - Animated expand/collapse
-- | - Open/closed state
-- | - Controlled mode
-- | - Lazy render content option
-- | - Icon rotation animation
-- | - Disabled state
-- | - Accessible (ARIA expanded)
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Collapsible as Collapsible
-- |
-- | -- Basic collapsible
-- | Collapsible.collapsible
-- |   [ Collapsible.onToggle HandleToggle ]
-- |   (Collapsible.trigger [] [ HH.text "Click to expand" ])
-- |   (Collapsible.content [] [ HH.text "Hidden content here" ])
-- |
-- | -- Controlled collapsible
-- | Collapsible.collapsible
-- |   [ Collapsible.isOpen state.expanded
-- |   , Collapsible.onToggle ToggleExpanded
-- |   ]
-- |   (Collapsible.trigger [] [ HH.text "Settings" ])
-- |   (Collapsible.content [] settingsContent)
-- |
-- | -- With icon
-- | Collapsible.collapsible
-- |   [ Collapsible.isOpen true
-- |   , Collapsible.showIcon true
-- |   ]
-- |   (Collapsible.triggerWithIcon [] "Advanced Options")
-- |   (Collapsible.content [] advancedContent)
-- |
-- | -- Disabled
-- | Collapsible.collapsible
-- |   [ Collapsible.disabled true ]
-- |   trigger
-- |   content
-- | ```
module Hydrogen.Component.Collapsible
  ( -- * Components
    collapsible
  , trigger
  , triggerWithIcon
  , content
    -- * Props
  , CollapsibleProps
  , CollapsibleProp
  , TriggerProps
  , TriggerProp
  , ContentProps
  , ContentProp
  , defaultProps
  , defaultTriggerProps
  , defaultContentProps
    -- * Prop Builders
  , isOpen
  , onToggle
  , disabled
  , showIcon
  , iconPosition
  , lazyRender
  , animationDuration
  , className
  , triggerClassName
  , contentClassName
    -- * Types
  , IconPosition(..)
    -- * FFI
  , CollapsibleElement
  , initCollapsible
  , destroyCollapsible
  , toggle
  , open
  , close
  ) where

import Prelude

import Data.Array (foldl)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Uncurried (EffectFn1, EffectFn2)
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)
import Web.UIEvent.MouseEvent (MouseEvent)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Icon position relative to trigger text
data IconPosition
  = IconLeft
  | IconRight

derive instance eqIconPosition :: Eq IconPosition

-- | Opaque collapsible element for FFI
foreign import data CollapsibleElement :: Type

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Initialize collapsible with animation
foreign import initCollapsibleImpl :: EffectFn2 
  { container :: String, duration :: Int }
  { onOpen :: Effect Unit, onClose :: Effect Unit }
  CollapsibleElement

-- | Destroy collapsible
foreign import destroyCollapsibleImpl :: EffectFn1 CollapsibleElement Unit

-- | Toggle collapsible state
foreign import toggleImpl :: EffectFn1 CollapsibleElement Boolean

-- | Open collapsible
foreign import openImpl :: EffectFn1 CollapsibleElement Unit

-- | Close collapsible
foreign import closeImpl :: EffectFn1 CollapsibleElement Unit

-- | Initialize collapsible
initCollapsible :: 
  { container :: String, duration :: Int } ->
  { onOpen :: Effect Unit, onClose :: Effect Unit } ->
  Effect CollapsibleElement
initCollapsible opts callbacks = pure unsafeCollapsibleElement

-- | Destroy collapsible
destroyCollapsible :: CollapsibleElement -> Effect Unit
destroyCollapsible _ = pure unit

-- | Toggle state
toggle :: CollapsibleElement -> Effect Boolean
toggle _ = pure false

-- | Open
open :: CollapsibleElement -> Effect Unit
open _ = pure unit

-- | Close
close :: CollapsibleElement -> Effect Unit
close _ = pure unit

-- Internal placeholder
foreign import unsafeCollapsibleElement :: CollapsibleElement

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Collapsible properties
type CollapsibleProps i =
  { isOpen :: Boolean
  , onToggle :: Maybe (Boolean -> i)
  , disabled :: Boolean
  , showIcon :: Boolean
  , iconPosition :: IconPosition
  , lazyRender :: Boolean
  , animationDuration :: Int
  , className :: String
  }

-- | Collapsible property modifier
type CollapsibleProp i = CollapsibleProps i -> CollapsibleProps i

-- | Default collapsible properties
defaultProps :: forall i. CollapsibleProps i
defaultProps =
  { isOpen: false
  , onToggle: Nothing
  , disabled: false
  , showIcon: true
  , iconPosition: IconRight
  , lazyRender: false
  , animationDuration: 200
  , className: ""
  }

-- | Trigger properties
type TriggerProps =
  { className :: String
  }

-- | Trigger property modifier
type TriggerProp = TriggerProps -> TriggerProps

-- | Default trigger properties
defaultTriggerProps :: TriggerProps
defaultTriggerProps =
  { className: ""
  }

-- | Content properties
type ContentProps =
  { className :: String
  }

-- | Content property modifier
type ContentProp = ContentProps -> ContentProps

-- | Default content properties
defaultContentProps :: ContentProps
defaultContentProps =
  { className: ""
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set open state
isOpen :: forall i. Boolean -> CollapsibleProp i
isOpen o props = props { isOpen = o }

-- | Set toggle handler
onToggle :: forall i. (Boolean -> i) -> CollapsibleProp i
onToggle handler props = props { onToggle = Just handler }

-- | Set disabled state
disabled :: forall i. Boolean -> CollapsibleProp i
disabled d props = props { disabled = d }

-- | Show expand/collapse icon
showIcon :: forall i. Boolean -> CollapsibleProp i
showIcon s props = props { showIcon = s }

-- | Set icon position
iconPosition :: forall i. IconPosition -> CollapsibleProp i
iconPosition p props = props { iconPosition = p }

-- | Enable lazy rendering of content
lazyRender :: forall i. Boolean -> CollapsibleProp i
lazyRender l props = props { lazyRender = l }

-- | Set animation duration (ms)
animationDuration :: forall i. Int -> CollapsibleProp i
animationDuration d props = props { animationDuration = d }

-- | Add custom class to container
className :: forall i. String -> CollapsibleProp i
className c props = props { className = props.className <> " " <> c }

-- | Add custom class to trigger
triggerClassName :: String -> TriggerProp
triggerClassName c props = props { className = props.className <> " " <> c }

-- | Add custom class to content
contentClassName :: String -> ContentProp
contentClassName c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Collapsible container
-- |
-- | Wraps trigger and content with expand/collapse behavior
collapsible :: forall w i. 
  Array (CollapsibleProp i) -> 
  HH.HTML w i -> 
  HH.HTML w i -> 
  HH.HTML w i
collapsible propMods triggerEl contentEl =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    containerClasses = "collapsible"
    
    openClass = if props.isOpen then "collapsible-open" else "collapsible-closed"
    
    disabledClass = if props.disabled then "collapsible-disabled opacity-50" else ""
  in
    HH.div
      [ cls [ containerClasses, openClass, disabledClass, props.className ]
      , HP.attr (HH.AttrName "data-state") (if props.isOpen then "open" else "closed")
      , HP.attr (HH.AttrName "data-disabled") (if props.disabled then "true" else "false")
      ]
      [ triggerEl
      , contentEl
      ]

-- | Trigger element
-- |
-- | Clickable element that toggles the collapsible
trigger :: forall w i. Array TriggerProp -> Array (HH.HTML w i) -> HH.HTML w i
trigger propMods children =
  let
    props = foldl (\p f -> f p) defaultTriggerProps propMods
    
    triggerClasses =
      "collapsible-trigger flex items-center justify-between w-full py-2 px-3 text-left font-medium transition-colors hover:bg-accent rounded-md cursor-pointer focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring"
  in
    HH.button
      [ cls [ triggerClasses, props.className ]
      , HP.type_ HP.ButtonButton
      , ARIA.expanded "false"  -- Will be updated via JS or parent
      ]
      children

-- | Trigger with icon
-- |
-- | Trigger element with chevron icon that rotates
triggerWithIcon :: forall w i. Array TriggerProp -> String -> HH.HTML w i
triggerWithIcon propMods label =
  let
    props = foldl (\p f -> f p) defaultTriggerProps propMods
    
    triggerClasses =
      "collapsible-trigger flex items-center justify-between w-full py-2 px-3 text-left font-medium transition-colors hover:bg-accent rounded-md cursor-pointer focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring"
  in
    HH.button
      [ cls [ triggerClasses, props.className ]
      , HP.type_ HP.ButtonButton
      , ARIA.expanded "false"
      ]
      [ HH.span [] [ HH.text label ]
      , chevronIcon
      ]

-- | Content element
-- |
-- | Collapsible content that expands/collapses
content :: forall w i. Array ContentProp -> Array (HH.HTML w i) -> HH.HTML w i
content propMods children =
  let
    props = foldl (\p f -> f p) defaultContentProps propMods
    
    contentClasses =
      "collapsible-content overflow-hidden transition-all data-[state=closed]:h-0 data-[state=closed]:opacity-0 data-[state=open]:opacity-100"
  in
    HH.div
      [ cls [ contentClasses, props.className ]
      , HP.attr (HH.AttrName "data-state") "closed"
      , ARIA.hidden "true"
      ]
      [ HH.div
          [ cls [ "collapsible-content-inner py-2 px-3" ] ]
          children
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // icons
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Chevron icon (rotates on expand)
chevronIcon :: forall w i. HH.HTML w i
chevronIcon =
  HH.element (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "width") "16"
    , HP.attr (HH.AttrName "height") "16"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , HP.attr (HH.AttrName "stroke-linejoin") "round"
    , cls [ "collapsible-chevron transition-transform duration-200 data-[state=open]:rotate-180" ]
    ]
    [ HH.element (HH.ElemName "polyline")
        [ HP.attr (HH.AttrName "points") "6 9 12 15 18 9" ]
        []
    ]
