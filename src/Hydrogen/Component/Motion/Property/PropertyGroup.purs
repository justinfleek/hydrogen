-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                   // hydrogen // component // motion // property // propertygroup
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Collapsible Property Group Component
-- |
-- | Groups related properties under a collapsible header. Used for organizing
-- | transform properties, effects, masks, and other property categories in
-- | motion graphics editors.
-- |
-- | ## Layout
-- |
-- | ```
-- | ┌─────────────────────────────────────┐
-- | │ ▼ Transform                     [◆] │  ← Header with expand/collapse
-- | ├─────────────────────────────────────┤
-- | │   Position X  .......... 250.0     │  ← Child properties
-- | │   Position Y  .......... 150.0     │
-- | │   Scale       .......... 100%      │
-- | │   Rotation    .......... 0°        │
-- | └─────────────────────────────────────┘
-- | ```
-- |
-- | ## Features
-- |
-- | - Click header to expand/collapse
-- | - Animated expand/collapse transition
-- | - Group-level keyframe indicator
-- | - Nesting support for sub-groups
-- | - Visual depth indication
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Motion.Property.PropertyGroup as PropertyGroup
-- |
-- | HH.slot _transform unit PropertyGroup.component
-- |   { label: "Transform"
-- |   , isExpanded: true
-- |   , hasAnimatedChildren: true
-- |   , depth: 0
-- |   }
-- |   HandleGroupOutput
-- | ```
module Hydrogen.Component.Motion.Property.PropertyGroup
  ( -- * Component
    component
  
  -- * Types
  , Query(SetExpanded, ToggleExpanded, SetHasAnimatedChildren)
  , Input
  , Output(Expanded, Collapsed, HeaderClicked)
  , Slot
  , ChildSlots
  
  -- * Slot Type
  , _propertyGroup
  , _children
  ) where

import Prelude

import Data.Maybe (Maybe(Just))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)
import Type.Proxy (Proxy(Proxy))
import Web.UIEvent.MouseEvent (MouseEvent)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Component input
type Input =
  { label :: String
  , isExpanded :: Boolean
  , hasAnimatedChildren :: Boolean
  , depth :: Int               -- Nesting depth (0 = top level)
  , disabled :: Boolean
  }

-- | Component queries
data Query a
  = SetExpanded Boolean a
  | ToggleExpanded a
  | SetHasAnimatedChildren Boolean a

-- | Component output
data Output
  = Expanded                   -- Group was expanded
  | Collapsed                  -- Group was collapsed
  | HeaderClicked              -- Header area clicked (for selection)

-- | Internal state
type State =
  { label :: String
  , isExpanded :: Boolean
  , hasAnimatedChildren :: Boolean
  , depth :: Int
  , disabled :: Boolean
  , isHovered :: Boolean
  }

-- | Internal actions
data Action
  = Initialize
  | Receive Input
  | HandleHeaderClick MouseEvent
  | HandleExpandClick MouseEvent
  | HandleMouseEnter
  | HandleMouseLeave

-- | Child slots for nested content
type ChildSlots = ( children :: forall query output. H.Slot query output Unit )

-- | Slot type helper
type Slot = H.Slot Query Output Unit

-- | Slot proxies
_propertyGroup :: Proxy "propertyGroup"
_propertyGroup = Proxy

_children :: Proxy "children"
_children = Proxy

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // component
-- ═══════════════════════════════════════════════════════════════════════════════

-- | PropertyGroup component
component :: forall m. MonadAff m => H.Component Query Input Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval H.defaultEval
      { handleAction = handleAction
      , handleQuery = handleQuery
      , receive = Just <<< Receive
      , initialize = Just Initialize
      }
  }

-- | Initial state from input
initialState :: Input -> State
initialState input =
  { label: input.label
  , isExpanded: input.isExpanded
  , hasAnimatedChildren: input.hasAnimatedChildren
  , depth: input.depth
  , disabled: input.disabled
  , isHovered: false
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // render
-- ═══════════════════════════════════════════════════════════════════════════════

render :: forall m. MonadAff m => State -> H.ComponentHTML Action ChildSlots m
render state =
  HH.div
    [ cls [ containerClasses state ]
    , ARIA.role "group"
    , ARIA.expanded (show state.isExpanded)
    ]
    [ -- Header section
      renderHeader state
    
    -- Collapsible content
    , renderContent state
    ]

-- | Render the group header
renderHeader :: forall m. State -> H.ComponentHTML Action ChildSlots m
renderHeader state =
  HH.div
    [ cls [ headerClasses state ]
    , HE.onClick HandleHeaderClick
    , HE.onMouseEnter (const HandleMouseEnter)
    , HE.onMouseLeave (const HandleMouseLeave)
    , ARIA.role "button"
    , HP.tabIndex 0
    ]
    [ -- Expand/collapse arrow
      HH.button
        [ cls [ arrowClasses state ]
        , HE.onClick HandleExpandClick
        , HP.disabled state.disabled
        , ARIA.label (if state.isExpanded then "Collapse" else "Expand")
        ]
        [ HH.text (if state.isExpanded then "▼" else "▶") ]
    
    -- Group label
    , HH.span
        [ cls [ labelClasses state ] ]
        [ HH.text state.label ]
    
    -- Animated indicator (if any children are animated)
    , if state.hasAnimatedChildren
        then HH.span
          [ cls [ "ml-auto text-primary text-xs" ] ]
          [ HH.text "◆" ]
        else HH.text ""
    ]

-- | Render the collapsible content area
renderContent :: forall m. MonadAff m => State -> H.ComponentHTML Action ChildSlots m
renderContent state =
  if state.isExpanded
    then
      HH.div
        [ cls [ contentClasses state ]
        , ARIA.hidden "false"
        ]
        [ -- Children slot (filled by parent)
          HH.slot_ _children unit emptySlot unit
        ]
    else
      HH.div
        [ cls [ "hidden" ]
        , ARIA.hidden "true"
        ]
        []

-- | Empty slot placeholder
emptySlot :: forall m query output. MonadAff m => H.Component query Unit output m
emptySlot = H.mkComponent
  { initialState: const unit
  , render: const (HH.text "")
  , eval: H.mkEval H.defaultEval
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // styles
-- ═══════════════════════════════════════════════════════════════════════════════

containerClasses :: State -> String
containerClasses state =
  "rounded " <>
  depthIndent state.depth

headerClasses :: State -> String
headerClasses state =
  "flex items-center gap-1 px-1 py-0.5 rounded cursor-pointer " <>
  "select-none transition-colors duration-75 " <>
  if state.disabled
    then "opacity-50 cursor-not-allowed"
    else if state.isHovered
      then "bg-accent"
      else "hover:bg-accent/50"

arrowClasses :: State -> String
arrowClasses state =
  "w-4 h-4 flex items-center justify-center text-xs " <>
  "text-muted-foreground transition-transform duration-150 " <>
  if state.disabled
    then "cursor-not-allowed"
    else "hover:text-foreground"

labelClasses :: State -> String
labelClasses state =
  "text-sm font-medium " <>
  if state.hasAnimatedChildren
    then "text-foreground"
    else "text-muted-foreground"

contentClasses :: State -> String
contentClasses _ =
  "pl-4 mt-0.5 space-y-0.5 " <>
  "border-l border-border/50 ml-2"

-- | Indentation based on nesting depth
depthIndent :: Int -> String
depthIndent 0 = ""
depthIndent 1 = "pl-2"
depthIndent 2 = "pl-4"
depthIndent _ = "pl-6"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // handle action
-- ═══════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action ChildSlots Output m Unit
handleAction = case _ of
  Initialize -> do
    pure unit
  
  Receive input -> do
    H.modify_ \s -> s
      { label = input.label
      , isExpanded = input.isExpanded
      , hasAnimatedChildren = input.hasAnimatedChildren
      , depth = input.depth
      , disabled = input.disabled
      }
  
  HandleHeaderClick _ -> do
    state <- H.get
    unless state.disabled do
      H.raise HeaderClicked
  
  HandleExpandClick _ -> do
    state <- H.get
    unless state.disabled do
      let newExpanded = not state.isExpanded
      H.modify_ _ { isExpanded = newExpanded }
      if newExpanded
        then H.raise Expanded
        else H.raise Collapsed
  
  HandleMouseEnter -> do
    H.modify_ _ { isHovered = true }
  
  HandleMouseLeave -> do
    H.modify_ _ { isHovered = false }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // handle query
-- ═══════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action ChildSlots Output m (Maybe a)
handleQuery = case _ of
  SetExpanded expanded reply -> do
    state <- H.get
    H.modify_ _ { isExpanded = expanded }
    -- Emit event if state changed
    when (expanded /= state.isExpanded) do
      if expanded
        then H.raise Expanded
        else H.raise Collapsed
    pure (Just reply)
  
  ToggleExpanded reply -> do
    state <- H.get
    let newExpanded = not state.isExpanded
    H.modify_ _ { isExpanded = newExpanded }
    if newExpanded
      then H.raise Expanded
      else H.raise Collapsed
    pure (Just reply)
  
  SetHasAnimatedChildren hasAnimated reply -> do
    H.modify_ _ { hasAnimatedChildren = hasAnimated }
    pure (Just reply)
