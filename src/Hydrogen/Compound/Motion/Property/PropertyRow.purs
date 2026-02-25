-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                    // hydrogen // component // motion // property // propertyrow
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Property Row Component
-- |
-- | A single row in the property panel, containing a label, value control,
-- | and keyframe toggle. This is the fundamental building block for property
-- | inspection in motion graphics editors.
-- |
-- | ## Layout
-- |
-- | ```
-- | ┌─────────────────────────────────────────────────────────┐
-- | │ ◇ Position X │ ████  250.0  ████ │ [expression icon] │
-- | └─────────────────────────────────────────────────────────┘
-- |   │              │                   │
-- |   │              │                   └── Expression indicator (optional)
-- |   │              └── Value input (slot for child component)
-- |   └── Keyframe stopwatch + label
-- | ```
-- |
-- | ## Features
-- |
-- | - Label with keyframe stopwatch toggle
-- | - Slot for value input component (ScrubableNumber, AngleDial, etc.)
-- | - Expression indicator when property has expression
-- | - Animated/non-animated visual distinction
-- | - Hover states for row selection
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Motion.Property.PropertyRow as PropertyRow
-- |
-- | HH.slot _position unit PropertyRow.component
-- |   { label: "Position X"
-- |   , isAnimated: true
-- |   , hasExpression: false
-- |   , isSelected: false
-- |   }
-- |   HandlePropertyRowOutput
-- | ```
module Hydrogen.Component.Motion.Property.PropertyRow
  ( -- * Component
    component
  
  -- * Types
  , Query(SetAnimated, SetExpression, SetSelected, SetDisabled)
  , Input
  , Output(ToggleAnimation, RowSelected, RowDoubleClicked, ExpressionClicked)
  , Slot
  , ChildSlots
  
  -- * Slot Type
  , _propertyRow
  , _valueInput
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
  , isAnimated :: Boolean
  , hasExpression :: Boolean
  , isSelected :: Boolean
  , disabled :: Boolean
  }

-- | Component queries
data Query a
  = SetAnimated Boolean a
  | SetExpression Boolean a
  | SetSelected Boolean a
  | SetDisabled Boolean a

-- | Component output
data Output
  = ToggleAnimation          -- Clicked the keyframe stopwatch
  | RowSelected              -- Clicked to select the row
  | RowDoubleClicked         -- Double-clicked (open keyframe editor)
  | ExpressionClicked        -- Clicked the expression indicator

-- | Internal state
type State =
  { label :: String
  , isAnimated :: Boolean
  , hasExpression :: Boolean
  , isSelected :: Boolean
  , disabled :: Boolean
  , isHovered :: Boolean
  }

-- | Internal actions
data Action
  = Initialize
  | Receive Input
  | HandleStopwatchClick MouseEvent
  | HandleRowClick MouseEvent
  | HandleRowDoubleClick MouseEvent
  | HandleExpressionClick MouseEvent
  | HandleMouseEnter
  | HandleMouseLeave

-- | Child slots for value input component
type ChildSlots = ( valueInput :: forall query output. H.Slot query output Unit )

-- | Slot type helper
type Slot = H.Slot Query Output Unit

-- | Slot proxies
_propertyRow :: Proxy "propertyRow"
_propertyRow = Proxy

_valueInput :: Proxy "valueInput"
_valueInput = Proxy

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // component
-- ═══════════════════════════════════════════════════════════════════════════════

-- | PropertyRow component
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
  , isAnimated: input.isAnimated
  , hasExpression: input.hasExpression
  , isSelected: input.isSelected
  , disabled: input.disabled
  , isHovered: false
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // render
-- ═══════════════════════════════════════════════════════════════════════════════

render :: forall m. MonadAff m => State -> H.ComponentHTML Action ChildSlots m
render state =
  HH.div
    [ cls [ rowClasses state ]
    , HE.onClick HandleRowClick
    , HE.onDoubleClick HandleRowDoubleClick
    , HE.onMouseEnter (const HandleMouseEnter)
    , HE.onMouseLeave (const HandleMouseLeave)
    , ARIA.role "row"
    , ARIA.selected (show state.isSelected)
    ]
    [ -- Keyframe stopwatch and label
      renderLabelSection state
    
    -- Value input slot (filled by parent)
    , renderValueSlot
    
    -- Expression indicator (if applicable)
    , renderExpressionIndicator state
    ]

-- | Render the label section with stopwatch
renderLabelSection :: forall m. State -> H.ComponentHTML Action ChildSlots m
renderLabelSection state =
  HH.div
    [ cls [ "flex items-center gap-1.5 min-w-[120px] flex-shrink-0" ] ]
    [ -- Keyframe stopwatch
      HH.button
        [ cls [ stopwatchClasses state ]
        , HE.onClick HandleStopwatchClick
        , HP.disabled state.disabled
        , ARIA.label (if state.isAnimated then "Remove animation" else "Add keyframe")
        , HP.title (if state.isAnimated then "Click to remove animation" else "Click to add keyframe")
        ]
        [ HH.text (if state.isAnimated then "◆" else "◇") ]
    
    -- Label text
    , HH.span
        [ cls [ labelClasses state ] ]
        [ HH.text state.label ]
    ]

-- | Render the value input slot
renderValueSlot :: forall m. MonadAff m => H.ComponentHTML Action ChildSlots m
renderValueSlot =
  HH.div
    [ cls [ "flex-1 flex items-center justify-end" ] ]
    [ -- This slot is filled by the parent component with the appropriate
      -- value input (ScrubableNumber, AngleDial, PositionXY, etc.)
      HH.slot_ _valueInput unit emptySlot unit
    ]

-- | Empty slot placeholder (parent fills this)
emptySlot :: forall m query output. MonadAff m => H.Component query Unit output m
emptySlot = H.mkComponent
  { initialState: const unit
  , render: const (HH.text "")
  , eval: H.mkEval H.defaultEval
  }

-- | Render expression indicator
renderExpressionIndicator :: forall m. State -> H.ComponentHTML Action ChildSlots m
renderExpressionIndicator state =
  if state.hasExpression
    then
      HH.button
        [ cls [ expressionClasses ]
        , HE.onClick HandleExpressionClick
        , HP.disabled state.disabled
        , ARIA.label "Edit expression"
        , HP.title "This property has an expression"
        ]
        [ HH.text "ƒ" ]
    else
      HH.text ""

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // styles
-- ═══════════════════════════════════════════════════════════════════════════════

rowClasses :: State -> String
rowClasses state =
  "flex items-center gap-2 px-2 py-1 rounded text-sm " <>
  "transition-colors duration-75 " <>
  if state.disabled
    then "opacity-50 cursor-not-allowed"
    else if state.isSelected
      then "bg-accent"
      else if state.isHovered
        then "bg-accent/50"
        else "hover:bg-accent/30"

stopwatchClasses :: State -> String
stopwatchClasses state =
  "w-4 h-4 flex items-center justify-center text-xs " <>
  "rounded transition-colors duration-75 " <>
  if state.disabled
    then "text-muted-foreground cursor-not-allowed"
    else if state.isAnimated
      then "text-primary hover:text-primary/80"
      else "text-muted-foreground hover:text-foreground"

labelClasses :: State -> String
labelClasses state =
  "truncate " <>
  if state.isAnimated
    then "text-foreground font-medium"
    else "text-muted-foreground"

expressionClasses :: String
expressionClasses =
  "w-5 h-5 flex items-center justify-center text-xs " <>
  "rounded bg-amber-500/20 text-amber-500 " <>
  "hover:bg-amber-500/30 transition-colors duration-75"

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
      , isAnimated = input.isAnimated
      , hasExpression = input.hasExpression
      , isSelected = input.isSelected
      , disabled = input.disabled
      }
  
  HandleStopwatchClick _ -> do
    state <- H.get
    unless state.disabled do
      -- Toggle animation state locally for immediate feedback
      H.modify_ _ { isAnimated = not state.isAnimated }
      H.raise ToggleAnimation
  
  HandleRowClick _ -> do
    state <- H.get
    unless state.disabled do
      H.raise RowSelected
  
  HandleRowDoubleClick _ -> do
    state <- H.get
    unless state.disabled do
      H.raise RowDoubleClicked
  
  HandleExpressionClick _ -> do
    state <- H.get
    unless state.disabled do
      H.raise ExpressionClicked
  
  HandleMouseEnter -> do
    H.modify_ _ { isHovered = true }
  
  HandleMouseLeave -> do
    H.modify_ _ { isHovered = false }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // handle query
-- ═══════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action ChildSlots Output m (Maybe a)
handleQuery = case _ of
  SetAnimated animated reply -> do
    H.modify_ _ { isAnimated = animated }
    pure (Just reply)
  
  SetExpression hasExpr reply -> do
    H.modify_ _ { hasExpression = hasExpr }
    pure (Just reply)
  
  SetSelected selected reply -> do
    H.modify_ _ { isSelected = selected }
    pure (Just reply)
  
  SetDisabled disabled reply -> do
    H.modify_ _ { disabled = disabled }
    pure (Just reply)
