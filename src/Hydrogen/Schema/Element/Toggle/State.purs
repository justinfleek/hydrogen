-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // schema // element // toggle // state
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ToggleState — State atoms for toggle/switch controls.
-- |
-- | ## Verified Atoms (re-exported from Schema pillars)
-- |
-- | - CheckedFlag (Reactive.Flags) — Boolean wrapper for checked state
-- | - IndeterminateFlag (Reactive.Flags) — For partial selection
-- | - DisabledFlag (Reactive.Flags) — UI disabled state
-- | - LoadingFlag (Reactive.Flags) — Loading indicator
-- | - AnimatingFlag (Reactive.Flags) — Transition in progress
-- | - ToggleState (Reactive.ButtonSemantics) — ARIA pressed state
-- | - Progress (Temporal.Progress) — Animation progress [0.0-1.0]
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Reactive.Flags (verified boolean atoms)
-- | - Hydrogen.Schema.Reactive.ButtonSemantics (ARIA toggle state)
-- | - Hydrogen.Schema.Temporal.Progress (bounded animation progress)
-- |
-- | ## Design Philosophy
-- |
-- | State atoms describe WHAT the toggle shows, not HOW it looks.
-- | All values use verified bounded types — no raw Booleans or Numbers.

module Hydrogen.Schema.Element.Toggle.State
  ( -- * Toggle Element State Record
    ToggleElementState
  , defaultState
  , checkedState
  , uncheckedState
  , indeterminateState
  , loadingState
  
  -- * State Accessors
  , isChecked
  , isIndeterminate
  , isDisabled
  , isLoading
  , isAnimating
  , getTransitionProgress
  , getAriaToggleState
  
  -- * State Modifiers
  , setChecked
  , setIndeterminate
  , setDisabled
  , setLoading
  , setAnimating
  , setTransitionProgress
  , toggle
  
  -- * Re-exports from Reactive.Flags
  , module Hydrogen.Schema.Reactive.Flags
  
  -- * Re-exports from Reactive.ButtonSemantics
  , module ToggleStateReexport
  
  -- * Re-exports from Temporal.Progress
  , module Hydrogen.Schema.Temporal.Progress
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , not
  , (<>)
  )

import Hydrogen.Schema.Reactive.Flags
  ( CheckedFlag(CheckedFlag)
  , IndeterminateFlag(IndeterminateFlag)
  , DisabledFlag(DisabledFlag)
  , LoadingFlag(LoadingFlag)
  , AnimatingFlag(AnimatingFlag)
  )

import Hydrogen.Schema.Reactive.ButtonSemantics
  ( ToggleState(Pressed, Unpressed, Mixed)
  , toggleStateToAria
  , isPressed
  ) as ToggleStateReexport

import Hydrogen.Schema.Temporal.Progress
  ( Progress
  , progress
  , unwrapProgress
  , start
  , end
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // toggle element state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete toggle element state — all values needed to render a toggle.
-- |
-- | ## Verified Bounded Types
-- |
-- | Every field uses a verified Schema atom:
-- | - checked: CheckedFlag (newtype Boolean)
-- | - indeterminate: IndeterminateFlag (newtype Boolean)
-- | - disabled: DisabledFlag (newtype Boolean)
-- | - loading: LoadingFlag (newtype Boolean)
-- | - animating: AnimatingFlag (newtype Boolean)
-- | - transitionProgress: Progress (bounded 0.0-1.0)
-- |
-- | ## State Machine
-- |
-- | A toggle transitions between:
-- | - Unchecked (checked = false)
-- | - Checked (checked = true)
-- | - Indeterminate (partial selection, e.g. "Select All" with some selected)
-- |
-- | During transitions, `animating` is true and `transitionProgress`
-- | tracks animation completion (0.0 = start, 1.0 = complete).
type ToggleElementState =
  { -- Core state (verified flags)
    checked :: CheckedFlag              -- ^ Is toggle on/checked
  , indeterminate :: IndeterminateFlag  -- ^ Is in partial/mixed state
    -- UI state (verified flags)
  , disabled :: DisabledFlag            -- ^ Cannot interact
  , loading :: LoadingFlag              -- ^ Shows loading indicator
    -- Animation state
  , animating :: AnimatingFlag          -- ^ Transition in progress
  , transitionProgress :: Progress      -- ^ Animation progress [0.0-1.0]
  }

-- | Default toggle state — unchecked, enabled, not animating.
defaultState :: ToggleElementState
defaultState =
  { checked: CheckedFlag false
  , indeterminate: IndeterminateFlag false
  , disabled: DisabledFlag false
  , loading: LoadingFlag false
  , animating: AnimatingFlag false
  , transitionProgress: start
  }

-- | Create a checked (on) state.
checkedState :: ToggleElementState
checkedState = defaultState { checked = CheckedFlag true }

-- | Create an unchecked (off) state.
uncheckedState :: ToggleElementState
uncheckedState = defaultState

-- | Create an indeterminate state (mixed/partial).
-- |
-- | Used for "Select All" toggles when some items are selected.
indeterminateState :: ToggleElementState
indeterminateState = defaultState { indeterminate = IndeterminateFlag true }

-- | Create a loading state.
loadingState :: ToggleElementState
loadingState = defaultState { loading = LoadingFlag true }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is the toggle checked (on)?
isChecked :: ToggleElementState -> Boolean
isChecked s = case s.checked of
  CheckedFlag b -> b

-- | Is the toggle in indeterminate (mixed) state?
isIndeterminate :: ToggleElementState -> Boolean
isIndeterminate s = case s.indeterminate of
  IndeterminateFlag b -> b

-- | Is the toggle disabled?
isDisabled :: ToggleElementState -> Boolean
isDisabled s = case s.disabled of
  DisabledFlag b -> b

-- | Is the toggle in loading state?
isLoading :: ToggleElementState -> Boolean
isLoading s = case s.loading of
  LoadingFlag b -> b

-- | Is a transition animation in progress?
isAnimating :: ToggleElementState -> Boolean
isAnimating s = case s.animating of
  AnimatingFlag b -> b

-- | Get animation progress (0.0-1.0, bounded).
getTransitionProgress :: ToggleElementState -> Progress
getTransitionProgress s = s.transitionProgress

-- | Get ARIA toggle state for accessibility.
-- |
-- | Maps state to ToggleState from ButtonSemantics:
-- | - Indeterminate → Mixed (aria-pressed="mixed")
-- | - Checked → Pressed (aria-pressed="true")
-- | - Unchecked → Unpressed (aria-pressed="false")
getAriaToggleState :: ToggleElementState -> ToggleStateReexport.ToggleState
getAriaToggleState s
  | isIndeterminate s = ToggleStateReexport.Mixed
  | isChecked s = ToggleStateReexport.Pressed
  | true = ToggleStateReexport.Unpressed

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set checked state.
setChecked :: Boolean -> ToggleElementState -> ToggleElementState
setChecked b s = s 
  { checked = CheckedFlag b
  , indeterminate = IndeterminateFlag false  -- Clear indeterminate when setting checked
  }

-- | Set indeterminate state.
-- |
-- | Note: Setting indeterminate does not change the checked value.
-- | Indeterminate is a display state, not a value state.
setIndeterminate :: Boolean -> ToggleElementState -> ToggleElementState
setIndeterminate b s = s { indeterminate = IndeterminateFlag b }

-- | Set disabled state.
setDisabled :: Boolean -> ToggleElementState -> ToggleElementState
setDisabled b s = s { disabled = DisabledFlag b }

-- | Set loading state.
setLoading :: Boolean -> ToggleElementState -> ToggleElementState
setLoading b s = s { loading = LoadingFlag b }

-- | Set animating state.
setAnimating :: Boolean -> ToggleElementState -> ToggleElementState
setAnimating b s = s { animating = AnimatingFlag b }

-- | Set transition progress (automatically bounded to 0.0-1.0).
setTransitionProgress :: Number -> ToggleElementState -> ToggleElementState
setTransitionProgress p s = s { transitionProgress = progress p }

-- | Toggle the checked state (flip on/off).
-- |
-- | Also clears indeterminate state.
toggle :: ToggleElementState -> ToggleElementState
toggle s = s
  { checked = CheckedFlag (not (isChecked s))
  , indeterminate = IndeterminateFlag false
  }
