-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // element // checkbox // state
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | CheckboxState — State atoms for checkbox controls.
-- |
-- | ## Checkbox vs Toggle
-- |
-- | Checkboxes and toggles are both binary controls, but differ semantically:
-- | - **Toggle/Switch**: Settings, immediate effect, "turn on/off"
-- | - **Checkbox**: Forms, submit effect, "select/include", can be grouped
-- |
-- | ## Verified Atoms (re-exported from Schema pillars)
-- |
-- | - CheckedFlag (Reactive.Flags) — Boolean wrapper for checked state
-- | - IndeterminateFlag (Reactive.Flags) — For partial selection ("Select All")
-- | - DisabledFlag, FocusedFlag, HoveredFlag (Reactive.Flags) — UI state
-- | - Progress (Temporal.Progress) — Animation progress [0.0-1.0]
-- |
-- | ## Domain Examples
-- |
-- | - **DAW**: Track mute/solo checkboxes, effect bypass
-- | - **Hospital**: Alert acknowledgment, medication confirmation
-- | - **Game**: Graphics settings, keybind toggles
-- | - **Mograph**: Layer visibility, effect enabled
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Reactive.Flags (verified boolean atoms)
-- | - Hydrogen.Schema.Temporal.Progress (bounded animation progress)

module Hydrogen.Schema.Element.Checkbox.State
  ( -- * Checkbox Element State Record
    CheckboxElementState
  , defaultState
  , checkedState
  , uncheckedState
  , indeterminateState
  , disabledState
  
  -- * State Accessors
  , isChecked
  , isIndeterminate
  , isDisabled
  , isFocused
  , isHovered
  , isPressed
  , isAnimating
  , getTransitionProgress
  , isRequired
  , getName
  , getValue
  
  -- * State Modifiers
  , setChecked
  , setIndeterminate
  , setDisabled
  , setFocused
  , setHovered
  , setPressed
  , setAnimating
  , setTransitionProgress
  , setRequired
  , setName
  , setValue
  , toggle
  
  -- * Re-exports from Reactive.Flags
  , module Hydrogen.Schema.Reactive.Flags
  
  -- * Re-exports from Temporal.Progress
  , module Hydrogen.Schema.Temporal.Progress
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , not
  )

import Prim (Boolean, Number, String)

import Hydrogen.Schema.Reactive.Flags
  ( CheckedFlag(CheckedFlag)
  , IndeterminateFlag(IndeterminateFlag)
  , DisabledFlag(DisabledFlag)
  , FocusedFlag(FocusedFlag)
  , HoveredFlag(HoveredFlag)
  , PressedFlag(PressedFlag)
  , AnimatingFlag(AnimatingFlag)
  , RequiredFlag(RequiredFlag)
  )

import Hydrogen.Schema.Temporal.Progress
  ( Progress
  , progress
  , unwrapProgress
  , start
  , end
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // checkbox element state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete checkbox element state — all values needed to render a checkbox.
-- |
-- | ## Verified Bounded Types
-- |
-- | Every field uses a verified Schema atom:
-- | - checked: CheckedFlag (newtype Boolean)
-- | - indeterminate: IndeterminateFlag (newtype Boolean)
-- | - disabled/focused/hovered/pressed: Verified flags
-- | - transitionProgress: Progress (bounded 0.0-1.0)
-- |
-- | ## State Machine
-- |
-- | A checkbox transitions between:
-- | - Unchecked (checked = false) — empty box
-- | - Checked (checked = true) — checkmark visible
-- | - Indeterminate (mixed state) — dash or partial indicator
-- |
-- | ## Form Integration
-- |
-- | Unlike toggles (immediate effect), checkboxes are form controls:
-- | - `name`: Form field name for submission
-- | - `value`: Value submitted when checked (defaults to "on")
-- | - `required`: Validation constraint
type CheckboxElementState =
  { -- Core state (verified flags)
    checked :: CheckedFlag              -- ^ Is checkbox checked
  , indeterminate :: IndeterminateFlag  -- ^ Is in partial/mixed state
    -- UI state (verified flags)
  , disabled :: DisabledFlag            -- ^ Cannot interact
  , focused :: FocusedFlag              -- ^ Has keyboard focus
  , hovered :: HoveredFlag              -- ^ Pointer is over checkbox
  , pressed :: PressedFlag              -- ^ Currently being pressed
    -- Animation state
  , animating :: AnimatingFlag          -- ^ Check animation in progress
  , transitionProgress :: Progress      -- ^ Animation progress [0.0-1.0]
    -- Form integration
  , name :: Maybe String                -- ^ Form field name
  , value :: String                     -- ^ Value when checked (default "on")
  , required :: RequiredFlag            -- ^ Must be checked for form validity
  }

-- | Default checkbox state — unchecked, enabled, not animating.
defaultState :: CheckboxElementState
defaultState =
  { checked: CheckedFlag false
  , indeterminate: IndeterminateFlag false
  , disabled: DisabledFlag false
  , focused: FocusedFlag false
  , hovered: HoveredFlag false
  , pressed: PressedFlag false
  , animating: AnimatingFlag false
  , transitionProgress: start
  , name: Nothing
  , value: "on"
  , required: RequiredFlag false
  }

-- | Create a checked state.
checkedState :: CheckboxElementState
checkedState = defaultState 
  { checked = CheckedFlag true
  , transitionProgress = end  -- Animation complete
  }

-- | Create an unchecked state.
uncheckedState :: CheckboxElementState
uncheckedState = defaultState

-- | Create an indeterminate state (mixed/partial).
-- |
-- | Used for parent checkboxes when some children are selected.
-- | Example: "Select All" checkbox with 3 of 5 items checked.
indeterminateState :: CheckboxElementState
indeterminateState = defaultState { indeterminate = IndeterminateFlag true }

-- | Create a disabled state.
disabledState :: CheckboxElementState
disabledState = defaultState { disabled = DisabledFlag true }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is the checkbox checked?
isChecked :: CheckboxElementState -> Boolean
isChecked s = case s.checked of
  CheckedFlag b -> b

-- | Is the checkbox in indeterminate (mixed) state?
isIndeterminate :: CheckboxElementState -> Boolean
isIndeterminate s = case s.indeterminate of
  IndeterminateFlag b -> b

-- | Is the checkbox disabled?
isDisabled :: CheckboxElementState -> Boolean
isDisabled s = case s.disabled of
  DisabledFlag b -> b

-- | Does the checkbox have keyboard focus?
isFocused :: CheckboxElementState -> Boolean
isFocused s = case s.focused of
  FocusedFlag b -> b

-- | Is the pointer hovering over the checkbox?
isHovered :: CheckboxElementState -> Boolean
isHovered s = case s.hovered of
  HoveredFlag b -> b

-- | Is the checkbox being pressed?
isPressed :: CheckboxElementState -> Boolean
isPressed s = case s.pressed of
  PressedFlag b -> b

-- | Is a check animation in progress?
isAnimating :: CheckboxElementState -> Boolean
isAnimating s = case s.animating of
  AnimatingFlag b -> b

-- | Get animation progress (0.0-1.0, bounded).
getTransitionProgress :: CheckboxElementState -> Progress
getTransitionProgress s = s.transitionProgress

-- | Is the checkbox required for form validity?
isRequired :: CheckboxElementState -> Boolean
isRequired s = case s.required of
  RequiredFlag b -> b

-- | Get the form field name.
getName :: CheckboxElementState -> Maybe String
getName s = s.name

-- | Get the value submitted when checked.
getValue :: CheckboxElementState -> String
getValue s = s.value

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set checked state.
-- |
-- | Clears indeterminate when setting a definite value.
setChecked :: Boolean -> CheckboxElementState -> CheckboxElementState
setChecked b s = s 
  { checked = CheckedFlag b
  , indeterminate = IndeterminateFlag false
  }

-- | Set indeterminate state.
-- |
-- | Note: Indeterminate is a visual state, not a value state.
-- | The underlying checked value remains unchanged.
setIndeterminate :: Boolean -> CheckboxElementState -> CheckboxElementState
setIndeterminate b s = s { indeterminate = IndeterminateFlag b }

-- | Set disabled state.
setDisabled :: Boolean -> CheckboxElementState -> CheckboxElementState
setDisabled b s = s { disabled = DisabledFlag b }

-- | Set focused state.
setFocused :: Boolean -> CheckboxElementState -> CheckboxElementState
setFocused b s = s { focused = FocusedFlag b }

-- | Set hovered state.
setHovered :: Boolean -> CheckboxElementState -> CheckboxElementState
setHovered b s = s { hovered = HoveredFlag b }

-- | Set pressed state.
setPressed :: Boolean -> CheckboxElementState -> CheckboxElementState
setPressed b s = s { pressed = PressedFlag b }

-- | Set animating state.
setAnimating :: Boolean -> CheckboxElementState -> CheckboxElementState
setAnimating b s = s { animating = AnimatingFlag b }

-- | Set transition progress (automatically bounded to 0.0-1.0).
setTransitionProgress :: Number -> CheckboxElementState -> CheckboxElementState
setTransitionProgress p s = s { transitionProgress = progress p }

-- | Set required flag.
setRequired :: Boolean -> CheckboxElementState -> CheckboxElementState
setRequired b s = s { required = RequiredFlag b }

-- | Set form field name.
setName :: String -> CheckboxElementState -> CheckboxElementState
setName n s = s { name = Just n }

-- | Set value submitted when checked.
setValue :: String -> CheckboxElementState -> CheckboxElementState
setValue v s = s { value = v }

-- | Toggle the checked state (flip on/off).
-- |
-- | Also clears indeterminate state.
toggle :: CheckboxElementState -> CheckboxElementState
toggle s = s
  { checked = CheckedFlag (not (isChecked s))
  , indeterminate = IndeterminateFlag false
  }
