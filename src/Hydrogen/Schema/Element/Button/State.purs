-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // schema // element // button // state
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ButtonState — Interaction state atoms for button controls.
-- |
-- | ## Design Philosophy
-- |
-- | Button state describes the CURRENT INTERACTION STATE, not the button's
-- | semantic purpose or appearance. A button doesn't have a persistent "value"
-- | like a toggle or slider — it triggers actions and returns to idle.
-- |
-- | However, buttons DO have interaction states that affect rendering:
-- | - Focused: Has keyboard focus (show focus ring)
-- | - Hovered: Pointer is over button (show hover effect)
-- | - Pressed: Being pressed/clicked (show pressed effect)
-- | - Loading: Action in progress (show spinner, disable)
-- | - Animating: Transition animation in progress
-- |
-- | ## Verified Atoms (re-exported from Schema pillars)
-- |
-- | All boolean states use verified wrappers from Reactive.Flags:
-- | - FocusedFlag — Has keyboard focus
-- | - HoveredFlag — Pointer is over element
-- | - PressedFlag — Being pressed (mousedown/touchstart)
-- | - LoadingFlag — Async operation in progress
-- | - AnimatingFlag — CSS/visual transition in progress
-- |
-- | ## State Machine
-- |
-- | A button transitions between interaction states:
-- | - Idle: No interaction (all flags false except possibly focused)
-- | - Hovered: Pointer over button (hovered = true)
-- | - Focused: Has keyboard focus (focused = true)
-- | - Pressed: Being pressed (pressed = true, during mousedown/touchstart)
-- | - Loading: Action triggered, waiting for completion (loading = true)
-- |
-- | Multiple states can be active simultaneously:
-- | - focused AND hovered (keyboard focus while pointer over)
-- | - focused AND pressed (keyboard activation via Enter/Space)
-- | - loading AND focused (loading while maintaining focus)
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Reactive.Flags (verified boolean atoms)
-- |
-- | ## Dependents
-- |
-- | - Hydrogen.Schema.Element.Button (compound type)
-- | - Rendering layers use these flags to determine visual state

module Hydrogen.Schema.Element.Button.State
  ( -- * Button Element State Record
    ButtonElementState
  , defaultState
  , idleState
  , focusedState
  , hoveredState
  , pressedState
  , loadingState
  
  -- * State Accessors
  , isFocused
  , isHovered
  , isPressed
  , isLoading
  , isAnimating
  , isInteractive
  
  -- * State Modifiers
  , setFocused
  , setHovered
  , setPressed
  , setLoading
  , setAnimating
  , resetInteraction
  
  -- * Re-exports from Reactive.Flags
  , module Hydrogen.Schema.Reactive.Flags
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , not
  , (&&)
  , (<>)
  )

import Hydrogen.Schema.Reactive.Flags
  ( FocusedFlag(FocusedFlag)
  , HoveredFlag(HoveredFlag)
  , PressedFlag(PressedFlag)
  , LoadingFlag(LoadingFlag)
  , AnimatingFlag(AnimatingFlag)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // button element state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete button element state — interaction flags for rendering.
-- |
-- | ## Verified Bounded Types
-- |
-- | Every field uses a verified Schema atom from Reactive.Flags:
-- | - focused: FocusedFlag — Has keyboard focus
-- | - hovered: HoveredFlag — Pointer is over button
-- | - pressed: PressedFlag — Being pressed (mousedown/touchstart)
-- | - loading: LoadingFlag — Async operation in progress
-- | - animating: AnimatingFlag — Visual transition in progress
-- |
-- | ## Usage
-- |
-- | These flags drive visual state in the Appearance layer:
-- | - focused → show focus ring
-- | - hovered → show hover fill/shadow
-- | - pressed → show pressed fill, scale down
-- | - loading → show spinner, disable interactions
-- | - animating → don't interrupt transitions
type ButtonElementState =
  { -- Interaction flags (verified wrappers)
    focused :: FocusedFlag       -- ^ Has keyboard focus
  , hovered :: HoveredFlag       -- ^ Pointer is over button
  , pressed :: PressedFlag       -- ^ Being pressed (mousedown/touchstart)
  , loading :: LoadingFlag       -- ^ Async operation in progress
  , animating :: AnimatingFlag   -- ^ Visual transition in progress
  }

-- | Default button state — idle, not interacting.
-- |
-- | All flags false. Button is ready for interaction.
defaultState :: ButtonElementState
defaultState =
  { focused: FocusedFlag false
  , hovered: HoveredFlag false
  , pressed: PressedFlag false
  , loading: LoadingFlag false
  , animating: AnimatingFlag false
  }

-- | Idle state — alias for defaultState.
-- |
-- | Explicitly named for clarity in state machine transitions.
idleState :: ButtonElementState
idleState = defaultState

-- | Focused state — button has keyboard focus.
-- |
-- | User can activate with Enter or Space.
focusedState :: ButtonElementState
focusedState = defaultState { focused = FocusedFlag true }

-- | Hovered state — pointer is over button.
-- |
-- | Shows hover visual feedback.
hoveredState :: ButtonElementState
hoveredState = defaultState { hovered = HoveredFlag true }

-- | Pressed state — button is being pressed.
-- |
-- | Active during mousedown/touchstart, before mouseup/touchend.
pressedState :: ButtonElementState
pressedState = defaultState { pressed = PressedFlag true }

-- | Loading state — async operation in progress.
-- |
-- | Shows spinner, disables further interaction until complete.
loadingState :: ButtonElementState
loadingState = defaultState { loading = LoadingFlag true }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Does the button have keyboard focus?
isFocused :: ButtonElementState -> Boolean
isFocused s = case s.focused of
  FocusedFlag b -> b

-- | Is the pointer hovering over the button?
isHovered :: ButtonElementState -> Boolean
isHovered s = case s.hovered of
  HoveredFlag b -> b

-- | Is the button being pressed?
isPressed :: ButtonElementState -> Boolean
isPressed s = case s.pressed of
  PressedFlag b -> b

-- | Is the button in loading state?
isLoading :: ButtonElementState -> Boolean
isLoading s = case s.loading of
  LoadingFlag b -> b

-- | Is a visual transition in progress?
isAnimating :: ButtonElementState -> Boolean
isAnimating s = case s.animating of
  AnimatingFlag b -> b

-- | Can the button receive interactions?
-- |
-- | False when loading (button is effectively disabled during async ops).
-- | Note: This does NOT check the `disabled` semantic flag from Semantics.purs.
-- | That's a separate concern — Semantics.disabled is the ARIA semantic,
-- | State.loading is the runtime UI state.
isInteractive :: ButtonElementState -> Boolean
isInteractive s = not (isLoading s)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set focused state.
setFocused :: Boolean -> ButtonElementState -> ButtonElementState
setFocused b s = s { focused = FocusedFlag b }

-- | Set hovered state.
setHovered :: Boolean -> ButtonElementState -> ButtonElementState
setHovered b s = s { hovered = HoveredFlag b }

-- | Set pressed state.
setPressed :: Boolean -> ButtonElementState -> ButtonElementState
setPressed b s = s { pressed = PressedFlag b }

-- | Set loading state.
-- |
-- | When loading becomes true, pressed is automatically cleared
-- | (the click action has been triggered, now waiting for result).
setLoading :: Boolean -> ButtonElementState -> ButtonElementState
setLoading b s = s 
  { loading = LoadingFlag b
  , pressed = if b then PressedFlag false else s.pressed
  }

-- | Set animating state.
setAnimating :: Boolean -> ButtonElementState -> ButtonElementState
setAnimating b s = s { animating = AnimatingFlag b }

-- | Reset all interaction flags to idle.
-- |
-- | Useful when button is programmatically disabled or hidden.
-- | Preserves loading state (that's async, not interaction).
resetInteraction :: ButtonElementState -> ButtonElementState
resetInteraction s = s
  { focused = FocusedFlag false
  , hovered = HoveredFlag false
  , pressed = PressedFlag false
  , animating = AnimatingFlag false
  }
