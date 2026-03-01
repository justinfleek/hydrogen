-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // otpinput // props // behavior
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | OTPInput Behavior Props — Builders for behavior and event handlers.
-- |
-- | Behavior props control:
-- | - Event handlers (onChange, onComplete, onFocus, onBlur, etc.)
-- | - Behavior flags (autoSubmit, autoFocus, autoAdvance)
-- | - Animation configuration (durations, easing, stagger)
-- | - Separator configuration (for XXX-XXX patterns)

module Hydrogen.Element.Compound.OTPInput.Props.Behavior
  ( -- * Event Handlers
    onDigitChangeProp
  , onCompleteProp
  , onResendClickProp
  , onFocusProp
  , onBlurProp
  , onPasteProp
  
  -- * Granular Event Handlers
  , onDigitInputProp
  , onDigitDeleteProp
  , onDigitKeyDownProp
  , onDigitFocusProp
  , onDigitBlurProp
  
  -- * Behavior Flags
  , autoSubmitProp
  , autoFocusProp
  , autoAdvanceProp
  
  -- * Animation Configuration
  , animationEnabledProp
  , reducedMotionProp
  , shakeDurationProp
  , pulseDurationProp
  , entryDurationProp
  , transitionDurationProp
  , transitionEasingProp
  , staggerDelayProp
  
  -- * Separator Configuration
  , separatorEnabledProp
  , separatorPositionsProp
  , separatorCharProp
  ) where

import Data.Maybe (Maybe(Just))

import Hydrogen.Element.Compound.OTPInput.Types
  ( OTPValue
  , OTPIndex
  )

import Hydrogen.Element.Compound.OTPInput.Props.Types (OTPInputProp)

import Hydrogen.Schema.Dimension.Temporal as Temporal
import Hydrogen.Schema.Motion.Easing as Easing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // event handler builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set handler for OTP value changes
-- |
-- | Called whenever any digit changes. Receives the complete OTPValue.
onDigitChangeProp :: forall msg. (OTPValue -> msg) -> OTPInputProp msg
onDigitChangeProp handler props = props { onDigitChange = Just handler }

-- | Set handler for OTP completion (all digits filled)
-- |
-- | Called when the last digit is entered and all slots are filled.
onCompleteProp :: forall msg. (OTPValue -> msg) -> OTPInputProp msg
onCompleteProp handler props = props { onComplete = Just handler }

-- | Set handler for resend button click
-- |
-- | Called when user clicks "Resend Code" button.
onResendClickProp :: forall msg. msg -> OTPInputProp msg
onResendClickProp handler props = props { onResendClick = Just handler }

-- | Set handler for digit focus
-- |
-- | Called when any digit receives focus.
onFocusProp :: forall msg. (OTPIndex -> msg) -> OTPInputProp msg
onFocusProp handler props = props { onFocus = Just handler }

-- | Set handler for digit blur
-- |
-- | Called when focus leaves a digit.
onBlurProp :: forall msg. (OTPIndex -> msg) -> OTPInputProp msg
onBlurProp handler props = props { onBlur = Just handler }

-- | Set handler for paste events
-- |
-- | Called when user pastes text. Receives the pasted string.
onPasteProp :: forall msg. (String -> msg) -> OTPInputProp msg
onPasteProp handler props = props { onPaste = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                             // granular event handler builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set handler for digit input (character entered)
-- |
-- | Called with (index, character) when a character is entered.
-- | More granular than onDigitChange for per-digit tracking.
onDigitInputProp :: forall msg. (OTPIndex -> Char -> msg) -> OTPInputProp msg
onDigitInputProp handler props = props { onDigitInput = Just handler }

-- | Set handler for digit delete (backspace)
-- |
-- | Called with index when backspace is pressed at that digit.
onDigitDeleteProp :: forall msg. (OTPIndex -> msg) -> OTPInputProp msg
onDigitDeleteProp handler props = props { onDigitDelete = Just handler }

-- | Set handler for digit keydown (any key)
-- |
-- | Called with (index, keyCode) for any keypress.
-- | Useful for custom keyboard navigation.
onDigitKeyDownProp :: forall msg. (OTPIndex -> String -> msg) -> OTPInputProp msg
onDigitKeyDownProp handler props = props { onDigitKeyDown = Just handler }

-- | Set handler for digit focus (explicit)
-- |
-- | Called with index when a specific digit receives focus.
onDigitFocusProp :: forall msg. (OTPIndex -> msg) -> OTPInputProp msg
onDigitFocusProp handler props = props { onDigitFocus = Just handler }

-- | Set handler for digit blur (explicit)
-- |
-- | Called with index when a specific digit loses focus.
onDigitBlurProp :: forall msg. (OTPIndex -> msg) -> OTPInputProp msg
onDigitBlurProp handler props = props { onDigitBlur = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // behavior flag builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Enable auto-submit on completion
-- |
-- | When true, onComplete is called immediately when last digit is entered.
autoSubmitProp :: forall msg. Boolean -> OTPInputProp msg
autoSubmitProp enabled props = props { autoSubmit = enabled }

-- | Enable auto-focus on mount
-- |
-- | When true, first digit receives focus when component mounts.
autoFocusProp :: forall msg. Boolean -> OTPInputProp msg
autoFocusProp enabled props = props { autoFocus = enabled }

-- | Enable/disable auto-advance behavior
-- |
-- | When true (default), focus automatically advances to next digit after entry.
-- | Set to false for manual navigation between digits.
autoAdvanceProp :: forall msg. Boolean -> OTPInputProp msg
autoAdvanceProp enabled props = props { autoAdvance = enabled }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // animation prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Enable/disable animations
-- |
-- | Master toggle for all animations.
animationEnabledProp :: forall msg. Boolean -> OTPInputProp msg
animationEnabledProp enabled props = props { animationEnabled = enabled }

-- | Enable reduced motion (respects prefers-reduced-motion)
-- |
-- | When true, animations are minimized or disabled.
reducedMotionProp :: forall msg. Boolean -> OTPInputProp msg
reducedMotionProp enabled props = props { reducedMotion = enabled }

-- | Set error shake animation duration (Schema Milliseconds)
-- |
-- | Duration of the horizontal shake on error.
shakeDurationProp :: forall msg. Temporal.Milliseconds -> OTPInputProp msg
shakeDurationProp duration props = props { shakeDuration = duration }

-- | Set success pulse animation duration (Schema Milliseconds)
-- |
-- | Duration of the scale pulse on success.
pulseDurationProp :: forall msg. Temporal.Milliseconds -> OTPInputProp msg
pulseDurationProp duration props = props { pulseDuration = duration }

-- | Set digit entry animation duration (Schema Milliseconds)
-- |
-- | Duration of the pop-in animation when a digit is entered.
entryDurationProp :: forall msg. Temporal.Milliseconds -> OTPInputProp msg
entryDurationProp duration props = props { entryDuration = duration }

-- | Set transition duration for state changes (Schema Milliseconds)
-- |
-- | Duration of CSS transitions (color, border, shadow changes).
transitionDurationProp :: forall msg. Temporal.Milliseconds -> OTPInputProp msg
transitionDurationProp duration props = props { transitionDuration = duration }

-- | Set transition easing curve (Schema Motion.Easing)
-- |
-- | Easing function for all transitions.
transitionEasingProp :: forall msg. Easing.Easing -> OTPInputProp msg
transitionEasingProp easing props = props { transitionEasing = easing }

-- | Set stagger delay between digit animations (Schema Milliseconds)
-- |
-- | Delay between each digit's animation in sequence effects.
staggerDelayProp :: forall msg. Temporal.Milliseconds -> OTPInputProp msg
staggerDelayProp delay props = props { staggerDelay = delay }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // separator prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Enable/disable separators (for XXX-XXX patterns)
-- |
-- | When true, separator characters appear between digit groups.
separatorEnabledProp :: forall msg. Boolean -> OTPInputProp msg
separatorEnabledProp enabled props = props { separatorEnabled = enabled }

-- | Set separator positions (indices where separators appear)
-- |
-- | e.g., [3] for 6-digit OTP = XXX-XXX
-- | e.g., [2, 4] for 6-digit = XX-XX-XX
separatorPositionsProp :: forall msg. Array Int -> OTPInputProp msg
separatorPositionsProp positions props = props { separatorPositions = positions }

-- | Set separator character
-- |
-- | The character displayed between digit groups (default: '-').
separatorCharProp :: forall msg. Char -> OTPInputProp msg
separatorCharProp c props = props { separatorChar = c }
