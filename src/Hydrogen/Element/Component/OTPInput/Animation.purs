-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // element // otpinput // animation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | OTPInput Animation — CSS animation styles for OTP feedback.
-- |
-- | ## Animation Philosophy
-- |
-- | Animations provide immediate user feedback for:
-- |
-- | 1. **Entry** — Scale pop when digit is typed
-- | 2. **Error** — Shake animation on validation failure
-- | 3. **Success** — Pulse animation on verification success
-- | 4. **Loading** — Subtle pulse during verification
-- |
-- | All animations are CSS-based for performance. Durations are configurable
-- | via Props to respect user preferences (reduced motion).
-- |
-- | ## CSS Animation Strategy
-- |
-- | We generate inline CSS animation styles rather than requiring external
-- | stylesheets. This keeps the component self-contained.
-- |
-- | ## Dependencies
-- |
-- | - Types module for DigitAnimationState, OTPState
-- | - Props module for animation duration configuration

module Hydrogen.Element.Component.OTPInput.Animation
  ( -- * Animation Styles
    getAnimationStyles
  , getShakeAnimation
  , getPulseAnimation
  , getEntryAnimation
  , getLoadingAnimation
  
  -- * Animation State Computation
  , computeDigitAnimationState
  , shouldAnimate
  
  -- * CSS Keyframe Generators
  , shakeKeyframes
  , pulseKeyframes
  , entryKeyframes
  , loadingKeyframes
  
  -- * Timing Functions
  , getEasing
  , formatDuration
  ) where

import Prelude
  ( show
  , (==)
  , (<>)
  , (&&)
  , not
  )

import Data.Array (elem)
import Data.Maybe (Maybe(Nothing, Just))

import Hydrogen.Render.Element as E

import Hydrogen.Element.Component.OTPInput.Types
  ( DigitAnimationState(DigitIdle, DigitEntering, DigitFilled, DigitError, DigitSuccess)
  , OTPState(Idle, Entering, Verifying, Success, Error)
  , OTPDigit(OTPDigit)
  , OTPIndex
  )

import Hydrogen.Element.Component.OTPInput.Props
  ( OTPInputProps
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // animation styles
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get all animation-related CSS styles for a digit.
-- | Returns empty array if animations are disabled.
getAnimationStyles 
  :: forall msg 
   . OTPInputProps msg 
  -> DigitAnimationState 
  -> Array (E.Attribute msg)
getAnimationStyles props animState =
  if not props.animationEnabled
    then []
    else case animState of
      DigitIdle -> []
      DigitEntering -> getEntryAnimation props
      DigitFilled -> []
      DigitError -> getShakeAnimation props
      DigitSuccess -> getPulseAnimation props

-- | Get shake animation styles for error feedback
getShakeAnimation :: forall msg. OTPInputProps msg -> Array (E.Attribute msg)
getShakeAnimation props =
  [ E.style "animation-name" "otp-shake"
  , E.style "animation-duration" (formatDuration props.shakeDuration)
  , E.style "animation-timing-function" (getEasing "ease-out")
  , E.style "animation-fill-mode" "forwards"
  ]

-- | Get pulse animation styles for success feedback
getPulseAnimation :: forall msg. OTPInputProps msg -> Array (E.Attribute msg)
getPulseAnimation props =
  [ E.style "animation-name" "otp-pulse"
  , E.style "animation-duration" (formatDuration props.pulseDuration)
  , E.style "animation-timing-function" (getEasing "ease-in-out")
  , E.style "animation-fill-mode" "forwards"
  ]

-- | Get entry animation styles for digit input
getEntryAnimation :: forall msg. OTPInputProps msg -> Array (E.Attribute msg)
getEntryAnimation props =
  [ E.style "animation-name" "otp-entry"
  , E.style "animation-duration" (formatDuration props.entryDuration)
  , E.style "animation-timing-function" (getEasing "ease-out")
  , E.style "animation-fill-mode" "forwards"
  ]

-- | Get loading animation styles for verification state
getLoadingAnimation :: forall msg. OTPInputProps msg -> Array (E.Attribute msg)
getLoadingAnimation props =
  [ E.style "animation-name" "otp-loading"
  , E.style "animation-duration" "1000ms"
  , E.style "animation-timing-function" (getEasing "ease-in-out")
  , E.style "animation-iteration-count" "infinite"
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                    // animation state computation
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Compute the animation state for a digit based on component state.
-- |
-- | All OTPState variants handled explicitly for exhaustiveness.
computeDigitAnimationState 
  :: OTPState 
  -> OTPDigit 
  -> Boolean  -- ^ Is this digit currently being entered?
  -> DigitAnimationState
computeDigitAnimationState state digit isEntering =
  case state of
    Idle ->
      case digit of
        OTPDigit Nothing -> DigitIdle
        OTPDigit (Just _) -> DigitFilled
    Entering ->
      if isEntering
        then DigitEntering
        else case digit of
          OTPDigit Nothing -> DigitIdle
          OTPDigit (Just _) -> DigitFilled
    Verifying ->
      case digit of
        OTPDigit Nothing -> DigitIdle
        OTPDigit (Just _) -> DigitFilled
    Success ->
      DigitSuccess
    Error ->
      DigitError

-- | Check if animations should run (respects animationEnabled prop)
shouldAnimate :: forall msg. OTPInputProps msg -> Boolean
shouldAnimate props = props.animationEnabled

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // css keyframe generators
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Generate CSS keyframes for shake animation.
-- | This would be injected into a style tag at runtime.
shakeKeyframes :: String
shakeKeyframes =
  "@keyframes otp-shake { " <>
    "0%, 100% { transform: translateX(0); } " <>
    "10%, 30%, 50%, 70%, 90% { transform: translateX(-4px); } " <>
    "20%, 40%, 60%, 80% { transform: translateX(4px); } " <>
  "}"

-- | Generate CSS keyframes for pulse animation.
pulseKeyframes :: String
pulseKeyframes =
  "@keyframes otp-pulse { " <>
    "0% { transform: scale(1); } " <>
    "50% { transform: scale(1.05); } " <>
    "100% { transform: scale(1); } " <>
  "}"

-- | Generate CSS keyframes for entry animation.
entryKeyframes :: String
entryKeyframes =
  "@keyframes otp-entry { " <>
    "0% { transform: scale(0.8); opacity: 0.5; } " <>
    "100% { transform: scale(1); opacity: 1; } " <>
  "}"

-- | Generate CSS keyframes for loading animation.
loadingKeyframes :: String
loadingKeyframes =
  "@keyframes otp-loading { " <>
    "0%, 100% { opacity: 1; } " <>
    "50% { opacity: 0.6; } " <>
  "}"

-- | Get all keyframes combined for injection
allKeyframes :: String
allKeyframes =
  shakeKeyframes <> " " <>
  pulseKeyframes <> " " <>
  entryKeyframes <> " " <>
  loadingKeyframes

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // timing functions
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get CSS easing function by name
getEasing :: String -> String
getEasing name =
  if elem name validEasings
    then name
    else "ease"
  where
    validEasings = 
      [ "linear"
      , "ease"
      , "ease-in"
      , "ease-out"
      , "ease-in-out"
      ]

-- | Format duration as CSS value (ms)
formatDuration :: Int -> String
formatDuration ms = show ms <> "ms"
