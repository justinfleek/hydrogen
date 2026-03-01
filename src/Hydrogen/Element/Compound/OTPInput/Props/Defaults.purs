-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // otpinput // props // defaults
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | OTPInput Props Defaults — Sensible default values for OTP input.
-- |
-- | Uses 6 digits (standard TOTP), empty value, numeric input.
-- | All durations use Schema.Dimension.Temporal.Milliseconds.

module Hydrogen.Element.Compound.OTPInput.Props.Defaults
  ( defaultProps
  ) where

import Data.Maybe (Maybe(Nothing))

import Hydrogen.Element.Compound.OTPInput.Types
  ( OTPInputType(Numeric)
  , OTPState(Idle)
  , emptyOTP
  , digitCount
  )

import Hydrogen.Element.Compound.OTPInput.Props.Types (OTPInputProps)

import Hydrogen.Schema.Dimension.Temporal as Temporal
import Hydrogen.Schema.Motion.Easing as Easing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // default values
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default properties with sensible Schema values.
-- |
-- | Uses 6 digits (standard TOTP), empty value, numeric input.
-- | All durations use Schema.Dimension.Temporal.Milliseconds.
-- |
-- | Color values default to Nothing — theme layer provides actual colors.
-- | This separation allows components to be theme-agnostic.
defaultProps :: forall msg. OTPInputProps msg
defaultProps =
  { -- Content
    digitCount: digitCount 6
  , value: emptyOTP (digitCount 6)
  , inputType: Numeric
  , masked: false
  , disabled: false
  , state: Idle
  , errorMessage: Nothing
  , successMessage: Nothing
  , helpText: Nothing
  , label: Nothing
  , focusedIndex: Nothing
  , resendCooldown: 60
  , resendRemaining: 0
  , instanceId: Nothing
  
  -- Colors (Nothing = use theme defaults at render time)
  , backgroundColor: Nothing
  , borderColor: Nothing
  , focusBorderColor: Nothing
  , hoverBorderColor: Nothing
  , errorBorderColor: Nothing
  , successBorderColor: Nothing
  , filledBorderColor: Nothing
  , textColor: Nothing
  , placeholderColor: Nothing
  , placeholderChar: Nothing
  , errorTextColor: Nothing
  , successTextColor: Nothing
  , mutedTextColor: Nothing
  , primaryColor: Nothing
  , focusBackgroundColor: Nothing
  , hoverBackgroundColor: Nothing
  
  -- Gradients
  , backgroundGradient: Nothing
  , focusBackgroundGradient: Nothing
  
  -- Shadows/Elevation
  , shadow: Nothing
  , focusShadow: Nothing
  , hoverShadow: Nothing
  , errorShadow: Nothing
  , successShadow: Nothing
  
  -- Geometry
  , borderRadius: Nothing
  , borderWidth: Nothing
  , focusScale: Nothing
  , hoverScale: Nothing
  , pressScale: Nothing
  
  -- Dimensions
  , digitWidth: Nothing
  , digitHeight: Nothing
  , gap: Nothing
  , separatorWidth: Nothing
  
  -- Typography
  , fontSize: Nothing
  , fontWeight: Nothing
  , fontFamily: Nothing
  , letterSpacing: Nothing
  
  -- Behavior
  , onDigitChange: Nothing
  , onComplete: Nothing
  , onResendClick: Nothing
  , onFocus: Nothing
  , onBlur: Nothing
  , onPaste: Nothing
  , onDigitInput: Nothing
  , onDigitDelete: Nothing
  , onDigitKeyDown: Nothing
  , onDigitFocus: Nothing
  , onDigitBlur: Nothing
  , autoSubmit: false
  , autoFocus: false
  
  -- Animation (using proper Schema temporal types)
  , animationEnabled: true
  , reducedMotion: false
  , shakeDuration: Temporal.ms 500.0
  , pulseDuration: Temporal.ms 300.0
  , entryDuration: Temporal.ms 150.0
  , transitionDuration: Temporal.ms 150.0
  , transitionEasing: Easing.easeOut
  , staggerDelay: Temporal.ms 50.0
  
  -- Separator
  , separatorEnabled: false
  , separatorPositions: []
  , separatorChar: '-'
  , separatorColor: Nothing
  
  -- Label and help text colors
  , labelColor: Nothing
  
  -- Auto-advance (default true for typical OTP UX)
  , autoAdvance: true
  
  -- Cursor
  , cursorStyle: "text"
  }
