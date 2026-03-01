-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // element // otpinput // props
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | OTPInput Props — Complete Schema-native property system.
-- |
-- | ## Design Philosophy
-- |
-- | Props are the bridge between user configuration and component rendering.
-- | Every visual property maps to a Schema pillar atom — no escape hatches.
-- |
-- | ## Schema Pillars Used
-- |
-- | | Pillar     | Atoms                                        |
-- | |------------|----------------------------------------------|
-- | | Color      | RGB, Gradient                                |
-- | | Dimension  | Pixel, Temporal (Milliseconds)               |
-- | | Geometry   | Radius, Transform (Scale)                    |
-- | | Typography | FontSize, FontWeight, FontFamily             |
-- | | Elevation  | Shadow (LayeredShadow)                       |
-- | | Motion     | Easing, Transition                           |
-- | | Attestation| UUID5 (instance identity)                    |
-- |
-- | ## Prop Modifier Pattern
-- |
-- | Components accept `Array (OTPInputProp msg)` which fold over `defaultProps`.
-- |
-- | ## Module Structure
-- |
-- | This is a leader module re-exporting from:
-- | - Types: Core type definitions (OTPInputProps, OTPInputProp)
-- | - Defaults: Default property values (defaultProps)
-- | - Content: Content prop builders (digitCount, value, state, etc.)
-- | - Color: Color prop builders (background, border, text colors)
-- | - Visual: Visual prop builders (gradients, shadows, geometry, typography)
-- | - Behavior: Behavior prop builders (handlers, animations, separators)

module Hydrogen.Element.Compound.OTPInput.Props
  ( module Types
  , module Defaults
  , module Content
  , module Color
  , module Visual
  , module Behavior
  ) where

import Hydrogen.Element.Compound.OTPInput.Props.Types
  ( OTPInputProp
  , OTPInputProps
  ) as Types

import Hydrogen.Element.Compound.OTPInput.Props.Defaults
  ( defaultProps
  ) as Defaults

import Hydrogen.Element.Compound.OTPInput.Props.Content
  ( digitCountProp
  , disabledProp
  , errorMessageProp
  , focusedIndexProp
  , helpTextProp
  , instanceIdProp
  , labelProp
  , maskedProp
  , otpInputTypeProp
  , otpValueProp
  , resendCooldownProp
  , resendRemainingProp
  , stateProp
  , successMessageProp
  ) as Content

import Hydrogen.Element.Compound.OTPInput.Props.Color
  ( backgroundColorProp
  , borderColorProp
  , errorBorderColorProp
  , errorTextColorProp
  , filledBorderColorProp
  , focusBackgroundColorProp
  , focusBorderColorProp
  , hoverBackgroundColorProp
  , hoverBorderColorProp
  , labelColorProp
  , mutedTextColorProp
  , placeholderCharProp
  , placeholderColorProp
  , primaryColorProp
  , separatorColorProp
  , successBorderColorProp
  , successTextColorProp
  , textColorProp
  ) as Color

import Hydrogen.Element.Compound.OTPInput.Props.Visual
  ( backgroundGradientProp
  , borderRadiusProp
  , borderWidthProp
  , cursorStyleProp
  , digitHeightProp
  , digitWidthProp
  , errorShadowProp
  , focusBackgroundGradientProp
  , focusScaleProp
  , focusShadowProp
  , fontFamilyProp
  , fontSizeProp
  , fontWeightProp
  , gapProp
  , hoverScaleProp
  , hoverShadowProp
  , letterSpacingProp
  , pressScaleProp
  , separatorWidthProp
  , shadowProp
  , successShadowProp
  ) as Visual

import Hydrogen.Element.Compound.OTPInput.Props.Behavior
  ( animationEnabledProp
  , autoAdvanceProp
  , autoFocusProp
  , autoSubmitProp
  , entryDurationProp
  , onBlurProp
  , onCompleteProp
  , onDigitBlurProp
  , onDigitChangeProp
  , onDigitDeleteProp
  , onDigitFocusProp
  , onDigitInputProp
  , onDigitKeyDownProp
  , onFocusProp
  , onPasteProp
  , onResendClickProp
  , pulseDurationProp
  , reducedMotionProp
  , separatorCharProp
  , separatorEnabledProp
  , separatorPositionsProp
  , shakeDurationProp
  , staggerDelayProp
  , transitionDurationProp
  , transitionEasingProp
  ) as Behavior
