-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // element // otpinput // props
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | OTPInput Props — Schema-native property system for OTP components.
-- |
-- | ## Design Philosophy
-- |
-- | Props are the bridge between user configuration and component rendering.
-- | Every visual property maps to a Schema pillar atom — no escape hatches.
-- |
-- | ## Prop Modifier Pattern
-- |
-- | Components accept `Array (OTPInputProp msg)` which fold over `defaultProps`:
-- |
-- | ```purescript
-- | otpInput
-- |   [ digitCount (OTPDigitCount 6)
-- |   , borderColor brand.inputBorder
-- |   , focusBorderColor brand.primaryColor
-- |   ]
-- | ```
-- |
-- | ## Dependencies
-- |
-- | - Types module for OTPDigitCount, OTPInputType, OTPValue, OTPState
-- | - Schema pillars: Color.RGB, Geometry.Radius, Dimension.Device, Typography

module Hydrogen.Element.Component.OTPInput.Props
  ( -- * Props Record
    OTPInputProps
  , OTPInputProp
  , defaultProps
  
  -- * Content Props
  , digitCountProp
  , otpValueProp
  , otpInputTypeProp
  , maskedProp
  , disabledProp
  , stateProp
  , errorMessageProp
  , focusedIndexProp
  , resendCooldownProp
  , resendRemainingProp
  
  -- * Color Atoms
  , backgroundColorProp
  , borderColorProp
  , focusBorderColorProp
  , errorBorderColorProp
  , successBorderColorProp
  , filledBorderColorProp
  , textColorProp
  , placeholderColorProp
  , errorTextColorProp
  , successTextColorProp
  , mutedTextColorProp
  , primaryColorProp
  
  -- * Geometry Atoms
  , borderRadiusProp
  , borderWidthProp
  
  -- * Dimension Atoms
  , digitWidthProp
  , digitHeightProp
  , gapProp
  
  -- * Typography Atoms
  , fontSizeProp
  , fontWeightProp
  
  -- * Behavior Props
  , onDigitChangeProp
  , onCompleteProp
  , onResendClickProp
  , onFocusProp
  , onBlurProp
  , onPasteProp
  
  -- * Animation Props
  , animationEnabledProp
  , shakeDurationProp
  , pulseDurationProp
  , entryDurationProp
  ) where

import Data.Maybe (Maybe(Nothing, Just))

import Hydrogen.Element.Component.OTPInput.Types
  ( OTPDigitCount
  , OTPInputType(Numeric)
  , OTPValue
  , OTPIndex
  , OTPState(Idle)
  , emptyOTP
  , digitCount
  )

import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Typography.FontSize as FontSize

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // props record
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Complete OTP input configuration.
-- |
-- | All visual properties are Schema atoms. No strings for colors, sizes, etc.
type OTPInputProps msg =
  { -- Content (using bounded types from Types module)
    digitCount :: OTPDigitCount
  , value :: OTPValue
  , inputType :: OTPInputType
  , masked :: Boolean
  , disabled :: Boolean
  , state :: OTPState
  , errorMessage :: Maybe String
  , focusedIndex :: Maybe OTPIndex
  , resendCooldown :: Int
  , resendRemaining :: Int
  
  -- Color atoms (Schema.Color.RGB)
  , backgroundColor :: Maybe Color.RGB
  , borderColor :: Maybe Color.RGB
  , focusBorderColor :: Maybe Color.RGB
  , errorBorderColor :: Maybe Color.RGB
  , successBorderColor :: Maybe Color.RGB
  , filledBorderColor :: Maybe Color.RGB
  , textColor :: Maybe Color.RGB
  , placeholderColor :: Maybe Color.RGB
  , errorTextColor :: Maybe Color.RGB
  , successTextColor :: Maybe Color.RGB
  , mutedTextColor :: Maybe Color.RGB
  , primaryColor :: Maybe Color.RGB
  
  -- Geometry atoms (Schema.Geometry.Radius)
  , borderRadius :: Maybe Geometry.Radius
  , borderWidth :: Maybe Device.Pixel
  
  -- Dimension atoms (Schema.Dimension.Device)
  , digitWidth :: Maybe Device.Pixel
  , digitHeight :: Maybe Device.Pixel
  , gap :: Maybe Device.Pixel
  
  -- Typography atoms
  , fontSize :: Maybe FontSize.FontSize
  , fontWeight :: Maybe Int
  
  -- Behavior handlers
  , onDigitChange :: Maybe (OTPValue -> msg)
  , onComplete :: Maybe (OTPValue -> msg)
  , onResendClick :: Maybe msg
  , onFocus :: Maybe (OTPIndex -> msg)
  , onBlur :: Maybe (OTPIndex -> msg)
  , onPaste :: Maybe (String -> msg)
  
  -- Animation configuration
  , animationEnabled :: Boolean
  , shakeDuration :: Int     -- milliseconds
  , pulseDuration :: Int     -- milliseconds
  , entryDuration :: Int     -- milliseconds
  }

-- | Property modifier function
type OTPInputProp msg = OTPInputProps msg -> OTPInputProps msg

-- | Default properties with sensible Schema values.
-- |
-- | Uses 6 digits (standard TOTP), empty value, numeric input.
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
  , focusedIndex: Nothing
  , resendCooldown: 60
  , resendRemaining: 0
  
  -- Colors (Nothing = use theme defaults at render time)
  , backgroundColor: Nothing
  , borderColor: Nothing
  , focusBorderColor: Nothing
  , errorBorderColor: Nothing
  , successBorderColor: Nothing
  , filledBorderColor: Nothing
  , textColor: Nothing
  , placeholderColor: Nothing
  , errorTextColor: Nothing
  , successTextColor: Nothing
  , mutedTextColor: Nothing
  , primaryColor: Nothing
  
  -- Geometry
  , borderRadius: Nothing
  , borderWidth: Nothing
  
  -- Dimensions
  , digitWidth: Nothing
  , digitHeight: Nothing
  , gap: Nothing
  
  -- Typography
  , fontSize: Nothing
  , fontWeight: Nothing
  
  -- Behavior
  , onDigitChange: Nothing
  , onComplete: Nothing
  , onResendClick: Nothing
  , onFocus: Nothing
  , onBlur: Nothing
  , onPaste: Nothing
  
  -- Animation
  , animationEnabled: true
  , shakeDuration: 500
  , pulseDuration: 300
  , entryDuration: 150
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // content prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set number of OTP digits (4-8)
digitCountProp :: forall msg. OTPDigitCount -> OTPInputProp msg
digitCountProp n props = props { digitCount = n }

-- | Set current OTP value
otpValueProp :: forall msg. OTPValue -> OTPInputProp msg
otpValueProp v props = props { value = v }

-- | Set input type (numeric or alphanumeric)
otpInputTypeProp :: forall msg. OTPInputType -> OTPInputProp msg
otpInputTypeProp t props = props { inputType = t }

-- | Enable/disable input masking (dots instead of characters)
maskedProp :: forall msg. Boolean -> OTPInputProp msg
maskedProp m props = props { masked = m }

-- | Enable/disable the entire input
disabledProp :: forall msg. Boolean -> OTPInputProp msg
disabledProp d props = props { disabled = d }

-- | Set component state (Idle, Entering, Verifying, Success, Error)
stateProp :: forall msg. OTPState -> OTPInputProp msg
stateProp s props = props { state = s }

-- | Set error message text
errorMessageProp :: forall msg. String -> OTPInputProp msg
errorMessageProp m props = props { errorMessage = Just m }

-- | Set currently focused digit index
focusedIndexProp :: forall msg. OTPIndex -> OTPInputProp msg
focusedIndexProp i props = props { focusedIndex = Just i }

-- | Set resend cooldown duration in seconds
resendCooldownProp :: forall msg. Int -> OTPInputProp msg
resendCooldownProp c props = props { resendCooldown = c }

-- | Set remaining resend cooldown time in seconds
resendRemainingProp :: forall msg. Int -> OTPInputProp msg
resendRemainingProp r props = props { resendRemaining = r }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // color prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set digit input background color
backgroundColorProp :: forall msg. Color.RGB -> OTPInputProp msg
backgroundColorProp c props = props { backgroundColor = Just c }

-- | Set default digit border color
borderColorProp :: forall msg. Color.RGB -> OTPInputProp msg
borderColorProp c props = props { borderColor = Just c }

-- | Set focused digit border color
focusBorderColorProp :: forall msg. Color.RGB -> OTPInputProp msg
focusBorderColorProp c props = props { focusBorderColor = Just c }

-- | Set error state border color
errorBorderColorProp :: forall msg. Color.RGB -> OTPInputProp msg
errorBorderColorProp c props = props { errorBorderColor = Just c }

-- | Set success state border color
successBorderColorProp :: forall msg. Color.RGB -> OTPInputProp msg
successBorderColorProp c props = props { successBorderColor = Just c }

-- | Set filled (has value) digit border color
filledBorderColorProp :: forall msg. Color.RGB -> OTPInputProp msg
filledBorderColorProp c props = props { filledBorderColor = Just c }

-- | Set digit text color
textColorProp :: forall msg. Color.RGB -> OTPInputProp msg
textColorProp c props = props { textColor = Just c }

-- | Set placeholder/empty digit color
placeholderColorProp :: forall msg. Color.RGB -> OTPInputProp msg
placeholderColorProp c props = props { placeholderColor = Just c }

-- | Set error message text color
errorTextColorProp :: forall msg. Color.RGB -> OTPInputProp msg
errorTextColorProp c props = props { errorTextColor = Just c }

-- | Set success message text color
successTextColorProp :: forall msg. Color.RGB -> OTPInputProp msg
successTextColorProp c props = props { successTextColor = Just c }

-- | Set muted/secondary text color
mutedTextColorProp :: forall msg. Color.RGB -> OTPInputProp msg
mutedTextColorProp c props = props { mutedTextColor = Just c }

-- | Set primary/accent color
primaryColorProp :: forall msg. Color.RGB -> OTPInputProp msg
primaryColorProp c props = props { primaryColor = Just c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                      // geometry prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set digit border radius
borderRadiusProp :: forall msg. Geometry.Radius -> OTPInputProp msg
borderRadiusProp r props = props { borderRadius = Just r }

-- | Set digit border width
borderWidthProp :: forall msg. Device.Pixel -> OTPInputProp msg
borderWidthProp w props = props { borderWidth = Just w }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                     // dimension prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set digit input width
digitWidthProp :: forall msg. Device.Pixel -> OTPInputProp msg
digitWidthProp w props = props { digitWidth = Just w }

-- | Set digit input height
digitHeightProp :: forall msg. Device.Pixel -> OTPInputProp msg
digitHeightProp h props = props { digitHeight = Just h }

-- | Set gap between digit inputs
gapProp :: forall msg. Device.Pixel -> OTPInputProp msg
gapProp g props = props { gap = Just g }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                    // typography prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set digit font size
fontSizeProp :: forall msg. FontSize.FontSize -> OTPInputProp msg
fontSizeProp s props = props { fontSize = Just s }

-- | Set digit font weight (100-900)
fontWeightProp :: forall msg. Int -> OTPInputProp msg
fontWeightProp w props = props { fontWeight = Just w }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                      // behavior prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set handler for OTP value changes
onDigitChangeProp :: forall msg. (OTPValue -> msg) -> OTPInputProp msg
onDigitChangeProp handler props = props { onDigitChange = Just handler }

-- | Set handler for OTP completion (all digits filled)
onCompleteProp :: forall msg. (OTPValue -> msg) -> OTPInputProp msg
onCompleteProp handler props = props { onComplete = Just handler }

-- | Set handler for resend button click
onResendClickProp :: forall msg. msg -> OTPInputProp msg
onResendClickProp handler props = props { onResendClick = Just handler }

-- | Set handler for digit focus
onFocusProp :: forall msg. (OTPIndex -> msg) -> OTPInputProp msg
onFocusProp handler props = props { onFocus = Just handler }

-- | Set handler for digit blur
onBlurProp :: forall msg. (OTPIndex -> msg) -> OTPInputProp msg
onBlurProp handler props = props { onBlur = Just handler }

-- | Set handler for paste events
onPasteProp :: forall msg. (String -> msg) -> OTPInputProp msg
onPasteProp handler props = props { onPaste = Just handler }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                     // animation prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Enable/disable animations
animationEnabledProp :: forall msg. Boolean -> OTPInputProp msg
animationEnabledProp enabled props = props { animationEnabled = enabled }

-- | Set error shake animation duration (milliseconds)
shakeDurationProp :: forall msg. Int -> OTPInputProp msg
shakeDurationProp ms props = props { shakeDuration = ms }

-- | Set success pulse animation duration (milliseconds)
pulseDurationProp :: forall msg. Int -> OTPInputProp msg
pulseDurationProp ms props = props { pulseDuration = ms }

-- | Set digit entry animation duration (milliseconds)
entryDurationProp :: forall msg. Int -> OTPInputProp msg
entryDurationProp ms props = props { entryDuration = ms }
