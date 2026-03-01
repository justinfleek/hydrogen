-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // otpinput // props // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | OTPInput Props Types — Core type definitions for OTP input configuration.
-- |
-- | This module defines the complete property record type using Schema atoms.
-- | All visual properties map to Schema pillar atoms — no escape hatches.

module Hydrogen.Element.Compound.OTPInput.Props.Types
  ( OTPInputProps
  , OTPInputProp
  ) where

import Data.Maybe (Maybe)

import Hydrogen.Element.Compound.OTPInput.Types
  ( OTPDigitCount
  , OTPInputType
  , OTPValue
  , OTPIndex
  , OTPState
  )

import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Color.Gradient as Gradient
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Geometry.Transform as Transform
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Dimension.Temporal as Temporal
import Hydrogen.Schema.Elevation.Shadow as Shadow
import Hydrogen.Schema.Motion.Easing as Easing
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Typography.FontWeight as FontWeight
import Hydrogen.Schema.Typography.FontFamily as FontFamily
import Hydrogen.Schema.Attestation.UUID5 as UUID5

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // props record
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete OTP input configuration using Schema atoms.
-- |
-- | All visual properties are typed Schema atoms. No strings for colors, sizes.
-- | Instance identity via UUID5 ensures uniqueness at billion-agent scale.
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
type OTPInputProps msg =
  { -- Content (bounded types from Types module)
    digitCount :: OTPDigitCount
  , value :: OTPValue
  , inputType :: OTPInputType
  , masked :: Boolean
  , disabled :: Boolean
  , state :: OTPState
  , errorMessage :: Maybe String
  , successMessage :: Maybe String
  , helpText :: Maybe String
  , label :: Maybe String
  , focusedIndex :: Maybe OTPIndex
  , resendCooldown :: Int
  , resendRemaining :: Int
  , instanceId :: Maybe UUID5.UUID5
  
  -- Color atoms (Schema.Color.RGB)
  , backgroundColor :: Maybe Color.RGB
  , borderColor :: Maybe Color.RGB
  , focusBorderColor :: Maybe Color.RGB
  , hoverBorderColor :: Maybe Color.RGB
  , errorBorderColor :: Maybe Color.RGB
  , successBorderColor :: Maybe Color.RGB
  , filledBorderColor :: Maybe Color.RGB
  , textColor :: Maybe Color.RGB
  , placeholderColor :: Maybe Color.RGB
  , placeholderChar :: Maybe Char
  , errorTextColor :: Maybe Color.RGB
  , successTextColor :: Maybe Color.RGB
  , mutedTextColor :: Maybe Color.RGB
  , primaryColor :: Maybe Color.RGB
  , focusBackgroundColor :: Maybe Color.RGB
  , hoverBackgroundColor :: Maybe Color.RGB
  
  -- Gradient atoms (Schema.Color.Gradient)
  , backgroundGradient :: Maybe Gradient.Gradient
  , focusBackgroundGradient :: Maybe Gradient.Gradient
  
  -- Elevation atoms (Schema.Elevation.Shadow)
  , shadow :: Maybe Shadow.LayeredShadow
  , focusShadow :: Maybe Shadow.LayeredShadow
  , hoverShadow :: Maybe Shadow.LayeredShadow
  , errorShadow :: Maybe Shadow.LayeredShadow
  , successShadow :: Maybe Shadow.LayeredShadow
  
  -- Geometry atoms (Schema.Geometry)
  , borderRadius :: Maybe Geometry.Radius
  , borderWidth :: Maybe Device.Pixel
  , focusScale :: Maybe Transform.Scale
  , hoverScale :: Maybe Transform.Scale
  , pressScale :: Maybe Transform.Scale
  
  -- Dimension atoms (Schema.Dimension.Device)
  , digitWidth :: Maybe Device.Pixel
  , digitHeight :: Maybe Device.Pixel
  , gap :: Maybe Device.Pixel
  , separatorWidth :: Maybe Device.Pixel
  
  -- Typography atoms (Schema.Typography)
  , fontSize :: Maybe FontSize.FontSize
  , fontWeight :: Maybe FontWeight.FontWeight
  , fontFamily :: Maybe FontFamily.FontFamily
  , letterSpacing :: Maybe Device.Pixel
  
  -- Behavior handlers
  , onDigitChange :: Maybe (OTPValue -> msg)
  , onComplete :: Maybe (OTPValue -> msg)
  , onResendClick :: Maybe msg
  , onFocus :: Maybe (OTPIndex -> msg)
  , onBlur :: Maybe (OTPIndex -> msg)
  , onPaste :: Maybe (String -> msg)
  
  -- Raw event handlers (more granular control)
  , onDigitInput :: Maybe (OTPIndex -> Char -> msg)
  , onDigitDelete :: Maybe (OTPIndex -> msg)
  , onDigitKeyDown :: Maybe (OTPIndex -> String -> msg)
  , onDigitFocus :: Maybe (OTPIndex -> msg)
  , onDigitBlur :: Maybe (OTPIndex -> msg)
  
  -- Behavior flags
  , autoSubmit :: Boolean
  , autoFocus :: Boolean
  
  -- Animation configuration (Schema.Dimension.Temporal, Schema.Motion.Easing)
  , animationEnabled :: Boolean
  , reducedMotion :: Boolean
  , shakeDuration :: Temporal.Milliseconds
  , pulseDuration :: Temporal.Milliseconds
  , entryDuration :: Temporal.Milliseconds
  , transitionDuration :: Temporal.Milliseconds
  , transitionEasing :: Easing.Easing
  , staggerDelay :: Temporal.Milliseconds
  
  -- Separator configuration (for XXX-XXX patterns)
  , separatorEnabled :: Boolean
  , separatorPositions :: Array Int
  , separatorChar :: Char
  , separatorColor :: Maybe Color.RGB
  
  -- Label and help text colors
  , labelColor :: Maybe Color.RGB
  
  -- Auto-advance behavior (focus moves to next digit automatically)
  , autoAdvance :: Boolean
  
  -- Cursor configuration
  , cursorStyle :: String
  }

-- | Property modifier function
-- |
-- | Props are composed via function application: `prop1 >>> prop2 >>> prop3`
-- | or via foldl: `foldl (\p f -> f p) defaultProps [prop1, prop2, prop3]`
type OTPInputProp msg = OTPInputProps msg -> OTPInputProps msg
