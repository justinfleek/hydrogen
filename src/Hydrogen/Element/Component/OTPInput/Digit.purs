-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // element // otpinput // digit
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | OTPInput Digit — Single digit input rendering.
-- |
-- | ## Design Philosophy
-- |
-- | Each OTP digit is rendered as an individual input element. This module
-- | handles the visual representation with Schema-native styling:
-- |
-- | - Border states (default, focused, filled, error, success)
-- | - Text display (digit, masked dot, placeholder)
-- | - Focus ring effects
-- | - Disabled state styling
-- |
-- | ## Dependencies
-- |
-- | - Types module for OTPDigit, OTPIndex, OTPState
-- | - Props module for OTPInputProps
-- | - Validation module for input patterns
-- | - Element module for rendering

module Hydrogen.Element.Component.OTPInput.Digit
  ( -- * Digit Rendering
    renderDigit
  , renderDigitInput
  
  -- * Style Computation
  , getDigitBorderColor
  , getDigitBackgroundColor
  , getDigitTextColor
  , getDefaultBorderColor
  , getDefaultTextColor
  , getFocusRingStyle
  
  -- * State Helpers
  , isDigitFocused
  , isDigitFilled
  , getDigitDisplayValue
  ) where

import Prelude
  ( show
  , (==)
  , (<>)
  , (+)
  )

import Data.Maybe (Maybe(Nothing, Just))
import Data.String.CodeUnits as SCU

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Typography.FontSize as FontSize

import Hydrogen.Element.Component.OTPInput.Types
  ( OTPDigit(OTPDigit)
  , OTPIndex
  , OTPState(Idle, Entering, Verifying, Success, Error)
  , unwrapOTPIndex
  , unwrapDigitCount
  , getDigitAt
  , otpIndex
  )

import Hydrogen.Element.Component.OTPInput.Props
  ( OTPInputProps
  )

import Hydrogen.Element.Component.OTPInput.Validation
  ( getInputMode
  , getInputPattern
  , getAutoComplete
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // digit rendering
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render a single OTP digit at the given index.
-- | This is the main entry point for digit rendering.
renderDigit :: forall msg. OTPInputProps msg -> Int -> E.Element msg
renderDigit props idx =
  let
    boundedIndex = otpIndex props.digitCount idx
    digit = getDigitAt boundedIndex props.value
    isFocused = isDigitFocused props boundedIndex
    hasFill = isDigitFilled digit
    displayValue = getDigitDisplayValue props.masked digit
  in
    renderDigitInput props boundedIndex digit isFocused hasFill displayValue

-- | Render the actual input element for a digit
renderDigitInput 
  :: forall msg
   . OTPInputProps msg 
  -> OTPIndex 
  -> OTPDigit 
  -> Boolean 
  -> Boolean 
  -> String 
  -> E.Element msg
renderDigitInput props idx _digit isFocused hasFill displayValue =
  let
    idxInt = unwrapOTPIndex idx
    totalDigits = unwrapDigitCount props.digitCount
  in
    E.input_
      ( [ -- Core attributes
          E.type_ "text"
        , E.value displayValue
        , E.disabled props.disabled
        , E.attr "maxlength" "1"
        , E.attr "inputmode" (getInputMode props.inputType)
        , E.attr "pattern" (getInputPattern props.inputType)
        , E.attr "autocomplete" getAutoComplete
        , E.dataAttr "otp-index" (show idxInt)
        
        -- Accessibility
        , E.ariaLabel ("Digit " <> show (idxInt + 1) <> " of " <> show totalDigits)
        , E.role "textbox"
        
        -- Core styles
        , E.style "width" (getDigitWidth props)
        , E.style "height" (getDigitHeight props)
        , E.style "text-align" "center"
        , E.style "font-size" (getFontSize props)
        , E.style "font-weight" (getFontWeight props)
        , E.style "font-family" "inherit"
        , E.style "border-style" "solid"
        , E.style "border-width" (getBorderWidth props)
        , E.style "border-radius" (getBorderRadius props)
        , E.style "outline" "none"
        , E.style "transition" "border-color 150ms ease-out, background-color 150ms ease-out, box-shadow 150ms ease-out, transform 150ms ease-out"
        , E.style "caret-color" "transparent"
        
        -- Computed styles based on state
        , E.style "border-color" (getDigitBorderColor props hasFill isFocused)
        , E.style "background-color" (getDigitBackgroundColor props)
        , E.style "color" (getDigitTextColor props)
        ]
        <> getFocusRingStyle props isFocused
        <> getDisabledStyles props
      )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // style computation
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get border color based on component state and digit state
-- | Priority: focus > error > success > filled > default
-- |
-- | All OTPState variants handled explicitly for exhaustiveness.
getDigitBorderColor :: forall msg. OTPInputProps msg -> Boolean -> Boolean -> String
getDigitBorderColor props hasFill isFocused =
  if isFocused
    then case props.focusBorderColor of
           Just c -> Color.toLegacyCss c
           Nothing -> "#3b82f6"  -- blue-500 default
    else case props.state of
      Error ->
        case props.errorBorderColor of
          Just c -> Color.toLegacyCss c
          Nothing -> "#ef4444"  -- red-500 default
      Success ->
        case props.successBorderColor of
          Just c -> Color.toLegacyCss c
          Nothing -> "#22c55e"  -- green-500 default
      Verifying ->
        case props.borderColor of
          Just c -> Color.toLegacyCss c
          Nothing -> "#e2e8f0"  -- slate-200 default
      Idle ->
        getDefaultBorderColor props hasFill
      Entering ->
        getDefaultBorderColor props hasFill

-- | Get default border color (filled vs empty)
getDefaultBorderColor :: forall msg. OTPInputProps msg -> Boolean -> String
getDefaultBorderColor props hasFill =
  if hasFill
    then case props.filledBorderColor of
           Just c -> Color.toLegacyCss c
           Nothing -> "#3b82f6"  -- blue-500 default
    else case props.borderColor of
           Just c -> Color.toLegacyCss c
           Nothing -> "#e2e8f0"  -- slate-200 default

-- | Get digit background color
getDigitBackgroundColor :: forall msg. OTPInputProps msg -> String
getDigitBackgroundColor props =
  case props.backgroundColor of
    Just c -> Color.toLegacyCss c
    Nothing -> "#ffffff"

-- | Get digit text color
-- |
-- | All OTPState variants handled explicitly for exhaustiveness.
getDigitTextColor :: forall msg. OTPInputProps msg -> String
getDigitTextColor props =
  case props.state of
    Error ->
      case props.errorTextColor of
        Just c -> Color.toLegacyCss c
        Nothing -> getDefaultTextColor props
    Success ->
      case props.successTextColor of
        Just c -> Color.toLegacyCss c
        Nothing -> getDefaultTextColor props
    Verifying ->
      getDefaultTextColor props
    Idle ->
      getDefaultTextColor props
    Entering ->
      getDefaultTextColor props

-- | Get default text color
getDefaultTextColor :: forall msg. OTPInputProps msg -> String
getDefaultTextColor props =
  case props.textColor of
    Just c -> Color.toLegacyCss c
    Nothing -> "#0f172a"  -- slate-900 default

-- | Get focus ring style attributes
getFocusRingStyle :: forall msg. OTPInputProps msg -> Boolean -> Array (E.Attribute msg)
getFocusRingStyle props isFocused =
  if isFocused
    then
      let ringColor = case props.focusBorderColor of
                        Just c -> Color.toLegacyCss c
                        Nothing -> "#3b82f6"
      in [ E.style "box-shadow" ("0 0 0 3px " <> ringColor <> "33") ]  -- 33 = 20% opacity
    else []

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // state helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Check if this digit is currently focused
isDigitFocused :: forall msg. OTPInputProps msg -> OTPIndex -> Boolean
isDigitFocused props idx =
  case props.focusedIndex of
    Nothing -> false
    Just focusedIdx -> focusedIdx == idx

-- | Check if a digit has a value
isDigitFilled :: OTPDigit -> Boolean
isDigitFilled (OTPDigit Nothing) = false
isDigitFilled (OTPDigit (Just _)) = true

-- | Get display value for a digit (handles masking)
getDigitDisplayValue :: Boolean -> OTPDigit -> String
getDigitDisplayValue _ (OTPDigit Nothing) = ""
getDigitDisplayValue masked (OTPDigit (Just c)) =
  if masked
    then "•"
    else SCU.singleton c

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // dimension helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get digit width CSS value
getDigitWidth :: forall msg. OTPInputProps msg -> String
getDigitWidth props =
  case props.digitWidth of
    Just w -> show w
    Nothing -> "48px"

-- | Get digit height CSS value
getDigitHeight :: forall msg. OTPInputProps msg -> String
getDigitHeight props =
  case props.digitHeight of
    Just h -> show h
    Nothing -> "56px"

-- | Get font size CSS value
getFontSize :: forall msg. OTPInputProps msg -> String
getFontSize props =
  case props.fontSize of
    Just s -> FontSize.toLegacyCss s
    Nothing -> "20px"

-- | Get font weight CSS value
getFontWeight :: forall msg. OTPInputProps msg -> String
getFontWeight props =
  case props.fontWeight of
    Just w -> show w
    Nothing -> "600"

-- | Get border width CSS value
getBorderWidth :: forall msg. OTPInputProps msg -> String
getBorderWidth props =
  case props.borderWidth of
    Just w -> show w
    Nothing -> "2px"

-- | Get border radius CSS value
getBorderRadius :: forall msg. OTPInputProps msg -> String
getBorderRadius props =
  case props.borderRadius of
    Just r -> Geometry.toLegacyCss r
    Nothing -> "8px"

-- | Get disabled state styles
getDisabledStyles :: forall msg. OTPInputProps msg -> Array (E.Attribute msg)
getDisabledStyles props =
  if props.disabled
    then 
      [ E.style "opacity" "0.5"
      , E.style "cursor" "not-allowed"
      ]
    else []
