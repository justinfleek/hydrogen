-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // element // otpinput
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | OTPInput — Schema-native one-time password input component.
-- |
-- | ## Design Philosophy
-- |
-- | This component renders a row of single-character inputs for OTP/PIN entry.
-- | All visual properties are Schema atoms — no Tailwind, no CSS strings.
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property            | Pillar     | Type                | CSS Output           |
-- | |---------------------|------------|---------------------|----------------------|
-- | | backgroundColor     | Color      | Color.RGB           | input background     |
-- | | borderColor         | Color      | Color.RGB           | default border       |
-- | | focusBorderColor    | Color      | Color.RGB           | focused border       |
-- | | errorBorderColor    | Color      | Color.RGB           | error border         |
-- | | filledBorderColor   | Color      | Color.RGB           | filled digit border  |
-- | | textColor           | Color      | Color.RGB           | digit text color     |
-- | | errorTextColor      | Color      | Color.RGB           | error message color  |
-- | | borderRadius        | Geometry   | Geometry.Radius     | input corners        |
-- | | digitWidth          | Dimension  | Device.Pixel        | each digit width     |
-- | | digitHeight         | Dimension  | Device.Pixel        | each digit height    |
-- | | gap                 | Dimension  | Device.Pixel        | spacing between      |
-- | | fontSize            | Typography | FontSize            | digit font size      |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Component.OTPInput as OTP
-- |
-- | -- Basic 6-digit OTP
-- | OTP.otpInput
-- |   [ OTP.digitCount 6
-- |   , OTP.otpValue "123"
-- |   , OTP.onDigitChange HandleChange
-- |   ]
-- |
-- | -- With brand colors
-- | OTP.otpInput
-- |   [ OTP.digitCount 4
-- |   , OTP.borderColor brand.inputBorder
-- |   , OTP.focusBorderColor brand.primaryColor
-- |   , OTP.borderRadius brand.inputRadius
-- |   ]
-- | ```

module Hydrogen.Element.Component.OTPInput
  ( -- * Components
    otpInput
  , otpInputWithResend
  , otpDigit
  
  -- * Types
  , OTPInputType(Numeric, Alphanumeric)
  , OTPMsg(DigitChanged, DigitFocused, Completed, ResendClicked)
  
  -- * Props
  , OTPInputProps
  , OTPInputProp
  , defaultProps
  
  -- * Content Props
  , digitCount
  , otpValue
  , otpInputType
  , masked
  , otpDisabled
  , otpError
  , otpErrorMessage
  , focusedIndex
  , resendCooldown
  , resendRemaining
  
  -- * Color Atoms
  , backgroundColor
  , borderColor
  , focusBorderColor
  , errorBorderColor
  , filledBorderColor
  , textColor
  , errorTextColor
  , mutedTextColor
  , primaryColor
  
  -- * Geometry Atoms
  , borderRadius
  
  -- * Dimension Atoms
  , digitWidth
  , digitHeight
  , otpGap
  
  -- * Typography Atoms
  , fontSize
  
  -- * Behavior Props
  , onDigitChange
  , onComplete
  , onResendClick
  ) where

import Prelude
  ( class Eq
  , class Show
  , map
  , show
  , (+)
  , (-)
  , (<>)
  , (==)
  , (>)
  , (&&)
  )

import Data.Array (foldl, range)
import Data.Maybe (Maybe(Nothing, Just))
import Data.String as String

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Typography.FontSize as FontSize

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Input type for OTP digits
data OTPInputType
  = Numeric       -- ^ Only digits 0-9
  | Alphanumeric  -- ^ Letters and digits

derive instance eqOTPInputType :: Eq OTPInputType

instance showOTPInputType :: Show OTPInputType where
  show Numeric = "numeric"
  show Alphanumeric = "alphanumeric"

-- | OTP component messages
data OTPMsg
  = DigitChanged String      -- ^ Full value changed
  | DigitFocused Int         -- ^ A digit was focused
  | Completed String         -- ^ All digits filled
  | ResendClicked            -- ^ Resend button clicked

derive instance eqOTPMsg :: Eq OTPMsg

instance showOTPMsg :: Show OTPMsg where
  show (DigitChanged v) = "DigitChanged(" <> v <> ")"
  show (DigitFocused i) = "DigitFocused(" <> show i <> ")"
  show (Completed v) = "Completed(" <> v <> ")"
  show ResendClicked = "ResendClicked"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | OTP input properties
type OTPInputProps msg =
  { -- Content
    digitCount :: Int
  , value :: String
  , inputType :: OTPInputType
  , masked :: Boolean
  , disabled :: Boolean
  , error :: Boolean
  , errorMessage :: Maybe String
  , focusedIndex :: Int
  , resendCooldown :: Int
  , resendRemaining :: Int
  
  -- Color atoms
  , backgroundColor :: Maybe Color.RGB
  , borderColor :: Maybe Color.RGB
  , focusBorderColor :: Maybe Color.RGB
  , errorBorderColor :: Maybe Color.RGB
  , filledBorderColor :: Maybe Color.RGB
  , textColor :: Maybe Color.RGB
  , errorTextColor :: Maybe Color.RGB
  , mutedTextColor :: Maybe Color.RGB
  , primaryColor :: Maybe Color.RGB
  
  -- Geometry atoms
  , borderRadius :: Maybe Geometry.Radius
  
  -- Dimension atoms
  , digitWidth :: Maybe Device.Pixel
  , digitHeight :: Maybe Device.Pixel
  , gap :: Maybe Device.Pixel
  
  -- Typography atoms
  , fontSize :: Maybe FontSize.FontSize
  
  -- Behavior
  , onDigitChange :: Maybe (String -> msg)
  , onComplete :: Maybe (String -> msg)
  , onResendClick :: Maybe msg
  }

-- | Property modifier
type OTPInputProp msg = OTPInputProps msg -> OTPInputProps msg

-- | Default properties
defaultProps :: forall msg. OTPInputProps msg
defaultProps =
  { digitCount: 6
  , value: ""
  , inputType: Numeric
  , masked: false
  , disabled: false
  , error: false
  , errorMessage: Nothing
  , focusedIndex: 0
  , resendCooldown: 60
  , resendRemaining: 0
  , backgroundColor: Nothing
  , borderColor: Nothing
  , focusBorderColor: Nothing
  , errorBorderColor: Nothing
  , filledBorderColor: Nothing
  , textColor: Nothing
  , errorTextColor: Nothing
  , mutedTextColor: Nothing
  , primaryColor: Nothing
  , borderRadius: Nothing
  , digitWidth: Nothing
  , digitHeight: Nothing
  , gap: Nothing
  , fontSize: Nothing
  , onDigitChange: Nothing
  , onComplete: Nothing
  , onResendClick: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: content
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set number of digits
digitCount :: forall msg. Int -> OTPInputProp msg
digitCount n props = props { digitCount = n }

-- | Set current OTP value
otpValue :: forall msg. String -> OTPInputProp msg
otpValue v props = props { value = v }

-- | Set input type (numeric/alphanumeric)
otpInputType :: forall msg. OTPInputType -> OTPInputProp msg
otpInputType t props = props { inputType = t }

-- | Mask input (show dots instead of characters)
masked :: forall msg. Boolean -> OTPInputProp msg
masked m props = props { masked = m }

-- | Set disabled state
otpDisabled :: forall msg. Boolean -> OTPInputProp msg
otpDisabled d props = props { disabled = d }

-- | Set error state
otpError :: forall msg. Boolean -> OTPInputProp msg
otpError e props = props { error = e }

-- | Set error message
otpErrorMessage :: forall msg. String -> OTPInputProp msg
otpErrorMessage m props = props { errorMessage = Just m }

-- | Set currently focused digit index
focusedIndex :: forall msg. Int -> OTPInputProp msg
focusedIndex i props = props { focusedIndex = i }

-- | Set resend cooldown in seconds
resendCooldown :: forall msg. Int -> OTPInputProp msg
resendCooldown c props = props { resendCooldown = c }

-- | Set remaining resend time
resendRemaining :: forall msg. Int -> OTPInputProp msg
resendRemaining r props = props { resendRemaining = r }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // prop builders: color
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set digit background color
backgroundColor :: forall msg. Color.RGB -> OTPInputProp msg
backgroundColor c props = props { backgroundColor = Just c }

-- | Set default digit border color
borderColor :: forall msg. Color.RGB -> OTPInputProp msg
borderColor c props = props { borderColor = Just c }

-- | Set focused digit border color
focusBorderColor :: forall msg. Color.RGB -> OTPInputProp msg
focusBorderColor c props = props { focusBorderColor = Just c }

-- | Set error state border color
errorBorderColor :: forall msg. Color.RGB -> OTPInputProp msg
errorBorderColor c props = props { errorBorderColor = Just c }

-- | Set filled digit border color
filledBorderColor :: forall msg. Color.RGB -> OTPInputProp msg
filledBorderColor c props = props { filledBorderColor = Just c }

-- | Set digit text color
textColor :: forall msg. Color.RGB -> OTPInputProp msg
textColor c props = props { textColor = Just c }

-- | Set error message text color
errorTextColor :: forall msg. Color.RGB -> OTPInputProp msg
errorTextColor c props = props { errorTextColor = Just c }

-- | Set muted/secondary text color
mutedTextColor :: forall msg. Color.RGB -> OTPInputProp msg
mutedTextColor c props = props { mutedTextColor = Just c }

-- | Set primary/accent color
primaryColor :: forall msg. Color.RGB -> OTPInputProp msg
primaryColor c props = props { primaryColor = Just c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                      // prop builders: geometry
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set digit border radius
borderRadius :: forall msg. Geometry.Radius -> OTPInputProp msg
borderRadius r props = props { borderRadius = Just r }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                     // prop builders: dimension
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set digit input width
digitWidth :: forall msg. Device.Pixel -> OTPInputProp msg
digitWidth w props = props { digitWidth = Just w }

-- | Set digit input height
digitHeight :: forall msg. Device.Pixel -> OTPInputProp msg
digitHeight h props = props { digitHeight = Just h }

-- | Set gap between digits
otpGap :: forall msg. Device.Pixel -> OTPInputProp msg
otpGap g props = props { gap = Just g }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: typography
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set digit font size
fontSize :: forall msg. FontSize.FontSize -> OTPInputProp msg
fontSize s props = props { fontSize = Just s }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                      // prop builders: behavior
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set change handler (receives full OTP value)
onDigitChange :: forall msg. (String -> msg) -> OTPInputProp msg
onDigitChange handler props = props { onDigitChange = Just handler }

-- | Set completion handler (all digits filled)
onComplete :: forall msg. (String -> msg) -> OTPInputProp msg
onComplete handler props = props { onComplete = Just handler }

-- | Set resend button click handler
onResendClick :: forall msg. msg -> OTPInputProp msg
onResendClick handler props = props { onResendClick = Just handler }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render OTP input
otpInput :: forall msg. Array (OTPInputProp msg) -> E.Element msg
otpInput propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    digits = range 0 (props.digitCount - 1)
  in
    E.div_
      ( [ E.style "display" "flex"
        , E.style "flex-direction" "column"
        , E.style "gap" "8px"
        , E.style "align-items" "center"
        ]
      )
      [ -- Digits row
        E.div_
          ( [ E.attr "role" "group"
            , E.ariaLabel "One-time password input"
            , E.style "display" "flex"
            , E.style "gap" (getGap props)
            , E.style "justify-content" "center"
            ]
          )
          (map (otpDigit props) digits)
      , -- Error message
        renderErrorMessage props
      ]

-- | Render OTP input with resend button
otpInputWithResend :: forall msg. Array (OTPInputProp msg) -> E.Element msg
otpInputWithResend propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
  in
    E.div_
      ( [ E.style "display" "flex"
        , E.style "flex-direction" "column"
        , E.style "gap" "16px"
        , E.style "align-items" "center"
        ]
      )
      [ otpInput propMods
      , renderResendSection props
      ]

-- | Render a single OTP digit input
otpDigit :: forall msg. OTPInputProps msg -> Int -> E.Element msg
otpDigit props idx =
  let
    digitValue = String.take 1 (String.drop idx props.value)
    hasValue = String.length digitValue > 0
    displayValue = if hasValue && props.masked then "•" else digitValue
    isFocused = idx == props.focusedIndex
    
    -- Determine border color based on state (focus takes priority)
    borderStyle = getBorderColor props hasValue isFocused
  in
    E.input_
      ( [ E.type_ "text"
        , E.value displayValue
        , E.disabled props.disabled
        , E.attr "maxlength" "1"
        , E.attr "inputmode" (if props.inputType == Numeric then "numeric" else "text")
        , E.attr "pattern" (if props.inputType == Numeric then "[0-9]" else "[a-zA-Z0-9]")
        , E.attr "autocomplete" "one-time-code"
        , E.attr "data-otp-index" (show idx)
        , E.ariaLabel ("Digit " <> show (idx + 1) <> " of " <> show props.digitCount)
        -- Core styles
        , E.style "width" (getDigitWidth props)
        , E.style "height" (getDigitHeight props)
        , E.style "text-align" "center"
        , E.style "font-size" (getFontSize props)
        , E.style "font-weight" "600"
        , E.style "border-style" "solid"
        , E.style "border-width" "2px"
        , E.style "border-radius" (getBorderRadius props)
        , E.style "outline" "none"
        , E.style "transition" "border-color 150ms ease-out, background-color 150ms ease-out, box-shadow 150ms ease-out"
        , E.style "background-color" (getBackgroundColor props)
        , E.style "color" (getTextColor props)
        ]
        <> borderStyle
        <> getFocusRingStyles props isFocused
        <> getDisabledStyles props
      )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render error message if present
renderErrorMessage :: forall msg. OTPInputProps msg -> E.Element msg
renderErrorMessage props = case props.errorMessage of
  Just msg ->
    E.div_
      ( [ E.style "font-size" "14px"
        , E.style "color" (getErrorTextColor props)
        , E.style "text-align" "center"
        ]
      )
      [ E.text msg ]
  Nothing -> E.empty

-- | Render resend section
renderResendSection :: forall msg. OTPInputProps msg -> E.Element msg
renderResendSection props =
  E.div_
    [ E.style "text-align" "center" ]
    [ if props.resendRemaining > 0
        then
          E.span_
            ( [ E.style "font-size" "14px"
              , E.style "color" (getMutedTextColor props)
              ]
            )
            [ E.text ("Resend code in " <> show props.resendRemaining <> "s") ]
        else
          renderResendButton props
    ]

-- | Render resend button
renderResendButton :: forall msg. OTPInputProps msg -> E.Element msg
renderResendButton props =
  E.button_
    ( [ E.type_ "button"
      , E.style "font-size" "14px"
      , E.style "color" (getPrimaryColor props)
      , E.style "background" "transparent"
      , E.style "border" "none"
      , E.style "cursor" "pointer"
      , E.style "text-decoration" "underline"
      , E.style "padding" "0"
      ]
      <> case props.onResendClick of
           Just handler -> [ E.onClick handler ]
           Nothing -> []
    )
    [ E.text "Resend code" ]

-- | Get gap value
getGap :: forall msg. OTPInputProps msg -> String
getGap props = case props.gap of
  Just g -> show g
  Nothing -> "8px"

-- | Get digit width
getDigitWidth :: forall msg. OTPInputProps msg -> String
getDigitWidth props = case props.digitWidth of
  Just w -> show w
  Nothing -> "48px"

-- | Get digit height
getDigitHeight :: forall msg. OTPInputProps msg -> String
getDigitHeight props = case props.digitHeight of
  Just h -> show h
  Nothing -> "56px"

-- | Get font size
getFontSize :: forall msg. OTPInputProps msg -> String
getFontSize props = case props.fontSize of
  Just s -> FontSize.toLegacyCss s
  Nothing -> "20px"

-- | Get border radius
getBorderRadius :: forall msg. OTPInputProps msg -> String
getBorderRadius props = case props.borderRadius of
  Just r -> Geometry.toLegacyCss r
  Nothing -> "8px"

-- | Get background color
getBackgroundColor :: forall msg. OTPInputProps msg -> String
getBackgroundColor props = case props.backgroundColor of
  Just c -> Color.toLegacyCss c
  Nothing -> "#ffffff"

-- | Get text color
getTextColor :: forall msg. OTPInputProps msg -> String
getTextColor props = case props.textColor of
  Just c -> Color.toLegacyCss c
  Nothing -> "#0f172a"

-- | Get error text color
getErrorTextColor :: forall msg. OTPInputProps msg -> String
getErrorTextColor props = case props.errorTextColor of
  Just c -> Color.toLegacyCss c
  Nothing -> "#ef4444"

-- | Get muted text color
getMutedTextColor :: forall msg. OTPInputProps msg -> String
getMutedTextColor props = case props.mutedTextColor of
  Just c -> Color.toLegacyCss c
  Nothing -> "#64748b"

-- | Get primary color
getPrimaryColor :: forall msg. OTPInputProps msg -> String
getPrimaryColor props = case props.primaryColor of
  Just c -> Color.toLegacyCss c
  Nothing -> "#3b82f6"

-- | Get border color based on state (focus > error > filled > default)
getBorderColor :: forall msg. OTPInputProps msg -> Boolean -> Boolean -> Array (E.Attribute msg)
getBorderColor props hasValue isFocused =
  let
    color = 
      if isFocused
        then case props.focusBorderColor of
               Just c -> Color.toLegacyCss c
               Nothing -> "#3b82f6"
        else if props.error
          then case props.errorBorderColor of
                 Just c -> Color.toLegacyCss c
                 Nothing -> "#ef4444"
          else if hasValue
            then case props.filledBorderColor of
                   Just c -> Color.toLegacyCss c
                   Nothing -> "#3b82f6"
            else case props.borderColor of
                   Just c -> Color.toLegacyCss c
                   Nothing -> "#e2e8f0"
  in
    [ E.style "border-color" color ]

-- | Get focus ring styles when digit is focused
getFocusRingStyles :: forall msg. OTPInputProps msg -> Boolean -> Array (E.Attribute msg)
getFocusRingStyles props isFocused =
  if isFocused
    then 
      let ringColor = case props.focusBorderColor of
                        Just c -> Color.toLegacyCss c
                        Nothing -> "#3b82f6"
      in [ E.style "box-shadow" ("0 0 0 2px " <> ringColor <> "40") ]  -- 40 = 25% opacity in hex
    else []

-- | Get disabled styles
getDisabledStyles :: forall msg. OTPInputProps msg -> Array (E.Attribute msg)
getDisabledStyles props =
  if props.disabled
    then [ E.style "opacity" "0.5", E.style "cursor" "not-allowed" ]
    else []
