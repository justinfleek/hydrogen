-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // hydrogen // otpinput
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | One-Time Password (OTP) input component
-- |
-- | Multi-digit input for verification codes with auto-focus and paste support.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.OTPInput as OTPInput
-- |
-- | -- Basic 6-digit OTP
-- | OTPInput.otpInput
-- |   [ OTPInput.length 6
-- |   , OTPInput.value "123"
-- |   , OTPInput.onChange HandleOTPChange
-- |   , OTPInput.onComplete HandleOTPComplete
-- |   ]
-- |
-- | -- 4-digit with masked display
-- | OTPInput.otpInput
-- |   [ OTPInput.length 4
-- |   , OTPInput.masked true
-- |   , OTPInput.onChange HandleOTPChange
-- |   ]
-- |
-- | -- Alphanumeric code
-- | OTPInput.otpInput
-- |   [ OTPInput.length 6
-- |   , OTPInput.inputType OTPInput.Alphanumeric
-- |   , OTPInput.onChange HandleOTPChange
-- |   ]
-- |
-- | -- With resend timer
-- | OTPInput.otpInputWithResend
-- |   [ OTPInput.length 6
-- |   , OTPInput.resendCooldown 60
-- |   , OTPInput.onResend HandleResend
-- |   ]
-- | ```
module Hydrogen.Component.OTPInput
  ( -- * OTP Input Components
    otpInput
  , otpInputWithResend
  , otpDigit
    -- * Props
  , OTPInputProps
  , OTPInputProp
  , defaultProps
    -- * Prop Builders
  , length
  , value
  , inputType
  , masked
  , autoSubmit
  , disabled
  , error
  , errorMessage
  , resendCooldown
  , resendRemaining
  , className
  , onChange
  , onComplete
  , onResend
    -- * Types
  , OTPInputType(..)
    -- * FFI
  , OTPInputElement
  ) where

import Prelude hiding (map)

import Data.Array (foldl, range, (!!))
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String as String
import Effect (Effect)
import Effect.Uncurried (EffectFn1, EffectFn2, EffectFn3)
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)
import Web.DOM.Element (Element)
import Web.Event.Event (Event)
import Web.UIEvent.MouseEvent (MouseEvent)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Input type for OTP
data OTPInputType
  = Numeric
  | Alphanumeric

derive instance eqOTPInputType :: Eq OTPInputType

-- | Opaque OTP input element type
foreign import data OTPInputElement :: Type

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Initialize OTP input handling
foreign import initOTPInputImpl :: EffectFn3 Element (String -> Effect Unit) { length :: Int, numeric :: Boolean } OTPInputElement

-- | Handle paste event
foreign import handlePasteImpl :: EffectFn2 Event { length :: Int, numeric :: Boolean } String

-- | Focus specific digit
foreign import focusDigitImpl :: EffectFn2 Element Int Unit

-- | Cleanup OTP input
foreign import destroyOTPInputImpl :: EffectFn1 OTPInputElement Unit

-- | Start resend timer
foreign import startResendTimerImpl :: EffectFn2 Int (Int -> Effect Unit) Unit

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

type OTPInputProps i =
  { length :: Int
  , value :: String
  , inputType :: OTPInputType
  , masked :: Boolean
  , autoSubmit :: Boolean
  , disabled :: Boolean
  , error :: Boolean
  , errorMessage :: Maybe String
  , resendCooldown :: Int
  , resendRemaining :: Int
  , focusedIndex :: Int
  , className :: String
  , onChange :: Maybe (String -> i)
  , onComplete :: Maybe (String -> i)
  , onResend :: Maybe (MouseEvent -> i)
  }

type OTPInputProp i = OTPInputProps i -> OTPInputProps i

defaultProps :: forall i. OTPInputProps i
defaultProps =
  { length: 6
  , value: ""
  , inputType: Numeric
  , masked: false
  , autoSubmit: false
  , disabled: false
  , error: false
  , errorMessage: Nothing
  , resendCooldown: 60
  , resendRemaining: 0
  , focusedIndex: 0
  , className: ""
  , onChange: Nothing
  , onComplete: Nothing
  , onResend: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set number of digits
length :: forall i. Int -> OTPInputProp i
length l props = props { length = l }

-- | Set current value
value :: forall i. String -> OTPInputProp i
value v props = props { value = v }

-- | Set input type (numeric/alphanumeric)
inputType :: forall i. OTPInputType -> OTPInputProp i
inputType t props = props { inputType = t }

-- | Mask input (show dots)
masked :: forall i. Boolean -> OTPInputProp i
masked m props = props { masked = m }

-- | Auto-submit when complete
autoSubmit :: forall i. Boolean -> OTPInputProp i
autoSubmit a props = props { autoSubmit = a }

-- | Set disabled state
disabled :: forall i. Boolean -> OTPInputProp i
disabled d props = props { disabled = d }

-- | Set error state
error :: forall i. Boolean -> OTPInputProp i
error e props = props { error = e }

-- | Set error message
errorMessage :: forall i. String -> OTPInputProp i
errorMessage m props = props { errorMessage = Just m }

-- | Set resend cooldown in seconds
resendCooldown :: forall i. Int -> OTPInputProp i
resendCooldown c props = props { resendCooldown = c }

-- | Set remaining resend time
resendRemaining :: forall i. Int -> OTPInputProp i
resendRemaining r props = props { resendRemaining = r }

-- | Add custom class
className :: forall i. String -> OTPInputProp i
className c props = props { className = props.className <> " " <> c }

-- | Set change handler
onChange :: forall i. (String -> i) -> OTPInputProp i
onChange handler props = props { onChange = Just handler }

-- | Set complete handler (all digits filled)
onComplete :: forall i. (String -> i) -> OTPInputProp i
onComplete handler props = props { onComplete = Just handler }

-- | Set resend handler
onResend :: forall i. (MouseEvent -> i) -> OTPInputProp i
onResend handler props = props { onResend = Just handler }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Main OTP input component
otpInput :: forall w i. Array (OTPInputProp i) -> HH.HTML w i
otpInput propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    digits = range 0 (props.length - 1)
  in
    HH.div
      [ cls [ "flex flex-col gap-2", props.className ] ]
      [ HH.div
          [ cls [ "flex gap-2 justify-center" ]
          , ARIA.role "group"
          , ARIA.label "One-time password input"
          ]
          ( map (\idx -> otpDigit props idx) digits )
      , case props.errorMessage of
          Just msg ->
            HH.div
              [ cls [ "text-sm text-destructive text-center" ] ]
              [ HH.text msg ]
          Nothing -> HH.text ""
      ]

-- | OTP input with resend button
otpInputWithResend :: forall w i. Array (OTPInputProp i) -> HH.HTML w i
otpInputWithResend propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
  in
    HH.div
      [ cls [ "flex flex-col gap-4", props.className ] ]
      [ otpInput propMods
      , HH.div
          [ cls [ "text-center" ] ]
          [ if props.resendRemaining > 0
              then
                HH.span
                  [ cls [ "text-sm text-muted-foreground" ] ]
                  [ HH.text ("Resend code in " <> show props.resendRemaining <> "s") ]
              else
                HH.button
                  ( [ cls 
                        [ "text-sm text-primary hover:underline focus:outline-none focus:ring-2 focus:ring-ring rounded"
                        ]
                    ] <> case props.onResend of
                      Just handler -> [ HE.onClick handler ]
                      Nothing -> []
                  )
                  [ HH.text "Resend code" ]
          ]
      ]

-- | Single OTP digit input
otpDigit :: forall w i. OTPInputProps i -> Int -> HH.HTML w i
otpDigit props idx =
  let
    digitValue = String.take 1 (String.drop idx props.value)
    hasValue = String.length digitValue > 0
    displayValue = 
      if hasValue && props.masked 
        then "•" 
        else digitValue
    isFocused = idx == props.focusedIndex
    
    inputClasses =
      [ "w-12 h-14 text-center text-xl font-semibold rounded-lg border-2"
      , "focus:outline-none focus:ring-2 focus:ring-ring focus:ring-offset-2"
      , "transition-all duration-150"
      , if props.error
          then "border-destructive bg-destructive/10"
          else if hasValue
            then "border-primary bg-primary/5"
            else "border-input bg-background"
      , if props.disabled then "opacity-50 cursor-not-allowed" else ""
      ]
  in
    HH.input
      [ cls inputClasses
      , HP.type_ HP.InputText
      , HP.value displayValue
      , HP.disabled props.disabled
      , HP.attr (HH.AttrName "maxlength") "1"
      , HP.attr (HH.AttrName "inputmode") (if props.inputType == Numeric then "numeric" else "text")
      , HP.attr (HH.AttrName "pattern") (if props.inputType == Numeric then "[0-9]" else "[a-zA-Z0-9]")
      , HP.attr (HH.AttrName "autocomplete") "one-time-code"
      , HP.attr (HH.AttrName "data-otp-index") (show idx)
      , ARIA.label ("Digit " <> show (idx + 1) <> " of " <> show props.length)
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // helpers

-- | Map function for arrays (FFI for performance in DOM operations)
map :: forall a b. (a -> b) -> Array a -> Array b
map f xs = mapImpl f xs

foreign import mapImpl :: forall a b. (a -> b) -> Array a -> Array b
