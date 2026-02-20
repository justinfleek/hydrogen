-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                     // hydrogen // creditcard
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Credit card input component
-- |
-- | Formatted credit card input with card type detection and validation.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.CreditCard as CreditCard
-- |
-- | -- Basic credit card input
-- | CreditCard.creditCard
-- |   [ CreditCard.cardNumber "4111111111111111"
-- |   , CreditCard.expiryDate "12/25"
-- |   , CreditCard.cvv "123"
-- |   , CreditCard.onChange HandleCardChange
-- |   ]
-- |
-- | -- With cardholder name
-- | CreditCard.creditCard
-- |   [ CreditCard.cardNumber cardNum
-- |   , CreditCard.cardholderName "John Doe"
-- |   , CreditCard.showCardholderName true
-- |   ]
-- |
-- | -- With visual card preview
-- | CreditCard.creditCardWithPreview
-- |   [ CreditCard.cardNumber cardNum
-- |   , CreditCard.expiryDate expiry
-- |   , CreditCard.cvv cvv
-- |   , CreditCard.cardholderName name
-- |   ]
-- |
-- | -- Individual inputs
-- | CreditCard.cardNumberInput
-- |   [ CreditCard.cardNumber cardNum
-- |   , CreditCard.onCardNumberChange HandleNumberChange
-- |   ]
-- | ```
module Hydrogen.Component.CreditCard
  ( -- * Credit Card Components
    creditCard
  , creditCardWithPreview
  , cardNumberInput
  , expiryInput
  , cvvInput
  , cardholderInput
  , cardPreview
    -- * Props
  , CreditCardProps
  , CreditCardProp
  , defaultProps
    -- * Prop Builders
  , cardNumber
  , expiryDate
  , cvv
  , cardholderName
  , showCardholderName
  , showCardPreview
  , focusedField
  , disabled
  , className
  , onCardNumberChange
  , onExpiryChange
  , onCvvChange
  , onCardholderChange
  , onChange
  , onValidate
    -- * Types
  , CardType(..)
  , CardField(..)
  , CreditCardValue
  , CardValidation
    -- * Utilities
  , detectCardType
  , formatCardNumber
  , validateCardNumber
  , validateExpiry
  , validateCvv
  , luhnCheck
    -- * FFI
  , CreditCardElement
  ) where

import Prelude

import Data.Array (foldl, (!!))
import Data.Int (fromString)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String as String
import Data.String.Pattern (Pattern(..))
import Effect (Effect)
import Effect.Uncurried (EffectFn1, EffectFn2)
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)
import Web.DOM.Element (Element)
import Web.Event.Event (Event)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Credit card type
data CardType
  = Visa
  | Mastercard
  | Amex
  | Discover
  | DinersClub
  | JCB
  | UnionPay
  | Unknown

derive instance eqCardType :: Eq CardType

-- | Field currently focused
data CardField
  = CardNumber
  | Expiry
  | Cvv
  | Cardholder
  | NoField

derive instance eqCardField :: Eq CardField

-- | Credit card value
type CreditCardValue =
  { cardNumber :: String
  , expiryDate :: String
  , cvv :: String
  , cardholderName :: String
  , cardType :: CardType
  , isValid :: Boolean
  }

-- | Validation result for each field
type CardValidation =
  { cardNumber :: Boolean
  , expiry :: Boolean
  , cvv :: Boolean
  , cardholder :: Boolean
  , complete :: Boolean
  }

-- | Opaque credit card element type
foreign import data CreditCardElement :: Type

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Initialize credit card input
foreign import initCreditCardImpl :: EffectFn2 Element (CreditCardValue -> Effect Unit) CreditCardElement

-- | Format card number
foreign import formatCardNumberImpl :: String -> CardType -> String

-- | Cleanup credit card input
foreign import destroyCreditCardImpl :: EffectFn1 CreditCardElement Unit

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

type CreditCardProps i =
  { cardNumber :: String
  , expiryDate :: String
  , cvv :: String
  , cardholderName :: String
  , showCardholderName :: Boolean
  , showCardPreview :: Boolean
  , focusedField :: CardField
  , disabled :: Boolean
  , errors :: { cardNumber :: Maybe String, expiry :: Maybe String, cvv :: Maybe String, cardholder :: Maybe String }
  , className :: String
  , onCardNumberChange :: Maybe (String -> i)
  , onExpiryChange :: Maybe (String -> i)
  , onCvvChange :: Maybe (String -> i)
  , onCardholderChange :: Maybe (String -> i)
  , onChange :: Maybe (CreditCardValue -> i)
  , onValidate :: Maybe (CardValidation -> i)
  , onFocusChange :: Maybe (CardField -> i)
  }

type CreditCardProp i = CreditCardProps i -> CreditCardProps i

defaultProps :: forall i. CreditCardProps i
defaultProps =
  { cardNumber: ""
  , expiryDate: ""
  , cvv: ""
  , cardholderName: ""
  , showCardholderName: false
  , showCardPreview: false
  , focusedField: NoField
  , disabled: false
  , errors: { cardNumber: Nothing, expiry: Nothing, cvv: Nothing, cardholder: Nothing }
  , className: ""
  , onCardNumberChange: Nothing
  , onExpiryChange: Nothing
  , onCvvChange: Nothing
  , onCardholderChange: Nothing
  , onChange: Nothing
  , onValidate: Nothing
  , onFocusChange: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set card number
cardNumber :: forall i. String -> CreditCardProp i
cardNumber n props = props { cardNumber = n }

-- | Set expiry date
expiryDate :: forall i. String -> CreditCardProp i
expiryDate e props = props { expiryDate = e }

-- | Set CVV
cvv :: forall i. String -> CreditCardProp i
cvv c props = props { cvv = c }

-- | Set cardholder name
cardholderName :: forall i. String -> CreditCardProp i
cardholderName n props = props { cardholderName = n }

-- | Show cardholder name field
showCardholderName :: forall i. Boolean -> CreditCardProp i
showCardholderName s props = props { showCardholderName = s }

-- | Show visual card preview
showCardPreview :: forall i. Boolean -> CreditCardProp i
showCardPreview s props = props { showCardPreview = s }

-- | Set focused field
focusedField :: forall i. CardField -> CreditCardProp i
focusedField f props = props { focusedField = f }

-- | Set disabled state
disabled :: forall i. Boolean -> CreditCardProp i
disabled d props = props { disabled = d }

-- | Add custom class
className :: forall i. String -> CreditCardProp i
className c props = props { className = props.className <> " " <> c }

-- | Set card number change handler
onCardNumberChange :: forall i. (String -> i) -> CreditCardProp i
onCardNumberChange handler props = props { onCardNumberChange = Just handler }

-- | Set expiry change handler
onExpiryChange :: forall i. (String -> i) -> CreditCardProp i
onExpiryChange handler props = props { onExpiryChange = Just handler }

-- | Set CVV change handler
onCvvChange :: forall i. (String -> i) -> CreditCardProp i
onCvvChange handler props = props { onCvvChange = Just handler }

-- | Set cardholder name change handler
onCardholderChange :: forall i. (String -> i) -> CreditCardProp i
onCardholderChange handler props = props { onCardholderChange = Just handler }

-- | Set overall change handler
onChange :: forall i. (CreditCardValue -> i) -> CreditCardProp i
onChange handler props = props { onChange = Just handler }

-- | Set validation handler
onValidate :: forall i. (CardValidation -> i) -> CreditCardProp i
onValidate handler props = props { onValidate = Just handler }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // card detection
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Detect card type from number prefix
detectCardType :: String -> CardType
detectCardType numStr =
  let
    digits = String.replaceAll (Pattern " ") (String.Replacement "") numStr
    prefix2 = String.take 2 digits
    prefix1 = String.take 1 digits
    prefix4 = String.take 4 digits
  in
    if prefix1 == "4" 
      then Visa
    else if prefix2 >= "51" && prefix2 <= "55"
      then Mastercard
    else if prefix2 == "34" || prefix2 == "37"
      then Amex
    else if prefix2 == "65" || prefix4 == "6011"
      then Discover
    else if prefix2 == "36" || prefix2 == "38" || (prefix2 >= "300" && prefix2 <= "305")
      then DinersClub
    else if prefix2 == "35"
      then JCB
    else if prefix2 == "62"
      then UnionPay
    else Unknown

-- | Get card number length for card type
cardNumberLength :: CardType -> Int
cardNumberLength = case _ of
  Amex -> 15
  DinersClub -> 14
  _ -> 16

-- | Get CVV length for card type
cvvLength :: CardType -> Int
cvvLength = case _ of
  Amex -> 4
  _ -> 3

-- | Format card number with spaces
formatCardNumber :: String -> CardType -> String
formatCardNumber num cardType =
  let
    digits = String.replaceAll (Pattern " ") (String.Replacement "") num
  in case cardType of
    Amex -> formatAmex digits
    _ -> formatStandard digits

-- | Format standard card (4-4-4-4)
formatStandard :: String -> String
formatStandard digits =
  let
    groups = 
      [ String.take 4 digits
      , String.take 4 (String.drop 4 digits)
      , String.take 4 (String.drop 8 digits)
      , String.take 4 (String.drop 12 digits)
      ]
  in String.joinWith " " (filter (\s -> String.length s > 0) groups)

-- | Format Amex card (4-6-5)
formatAmex :: String -> String
formatAmex digits =
  let
    groups =
      [ String.take 4 digits
      , String.take 6 (String.drop 4 digits)
      , String.take 5 (String.drop 10 digits)
      ]
  in String.joinWith " " (filter (\s -> String.length s > 0) groups)

-- | Luhn algorithm validation
luhnCheck :: String -> Boolean
luhnCheck numStr =
  let
    digits = String.replaceAll (Pattern " ") (String.Replacement "") numStr
    len = String.length digits
  in if len < 13 || len > 19
       then false
       else luhnCheckImpl digits

-- Foreign implementation for Luhn check
foreign import luhnCheckImpl :: String -> Boolean

-- | Validate card number
validateCardNumber :: String -> Boolean
validateCardNumber num =
  let
    digits = String.replaceAll (Pattern " ") (String.Replacement "") num
    cardType = detectCardType digits
    expectedLength = cardNumberLength cardType
  in String.length digits == expectedLength && luhnCheck digits

-- | Validate expiry date
validateExpiry :: String -> Boolean
validateExpiry expiry =
  case String.split (Pattern "/") expiry of
    [monthStr, yearStr] ->
      case { m: fromString monthStr, y: fromString yearStr } of
        { m: Just month, y: Just year } ->
          month >= 1 && month <= 12 && year >= 0 && year <= 99
        _ -> false
    _ -> false

-- | Validate CVV
validateCvv :: String -> CardType -> Boolean
validateCvv cvvStr cardType =
  let
    len = String.length cvvStr
    expectedLen = cvvLength cardType
  in len == expectedLen && isAllDigits cvvStr

-- | Check if string is all digits
isAllDigits :: String -> Boolean
isAllDigits str = 
  let digits = String.replaceAll (Pattern " ") (String.Replacement "") str
  in String.length digits > 0 && digitsOnlyCheck digits

foreign import digitsOnlyCheck :: String -> Boolean

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Main credit card input component
creditCard :: forall w i. Array (CreditCardProp i) -> HH.HTML w i
creditCard propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    cardType = detectCardType props.cardNumber
  in
    HH.div
      [ cls [ "space-y-4", props.className ] ]
      [ -- Card number
        cardNumberInput props cardType
        -- Expiry and CVV row
      , HH.div
          [ cls [ "flex gap-4" ] ]
          [ HH.div
              [ cls [ "flex-1" ] ]
              [ expiryInput props ]
          , HH.div
              [ cls [ "w-24" ] ]
              [ cvvInput props cardType ]
          ]
        -- Cardholder name (optional)
      , if props.showCardholderName
          then cardholderInput props
          else HH.text ""
      ]

-- | Credit card with visual preview
creditCardWithPreview :: forall w i. Array (CreditCardProp i) -> HH.HTML w i
creditCardWithPreview propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    cardType = detectCardType props.cardNumber
  in
    HH.div
      [ cls [ "space-y-6", props.className ] ]
      [ -- Visual card preview
        cardPreview props cardType
        -- Input fields
      , creditCard propMods
      ]

-- | Card number input
cardNumberInput :: forall w i. CreditCardProps i -> CardType -> HH.HTML w i
cardNumberInput props cardType =
  let
    formattedNumber = formatCardNumber props.cardNumber cardType
    hasError = case props.errors.cardNumber of
      Just _ -> true
      Nothing -> false
  in
    HH.div
      [ cls [ "space-y-1.5" ] ]
      [ HH.label
          [ cls [ "text-sm font-medium" ] ]
          [ HH.text "Card Number" ]
      , HH.div
          [ cls [ "relative" ] ]
          [ HH.input
              [ cls 
                  [ "w-full h-10 pl-10 pr-12 rounded-md border text-sm"
                  , "focus:outline-none focus:ring-2 focus:ring-ring focus:ring-offset-2"
                  , if hasError then "border-destructive" else "border-input"
                  , if props.disabled then "opacity-50 cursor-not-allowed bg-muted" else "bg-background"
                  ]
              , HP.type_ HP.InputText
              , HP.value formattedNumber
              , HP.placeholder "1234 5678 9012 3456"
              , HP.disabled props.disabled
              , HP.attr (HH.AttrName "inputmode") "numeric"
              , HP.attr (HH.AttrName "autocomplete") "cc-number"
              , HP.attr (HH.AttrName "maxlength") "19"
              , ARIA.label "Card number"
              ]
            -- Card type icon
          , HH.div
              [ cls [ "absolute left-3 top-1/2 -translate-y-1/2" ] ]
              [ cardTypeIcon cardType ]
            -- Card logo
          , HH.div
              [ cls [ "absolute right-3 top-1/2 -translate-y-1/2" ] ]
              [ cardBrandLogo cardType ]
          ]
      , case props.errors.cardNumber of
          Just msg -> 
            HH.div [ cls [ "text-sm text-destructive" ] ] [ HH.text msg ]
          Nothing -> HH.text ""
      ]

-- | Expiry date input
expiryInput :: forall w i. CreditCardProps i -> HH.HTML w i
expiryInput props =
  let
    hasError = case props.errors.expiry of
      Just _ -> true
      Nothing -> false
  in
    HH.div
      [ cls [ "space-y-1.5" ] ]
      [ HH.label
          [ cls [ "text-sm font-medium" ] ]
          [ HH.text "Expiry Date" ]
      , HH.input
          [ cls 
              [ "w-full h-10 px-3 rounded-md border text-sm"
              , "focus:outline-none focus:ring-2 focus:ring-ring focus:ring-offset-2"
              , if hasError then "border-destructive" else "border-input"
              , if props.disabled then "opacity-50 cursor-not-allowed bg-muted" else "bg-background"
              ]
          , HP.type_ HP.InputText
          , HP.value props.expiryDate
          , HP.placeholder "MM/YY"
          , HP.disabled props.disabled
          , HP.attr (HH.AttrName "inputmode") "numeric"
          , HP.attr (HH.AttrName "autocomplete") "cc-exp"
          , HP.attr (HH.AttrName "maxlength") "5"
          , ARIA.label "Expiry date"
          ]
      , case props.errors.expiry of
          Just msg -> 
            HH.div [ cls [ "text-sm text-destructive" ] ] [ HH.text msg ]
          Nothing -> HH.text ""
      ]

-- | CVV input
cvvInput :: forall w i. CreditCardProps i -> CardType -> HH.HTML w i
cvvInput props cardType =
  let
    hasError = case props.errors.cvv of
      Just _ -> true
      Nothing -> false
    maxLen = show (cvvLength cardType)
    placeholder = if cardType == Amex then "1234" else "123"
  in
    HH.div
      [ cls [ "space-y-1.5" ] ]
      [ HH.label
          [ cls [ "text-sm font-medium" ] ]
          [ HH.text "CVV" ]
      , HH.div
          [ cls [ "relative" ] ]
          [ HH.input
              [ cls 
                  [ "w-full h-10 px-3 rounded-md border text-sm"
                  , "focus:outline-none focus:ring-2 focus:ring-ring focus:ring-offset-2"
                  , if hasError then "border-destructive" else "border-input"
                  , if props.disabled then "opacity-50 cursor-not-allowed bg-muted" else "bg-background"
                  ]
              , HP.type_ HP.InputPassword
              , HP.value props.cvv
              , HP.placeholder placeholder
              , HP.disabled props.disabled
              , HP.attr (HH.AttrName "inputmode") "numeric"
              , HP.attr (HH.AttrName "autocomplete") "cc-csc"
              , HP.attr (HH.AttrName "maxlength") maxLen
              , ARIA.label "Security code"
              ]
            -- CVV help icon
          , HH.button
              [ cls [ "absolute right-2 top-1/2 -translate-y-1/2 text-muted-foreground hover:text-foreground" ]
              , HP.type_ HP.ButtonButton
              , ARIA.label "What is CVV?"
              ]
              [ questionIcon ]
          ]
      , case props.errors.cvv of
          Just msg -> 
            HH.div [ cls [ "text-sm text-destructive" ] ] [ HH.text msg ]
          Nothing -> HH.text ""
      ]

-- | Cardholder name input
cardholderInput :: forall w i. CreditCardProps i -> HH.HTML w i
cardholderInput props =
  let
    hasError = case props.errors.cardholder of
      Just _ -> true
      Nothing -> false
  in
    HH.div
      [ cls [ "space-y-1.5" ] ]
      [ HH.label
          [ cls [ "text-sm font-medium" ] ]
          [ HH.text "Cardholder Name" ]
      , HH.input
          [ cls 
              [ "w-full h-10 px-3 rounded-md border text-sm"
              , "focus:outline-none focus:ring-2 focus:ring-ring focus:ring-offset-2"
              , if hasError then "border-destructive" else "border-input"
              , if props.disabled then "opacity-50 cursor-not-allowed bg-muted" else "bg-background"
              ]
          , HP.type_ HP.InputText
          , HP.value props.cardholderName
          , HP.placeholder "John Doe"
          , HP.disabled props.disabled
          , HP.attr (HH.AttrName "autocomplete") "cc-name"
          , ARIA.label "Cardholder name"
          ]
      , case props.errors.cardholder of
          Just msg -> 
            HH.div [ cls [ "text-sm text-destructive" ] ] [ HH.text msg ]
          Nothing -> HH.text ""
      ]

-- | Visual card preview
cardPreview :: forall w i. CreditCardProps i -> CardType -> HH.HTML w i
cardPreview props cardType =
  let
    formattedNumber = formatCardNumber props.cardNumber cardType
    displayNumber = if String.length formattedNumber > 0
                      then formattedNumber
                      else "•••• •••• •••• ••••"
    displayExpiry = if String.length props.expiryDate > 0
                      then props.expiryDate
                      else "MM/YY"
    displayName = if String.length props.cardholderName > 0
                    then String.toUpper props.cardholderName
                    else "YOUR NAME"
    isCvvFocused = props.focusedField == Cvv
    
    -- Card gradient based on type
    cardGradient = case cardType of
      Visa -> "from-blue-600 to-blue-800"
      Mastercard -> "from-red-500 to-orange-500"
      Amex -> "from-gray-700 to-gray-900"
      Discover -> "from-orange-400 to-orange-600"
      _ -> "from-gray-600 to-gray-800"
  in
    HH.div
      [ cls [ "perspective-1000" ] ]
      [ HH.div
          [ cls 
              [ "relative w-80 h-48 rounded-xl shadow-xl transition-transform duration-500"
              , if isCvvFocused then "rotate-y-180" else ""
              ]
          , HP.attr (HH.AttrName "style") "transform-style: preserve-3d"
          ]
          [ -- Card front
            HH.div
              [ cls 
                  [ "absolute inset-0 rounded-xl p-6 text-white bg-gradient-to-br backface-hidden"
                  , cardGradient
                  ]
              ]
              [ -- Chip
                HH.div
                  [ cls [ "w-12 h-9 rounded bg-yellow-300/80 mb-6" ] ]
                  []
                -- Card number
              , HH.div
                  [ cls [ "text-xl tracking-widest font-mono mb-4" ] ]
                  [ HH.text displayNumber ]
                -- Bottom row
              , HH.div
                  [ cls [ "flex justify-between items-end" ] ]
                  [ HH.div_
                      [ HH.div
                          [ cls [ "text-xs text-white/70" ] ]
                          [ HH.text "CARD HOLDER" ]
                      , HH.div
                          [ cls [ "text-sm font-medium tracking-wide" ] ]
                          [ HH.text displayName ]
                      ]
                  , HH.div_
                      [ HH.div
                          [ cls [ "text-xs text-white/70" ] ]
                          [ HH.text "EXPIRES" ]
                      , HH.div
                          [ cls [ "text-sm font-medium" ] ]
                          [ HH.text displayExpiry ]
                      ]
                  , cardBrandLogoLarge cardType
                  ]
              ]
            -- Card back
          , HH.div
              [ cls 
                  [ "absolute inset-0 rounded-xl bg-gradient-to-br backface-hidden rotate-y-180"
                  , cardGradient
                  ]
              ]
              [ -- Magnetic stripe
                HH.div
                  [ cls [ "w-full h-12 bg-black mt-6" ] ]
                  []
                -- CVV area
              , HH.div
                  [ cls [ "px-6 mt-6" ] ]
                  [ HH.div
                      [ cls [ "text-xs text-white/70 mb-1" ] ]
                      [ HH.text "CVV" ]
                  , HH.div
                      [ cls [ "bg-white/90 rounded px-3 py-2 text-right font-mono text-gray-800" ] ]
                      [ HH.text (if String.length props.cvv > 0 then props.cvv else "•••") ]
                  ]
              ]
          ]
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // icons
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Card type icon (generic card)
cardTypeIcon :: forall w i. CardType -> HH.HTML w i
cardTypeIcon _ =
  HH.element (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "width") "20"
    , HP.attr (HH.AttrName "height") "20"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , cls [ "text-muted-foreground" ]
    ]
    [ HH.element (HH.ElemName "rect")
        [ HP.attr (HH.AttrName "width") "20"
        , HP.attr (HH.AttrName "height") "14"
        , HP.attr (HH.AttrName "x") "2"
        , HP.attr (HH.AttrName "y") "5"
        , HP.attr (HH.AttrName "rx") "2"
        ]
        []
    , HH.element (HH.ElemName "line")
        [ HP.attr (HH.AttrName "x1") "2"
        , HP.attr (HH.AttrName "y1") "10"
        , HP.attr (HH.AttrName "x2") "22"
        , HP.attr (HH.AttrName "y2") "10"
        ]
        []
    ]

-- | Card brand logo (small)
cardBrandLogo :: forall w i. CardType -> HH.HTML w i
cardBrandLogo cardType =
  HH.span
    [ cls [ "text-sm font-bold text-muted-foreground" ] ]
    [ HH.text (cardTypeName cardType) ]

-- | Card brand logo (large for preview)
cardBrandLogoLarge :: forall w i. CardType -> HH.HTML w i
cardBrandLogoLarge cardType =
  HH.span
    [ cls [ "text-xl font-bold text-white/90" ] ]
    [ HH.text (cardTypeName cardType) ]

-- | Get card type name
cardTypeName :: CardType -> String
cardTypeName = case _ of
  Visa -> "VISA"
  Mastercard -> "MC"
  Amex -> "AMEX"
  Discover -> "DISCOVER"
  DinersClub -> "DINERS"
  JCB -> "JCB"
  UnionPay -> "UNIONPAY"
  Unknown -> ""

-- | Question mark icon
questionIcon :: forall w i. HH.HTML w i
questionIcon =
  HH.element (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "width") "16"
    , HP.attr (HH.AttrName "height") "16"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    ]
    [ HH.element (HH.ElemName "circle")
        [ HP.attr (HH.AttrName "cx") "12"
        , HP.attr (HH.AttrName "cy") "12"
        , HP.attr (HH.AttrName "r") "10"
        ]
        []
    , HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M9.09 9a3 3 0 0 1 5.83 1c0 2-3 3-3 3" ]
        []
    , HH.element (HH.ElemName "line")
        [ HP.attr (HH.AttrName "x1") "12"
        , HP.attr (HH.AttrName "y1") "17"
        , HP.attr (HH.AttrName "x2") "12.01"
        , HP.attr (HH.AttrName "y2") "17"
        ]
        []
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Filter function for arrays
filter :: forall a. (a -> Boolean) -> Array a -> Array a
filter f xs = filterImpl f xs

foreign import filterImpl :: forall a. (a -> Boolean) -> Array a -> Array a
