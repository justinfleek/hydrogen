-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                     // hydrogen // phoneinput
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | International phone number input component
-- |
-- | Phone input with country selector, formatting, and validation.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.PhoneInput as PhoneInput
-- |
-- | -- Basic phone input
-- | PhoneInput.phoneInput
-- |   [ PhoneInput.value { country: "US", number: "555-123-4567" }
-- |   , PhoneInput.onChange HandlePhoneChange
-- |   ]
-- |
-- | -- With default country
-- | PhoneInput.phoneInput
-- |   [ PhoneInput.defaultCountry "GB"
-- |   , PhoneInput.onChange HandlePhoneChange
-- |   ]
-- |
-- | -- With favorite countries
-- | PhoneInput.phoneInput
-- |   [ PhoneInput.favoriteCountries ["US", "CA", "GB"]
-- |   , PhoneInput.searchable true
-- |   ]
-- |
-- | -- With validation
-- | PhoneInput.phoneInput
-- |   [ PhoneInput.value phoneValue
-- |   , PhoneInput.error (not phoneValue.isValid)
-- |   , PhoneInput.errorMessage "Please enter a valid phone number"
-- |   ]
-- | ```
module Hydrogen.Component.PhoneInput
  ( -- * Phone Input Components
    phoneInput
  , countrySelector
  , phoneNumberInput
    -- * Props
  , PhoneInputProps
  , PhoneInputProp
  , defaultProps
    -- * Prop Builders
  , value
  , defaultCountry
  , favoriteCountries
  , excludeCountries
  , onlyCountries
  , searchable
  , disabled
  , error
  , errorMessage
  , placeholder
  , autoDetectCountry
  , className
  , onChange
  , onCountryChange
  , onValidate
    -- * Types
  , PhoneValue
  , Country
  , CountryCode
    -- * Country Data
  , countries
  , getCountry
  , getCountryFlag
  , formatPhoneNumber
  , validatePhoneNumber
    -- * FFI
  , PhoneInputElement
  ) where

import Prelude

import Data.Array (foldl, filter, find, sortBy)
import Data.Maybe (Maybe(Nothing, Just), fromMaybe)
import Data.String as String
import Data.String.Pattern (Pattern(Pattern))
import Effect (Effect)
import Effect.Uncurried (EffectFn1, EffectFn2)
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)
import Web.DOM.Element (Element)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Country code (ISO 3166-1 alpha-2)
type CountryCode = String

-- | Country information
type Country =
  { code :: CountryCode
  , name :: String
  , dialCode :: String
  , flag :: String
  , format :: String  -- Phone number format pattern
  , example :: String -- Example phone number
  }

-- | Phone value with country and number
type PhoneValue =
  { country :: CountryCode
  , number :: String
  , formatted :: String
  , isValid :: Boolean
  , e164 :: String  -- E.164 format
  }

-- | Opaque phone input element type
foreign import data PhoneInputElement :: Type

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Initialize phone input formatting
foreign import initPhoneInputImpl :: EffectFn2 Element (PhoneValue -> Effect Unit) PhoneInputElement

-- | Format phone number for display
foreign import formatPhoneNumberImpl :: String -> CountryCode -> String

-- | Validate phone number
foreign import validatePhoneNumberImpl :: String -> CountryCode -> Boolean

-- | Auto-detect country from IP
foreign import detectCountryImpl :: EffectFn1 (CountryCode -> Effect Unit) Unit

-- | Cleanup phone input
foreign import destroyPhoneInputImpl :: EffectFn1 PhoneInputElement Unit

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

type PhoneInputProps i =
  { value :: PhoneValue
  , defaultCountry :: CountryCode
  , favoriteCountries :: Array CountryCode
  , excludeCountries :: Array CountryCode
  , onlyCountries :: Array CountryCode
  , searchable :: Boolean
  , disabled :: Boolean
  , error :: Boolean
  , errorMessage :: Maybe String
  , placeholder :: Maybe String
  , autoDetectCountry :: Boolean
  , isOpen :: Boolean
  , searchQuery :: String
  , className :: String
  , onChange :: Maybe (PhoneValue -> i)
  , onCountryChange :: Maybe (CountryCode -> i)
  , onValidate :: Maybe (Boolean -> i)
  , onOpenChange :: Maybe (Boolean -> i)
  }

type PhoneInputProp i = PhoneInputProps i -> PhoneInputProps i

defaultProps :: forall i. PhoneInputProps i
defaultProps =
  { value: { country: "US", number: "", formatted: "", isValid: false, e164: "" }
  , defaultCountry: "US"
  , favoriteCountries: []
  , excludeCountries: []
  , onlyCountries: []
  , searchable: true
  , disabled: false
  , error: false
  , errorMessage: Nothing
  , placeholder: Nothing
  , autoDetectCountry: false
  , isOpen: false
  , searchQuery: ""
  , className: ""
  , onChange: Nothing
  , onCountryChange: Nothing
  , onValidate: Nothing
  , onOpenChange: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set phone value
value :: forall i. PhoneValue -> PhoneInputProp i
value v props = props { value = v }

-- | Set default country
defaultCountry :: forall i. CountryCode -> PhoneInputProp i
defaultCountry c props = props { defaultCountry = c }

-- | Set favorite countries (shown at top)
favoriteCountries :: forall i. Array CountryCode -> PhoneInputProp i
favoriteCountries cs props = props { favoriteCountries = cs }

-- | Set countries to exclude
excludeCountries :: forall i. Array CountryCode -> PhoneInputProp i
excludeCountries cs props = props { excludeCountries = cs }

-- | Set allowed countries only
onlyCountries :: forall i. Array CountryCode -> PhoneInputProp i
onlyCountries cs props = props { onlyCountries = cs }

-- | Enable country search
searchable :: forall i. Boolean -> PhoneInputProp i
searchable s props = props { searchable = s }

-- | Set disabled state
disabled :: forall i. Boolean -> PhoneInputProp i
disabled d props = props { disabled = d }

-- | Set error state
error :: forall i. Boolean -> PhoneInputProp i
error e props = props { error = e }

-- | Set error message
errorMessage :: forall i. String -> PhoneInputProp i
errorMessage m props = props { errorMessage = Just m }

-- | Set placeholder text
placeholder :: forall i. String -> PhoneInputProp i
placeholder p props = props { placeholder = Just p }

-- | Enable auto-detect country from IP
autoDetectCountry :: forall i. Boolean -> PhoneInputProp i
autoDetectCountry a props = props { autoDetectCountry = a }

-- | Add custom class
className :: forall i. String -> PhoneInputProp i
className c props = props { className = props.className <> " " <> c }

-- | Set change handler
onChange :: forall i. (PhoneValue -> i) -> PhoneInputProp i
onChange handler props = props { onChange = Just handler }

-- | Set country change handler
onCountryChange :: forall i. (CountryCode -> i) -> PhoneInputProp i
onCountryChange handler props = props { onCountryChange = Just handler }

-- | Set validation handler
onValidate :: forall i. (Boolean -> i) -> PhoneInputProp i
onValidate handler props = props { onValidate = Just handler }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // country data
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Common countries list
countries :: Array Country
countries =
  [ { code: "US", name: "United States", dialCode: "+1", flag: "🇺🇸", format: "(###) ###-####", example: "(555) 123-4567" }
  , { code: "GB", name: "United Kingdom", dialCode: "+44", flag: "🇬🇧", format: "#### ### ####", example: "7911 123456" }
  , { code: "CA", name: "Canada", dialCode: "+1", flag: "🇨🇦", format: "(###) ###-####", example: "(555) 123-4567" }
  , { code: "AU", name: "Australia", dialCode: "+61", flag: "🇦🇺", format: "#### ### ###", example: "0412 345 678" }
  , { code: "DE", name: "Germany", dialCode: "+49", flag: "🇩🇪", format: "### #######", example: "151 12345678" }
  , { code: "FR", name: "France", dialCode: "+33", flag: "🇫🇷", format: "## ## ## ## ##", example: "06 12 34 56 78" }
  , { code: "IT", name: "Italy", dialCode: "+39", flag: "🇮🇹", format: "### ### ####", example: "312 345 6789" }
  , { code: "ES", name: "Spain", dialCode: "+34", flag: "🇪🇸", format: "### ### ###", example: "612 345 678" }
  , { code: "NL", name: "Netherlands", dialCode: "+31", flag: "🇳🇱", format: "## ########", example: "06 12345678" }
  , { code: "BE", name: "Belgium", dialCode: "+32", flag: "🇧🇪", format: "### ## ## ##", example: "470 12 34 56" }
  , { code: "CH", name: "Switzerland", dialCode: "+41", flag: "🇨🇭", format: "## ### ## ##", example: "78 123 45 67" }
  , { code: "AT", name: "Austria", dialCode: "+43", flag: "🇦🇹", format: "### #######", example: "664 1234567" }
  , { code: "SE", name: "Sweden", dialCode: "+46", flag: "🇸🇪", format: "##-### ## ##", example: "70-123 45 67" }
  , { code: "NO", name: "Norway", dialCode: "+47", flag: "🇳🇴", format: "### ## ###", example: "406 12 345" }
  , { code: "DK", name: "Denmark", dialCode: "+45", flag: "🇩🇰", format: "## ## ## ##", example: "32 12 34 56" }
  , { code: "FI", name: "Finland", dialCode: "+358", flag: "🇫🇮", format: "## ### ####", example: "41 234 5678" }
  , { code: "IE", name: "Ireland", dialCode: "+353", flag: "🇮🇪", format: "## ### ####", example: "85 123 4567" }
  , { code: "PT", name: "Portugal", dialCode: "+351", flag: "🇵🇹", format: "### ### ###", example: "912 345 678" }
  , { code: "PL", name: "Poland", dialCode: "+48", flag: "🇵🇱", format: "### ### ###", example: "512 345 678" }
  , { code: "CZ", name: "Czech Republic", dialCode: "+420", flag: "🇨🇿", format: "### ### ###", example: "601 123 456" }
  , { code: "JP", name: "Japan", dialCode: "+81", flag: "🇯🇵", format: "##-####-####", example: "90-1234-5678" }
  , { code: "CN", name: "China", dialCode: "+86", flag: "🇨🇳", format: "### #### ####", example: "131 2345 6789" }
  , { code: "KR", name: "South Korea", dialCode: "+82", flag: "🇰🇷", format: "##-####-####", example: "10-1234-5678" }
  , { code: "IN", name: "India", dialCode: "+91", flag: "🇮🇳", format: "#####-#####", example: "98765-43210" }
  , { code: "BR", name: "Brazil", dialCode: "+55", flag: "🇧🇷", format: "(##) #####-####", example: "(11) 91234-5678" }
  , { code: "MX", name: "Mexico", dialCode: "+52", flag: "🇲🇽", format: "## #### ####", example: "55 1234 5678" }
  , { code: "AR", name: "Argentina", dialCode: "+54", flag: "🇦🇷", format: "## ####-####", example: "11 1234-5678" }
  , { code: "ZA", name: "South Africa", dialCode: "+27", flag: "🇿🇦", format: "## ### ####", example: "71 123 4567" }
  , { code: "RU", name: "Russia", dialCode: "+7", flag: "🇷🇺", format: "### ###-##-##", example: "912 345-67-89" }
  , { code: "AE", name: "United Arab Emirates", dialCode: "+971", flag: "🇦🇪", format: "## ### ####", example: "50 123 4567" }
  , { code: "SG", name: "Singapore", dialCode: "+65", flag: "🇸🇬", format: "#### ####", example: "8123 4567" }
  , { code: "HK", name: "Hong Kong", dialCode: "+852", flag: "🇭🇰", format: "#### ####", example: "5123 4567" }
  , { code: "NZ", name: "New Zealand", dialCode: "+64", flag: "🇳🇿", format: "## ### ####", example: "21 123 4567" }
  ]

-- | Get country by code
getCountry :: CountryCode -> Maybe Country
getCountry code = find (\c -> c.code == code) countries

-- | Get country flag emoji
getCountryFlag :: CountryCode -> String
getCountryFlag code = case getCountry code of
  Just country -> country.flag
  Nothing -> "🏳️"

-- | Format phone number for display
formatPhoneNumber :: String -> CountryCode -> String
formatPhoneNumber = formatPhoneNumberImpl

-- | Validate phone number
validatePhoneNumber :: String -> CountryCode -> Boolean
validatePhoneNumber = validatePhoneNumberImpl

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Main phone input component
phoneInput :: forall w i. Array (PhoneInputProp i) -> HH.HTML w i
phoneInput propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    currentCountry = fromMaybe defaultUSCountry (getCountry props.value.country)
    
    inputClasses =
      [ "flex-1 h-10 px-3 text-sm rounded-r-md border-y border-r"
      , "focus:outline-none focus:ring-2 focus:ring-ring focus:ring-offset-2"
      , if props.error
          then "border-destructive"
          else "border-input"
      , if props.disabled then "opacity-50 cursor-not-allowed bg-muted" else "bg-background"
      ]
    
    placeholderText = fromMaybe currentCountry.example props.placeholder
  in
    HH.div
      [ cls [ "flex flex-col gap-1", props.className ] ]
      [ HH.div
          [ cls [ "flex" ] ]
          [ -- Country selector
            countrySelector props currentCountry
            -- Phone number input
          , HH.input
              [ cls inputClasses
              , HP.type_ HP.InputTel
              , HP.value props.value.formatted
              , HP.placeholder placeholderText
              , HP.disabled props.disabled
              , HP.attr (HH.AttrName "autocomplete") "tel-national"
              , ARIA.label "Phone number"
              ]
          ]
      , case props.errorMessage of
          Just msg ->
            HH.div
              [ cls [ "text-sm text-destructive" ] ]
              [ HH.text msg ]
          Nothing -> HH.text ""
      ]

-- | Country selector dropdown
countrySelector :: forall w i. PhoneInputProps i -> Country -> HH.HTML w i
countrySelector props currentCountry =
  let
    buttonClasses =
      [ "flex items-center gap-2 h-10 px-3 rounded-l-md border"
      , "focus:outline-none focus:ring-2 focus:ring-ring focus:z-10"
      , if props.error then "border-destructive" else "border-input"
      , if props.disabled then "opacity-50 cursor-not-allowed bg-muted" else "bg-background hover:bg-accent"
      ]
    
    -- Filter and sort countries
    availableCountries = getAvailableCountries props
    favoritesList = filter (\c -> elem c.code props.favoriteCountries) availableCountries
    othersList = filter (\c -> not (elem c.code props.favoriteCountries)) availableCountries
  in
    HH.div
      [ cls [ "relative" ] ]
      [ HH.button
          ( [ cls buttonClasses
            , HP.type_ HP.ButtonButton
            , HP.disabled props.disabled
            , ARIA.hasPopup "listbox"
            , ARIA.expanded (show props.isOpen)
            ] <> case props.onOpenChange of
              Just handler -> [ HE.onClick (\_ -> handler (not props.isOpen)) ]
              Nothing -> []
          )
          [ HH.span [ cls [ "text-xl leading-none" ] ] [ HH.text currentCountry.flag ]
          , HH.span [ cls [ "text-sm text-muted-foreground" ] ] [ HH.text currentCountry.dialCode ]
          , chevronIcon
          ]
      , if props.isOpen
          then countryDropdown props favoritesList othersList
          else HH.text ""
      ]

-- | Country dropdown list
countryDropdown :: forall w i. PhoneInputProps i -> Array Country -> Array Country -> HH.HTML w i
countryDropdown props favorites others =
  HH.div
    [ cls [ "absolute z-50 mt-1 w-72 max-h-60 overflow-auto rounded-md border bg-popover shadow-lg" ]
    , ARIA.role "listbox"
    ]
    [ if props.searchable
        then searchInput props
        else HH.text ""
    , if not (null favorites)
        then
          HH.div_
            [ HH.div
                [ cls [ "px-2 py-1.5 text-xs font-semibold text-muted-foreground" ] ]
                [ HH.text "Favorites" ]
            , HH.div_ (map (countryOption props) favorites)
            , HH.div [ cls [ "h-px bg-border my-1" ] ] []
            ]
        else HH.text ""
    , HH.div_ (map (countryOption props) (filterBySearch props.searchQuery others))
    ]

-- | Search input for countries
searchInput :: forall w i. PhoneInputProps i -> HH.HTML w i
searchInput _ =
  HH.div
    [ cls [ "p-2 border-b" ] ]
    [ HH.input
        [ cls [ "w-full h-8 px-2 text-sm rounded border border-input bg-background focus:outline-none focus:ring-1 focus:ring-ring" ]
        , HP.type_ HP.InputText
        , HP.placeholder "Search countries..."
        , HP.attr (HH.AttrName "data-search-input") "true"
        ]
    ]

-- | Country option in dropdown
countryOption :: forall w i. PhoneInputProps i -> Country -> HH.HTML w i
countryOption props country =
  let
    isSelected = props.value.country == country.code
  in
    HH.div
      ( [ cls 
            [ "flex items-center gap-3 px-3 py-2 cursor-pointer hover:bg-accent"
            , if isSelected then "bg-accent" else ""
            ]
        , ARIA.role "option"
        , ARIA.selected (show isSelected)
        ] <> case props.onCountryChange of
          Just handler -> [ HE.onClick (\_ -> handler country.code) ]
          Nothing -> []
      )
      [ HH.span [ cls [ "text-xl" ] ] [ HH.text country.flag ]
      , HH.span [ cls [ "flex-1 text-sm" ] ] [ HH.text country.name ]
      , HH.span [ cls [ "text-sm text-muted-foreground" ] ] [ HH.text country.dialCode ]
      ]

-- | Phone number input (standalone)
phoneNumberInput :: forall w i. PhoneInputProps i -> HH.HTML w i
phoneNumberInput props =
  let
    currentCountry = fromMaybe defaultUSCountry (getCountry props.value.country)
    placeholderText = fromMaybe currentCountry.example props.placeholder
  in
    HH.input
      [ cls 
          [ "flex h-10 w-full rounded-md border border-input bg-background px-3 py-2 text-sm"
          , "focus:outline-none focus:ring-2 focus:ring-ring focus:ring-offset-2"
          ]
      , HP.type_ HP.InputTel
      , HP.value props.value.formatted
      , HP.placeholder placeholderText
      , HP.disabled props.disabled
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // icons
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Chevron down icon
chevronIcon :: forall w i. HH.HTML w i
chevronIcon =
  HH.element (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "width") "12"
    , HP.attr (HH.AttrName "height") "12"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , cls [ "opacity-50" ]
    ]
    [ HH.element (HH.ElemName "polyline")
        [ HP.attr (HH.AttrName "points") "6 9 12 15 18 9" ]
        []
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Default US country
defaultUSCountry :: Country
defaultUSCountry = 
  { code: "US", name: "United States", dialCode: "+1", flag: "🇺🇸", format: "(###) ###-####", example: "(555) 123-4567" }

-- | Get available countries based on props
getAvailableCountries :: forall i. PhoneInputProps i -> Array Country
getAvailableCountries props =
  let
    filtered = 
      if not (null props.onlyCountries)
        then filter (\c -> elem c.code props.onlyCountries) countries
        else filter (\c -> not (elem c.code props.excludeCountries)) countries
  in
    sortBy (\a b -> compare a.name b.name) filtered

-- | Filter countries by search query
filterBySearch :: String -> Array Country -> Array Country
filterBySearch query cs =
  if String.length query < 1
    then cs
    else filter (matchesSearch (String.toLower query)) cs

-- | Check if country matches search
matchesSearch :: String -> Country -> Boolean
matchesSearch query country =
  String.contains (Pattern query) (String.toLower country.name) ||
  String.contains (Pattern query) (String.toLower country.code) ||
  String.contains (Pattern query) country.dialCode

-- | Null check for arrays
null :: forall a. Array a -> Boolean
null arr = case arr of
  [] -> true
  _ -> false

-- | Check if element is in array
elem :: forall a. Eq a => a -> Array a -> Boolean
elem x xs = case find (_ == x) xs of
  Just _ -> true
  Nothing -> false


