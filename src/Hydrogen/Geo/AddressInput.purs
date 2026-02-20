-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // hydrogen // addressinput
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Address autocomplete component
-- |
-- | A comprehensive address input with autocomplete suggestions, geocoding,
-- | and reverse geocoding. Works with Nominatim (OSM) or pluggable providers.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Geo.AddressInput as Address
-- |
-- | -- Basic address input
-- | Address.addressInput
-- |   [ Address.placeholder "Enter an address..."
-- |   , Address.onSelect \place -> HandleAddressSelect place
-- |   ]
-- |
-- | -- With current location button
-- | Address.addressInput
-- |   [ Address.placeholder "Search location..."
-- |   , Address.showCurrentLocation true
-- |   , Address.onSelect HandleAddressSelect
-- |   , Address.onCurrentLocation HandleCurrentLocation
-- |   ]
-- |
-- | -- With map preview
-- | Address.addressInput
-- |   [ Address.placeholder "Delivery address"
-- |   , Address.showMapPreview true
-- |   , Address.onSelect HandleAddressSelect
-- |   ]
-- |
-- | -- Custom geocoding provider
-- | Address.addressInput
-- |   [ Address.provider myCustomProvider
-- |   , Address.onSelect HandleAddressSelect
-- |   ]
-- |
-- | -- Geocode an address
-- | result <- Address.geocode "1600 Amphitheatre Parkway, Mountain View, CA"
-- | case result of
-- |   Right places -> -- Array of matching places
-- |   Left error -> -- Handle error
-- |
-- | -- Reverse geocode coordinates
-- | result <- Address.reverseGeocode { lat: 37.4224, lng: -122.0842 }
-- | case result of
-- |   Right address -> Console.log address.formatted
-- |   Left error -> -- Handle error
-- | ```
module Hydrogen.Geo.AddressInput
  ( -- * Component
    addressInput
  , AddressInputProps
  , AddressInputProp
  , defaultProps
    -- * Props
  , value
  , placeholder
  , disabled
  , className
  , onSelect
  , onChange
  , onClear
  , onCurrentLocation
  , showCurrentLocation
  , showClearButton
  , showMapPreview
  , debounceMs
  , minChars
  , maxSuggestions
  , recentSearches
  , provider
    -- * Place Types
  , Place
  , Address
  , AddressComponent
  , ComponentType(..)
    -- * Geocoding
  , geocode
  , reverseGeocode
  , GeocodeResult
    -- * Providers
  , GeocodingProvider
  , nominatimProvider
  , createProvider
    -- * Recent Searches
  , getRecentSearches
  , addRecentSearch
  , clearRecentSearches
    -- * Utilities
  , formatAddress
  , getComponent
  , getStreet
  , getCity
  , getState
  , getCountry
  , getPostalCode
  ) where

import Prelude

import Data.Argonaut (Json)
import Data.Array (foldl, filter, find, take)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..), fromMaybe)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Address component types
data ComponentType
  = StreetNumber
  | StreetName
  | Neighborhood
  | City
  | County
  | State
  | Country
  | PostalCode
  | PlusCode
  | Other String

derive instance eqComponentType :: Eq ComponentType

instance showComponentType :: Show ComponentType where
  show StreetNumber = "StreetNumber"
  show StreetName = "StreetName"
  show Neighborhood = "Neighborhood"
  show City = "City"
  show County = "County"
  show State = "State"
  show Country = "Country"
  show PostalCode = "PostalCode"
  show PlusCode = "PlusCode"
  show (Other s) = "Other: " <> s

-- | Individual address component
type AddressComponent =
  { types :: Array ComponentType
  , longName :: String
  , shortName :: String
  }

-- | Structured address
type Address =
  { formatted :: String
  , components :: Array AddressComponent
  , street :: Maybe String
  , city :: Maybe String
  , state :: Maybe String
  , country :: Maybe String
  , postalCode :: Maybe String
  }

-- | Place with coordinates and address
type Place =
  { placeId :: String
  , displayName :: String
  , address :: Address
  , coordinates :: { lat :: Number, lng :: Number }
  , boundingBox :: Maybe { north :: Number, south :: Number, east :: Number, west :: Number }
  , types :: Array String
  }

-- | Geocoding result
type GeocodeResult = Either String (Array Place)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // provider
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Geocoding provider interface
type GeocodingProvider =
  { search :: String -> Aff (Array Place)
  , reverseGeocode :: { lat :: Number, lng :: Number } -> Aff (Maybe Address)
  , getPlaceDetails :: String -> Aff (Maybe Place)
  , name :: String
  }

-- | Nominatim (OpenStreetMap) provider
nominatimProvider :: GeocodingProvider
nominatimProvider =
  { search: nominatimSearch
  , reverseGeocode: nominatimReverse
  , getPlaceDetails: nominatimDetails
  , name: "Nominatim"
  }

foreign import nominatimSearchImpl :: String -> EffectFnAff (Array Place)
foreign import nominatimReverseImpl :: { lat :: Number, lng :: Number } -> EffectFnAff (Maybe Address)
foreign import nominatimDetailsImpl :: String -> EffectFnAff (Maybe Place)

nominatimSearch :: String -> Aff (Array Place)
nominatimSearch query = fromEffectFnAff $ nominatimSearchImpl query

nominatimReverse :: { lat :: Number, lng :: Number } -> Aff (Maybe Address)
nominatimReverse coords = fromEffectFnAff $ nominatimReverseImpl coords

nominatimDetails :: String -> Aff (Maybe Place)
nominatimDetails placeId = fromEffectFnAff $ nominatimDetailsImpl placeId

-- | Create a custom provider
createProvider 
  :: String 
  -> (String -> Aff (Array Place))
  -> ({ lat :: Number, lng :: Number } -> Aff (Maybe Address))
  -> (String -> Aff (Maybe Place))
  -> GeocodingProvider
createProvider name search reverse details =
  { search
  , reverseGeocode: reverse
  , getPlaceDetails: details
  , name
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

type AddressInputProps i =
  { value :: String
  , placeholder :: String
  , disabled :: Boolean
  , className :: String
  , onSelect :: Maybe (Place -> i)
  , onChange :: Maybe (String -> i)
  , onClear :: Maybe i
  , onCurrentLocation :: Maybe ({ lat :: Number, lng :: Number } -> i)
  , showCurrentLocation :: Boolean
  , showClearButton :: Boolean
  , showMapPreview :: Boolean
  , debounceMs :: Int
  , minChars :: Int
  , maxSuggestions :: Int
  , recentSearches :: Array Place
  , provider :: GeocodingProvider
  }

type AddressInputProp i = AddressInputProps i -> AddressInputProps i

defaultProps :: forall i. AddressInputProps i
defaultProps =
  { value: ""
  , placeholder: "Enter address..."
  , disabled: false
  , className: ""
  , onSelect: Nothing
  , onChange: Nothing
  , onClear: Nothing
  , onCurrentLocation: Nothing
  , showCurrentLocation: false
  , showClearButton: true
  , showMapPreview: false
  , debounceMs: 300
  , minChars: 3
  , maxSuggestions: 5
  , recentSearches: []
  , provider: nominatimProvider
  }

-- | Set input value
value :: forall i. String -> AddressInputProp i
value v props = props { value = v }

-- | Set placeholder text
placeholder :: forall i. String -> AddressInputProp i
placeholder p props = props { placeholder = p }

-- | Set disabled state
disabled :: forall i. Boolean -> AddressInputProp i
disabled d props = props { disabled = d }

-- | Add custom class
className :: forall i. String -> AddressInputProp i
className c props = props { className = props.className <> " " <> c }

-- | Handle address selection
onSelect :: forall i. (Place -> i) -> AddressInputProp i
onSelect handler props = props { onSelect = Just handler }

-- | Handle input change
onChange :: forall i. (String -> i) -> AddressInputProp i
onChange handler props = props { onChange = Just handler }

-- | Handle clear
onClear :: forall i. i -> AddressInputProp i
onClear handler props = props { onClear = Just handler }

-- | Handle current location
onCurrentLocation :: forall i. ({ lat :: Number, lng :: Number } -> i) -> AddressInputProp i
onCurrentLocation handler props = props { onCurrentLocation = Just handler }

-- | Show current location button
showCurrentLocation :: forall i. Boolean -> AddressInputProp i
showCurrentLocation s props = props { showCurrentLocation = s }

-- | Show clear button
showClearButton :: forall i. Boolean -> AddressInputProp i
showClearButton s props = props { showClearButton = s }

-- | Show map preview of selected address
showMapPreview :: forall i. Boolean -> AddressInputProp i
showMapPreview s props = props { showMapPreview = s }

-- | Set debounce delay in milliseconds
debounceMs :: forall i. Int -> AddressInputProp i
debounceMs ms props = props { debounceMs = ms }

-- | Set minimum characters before searching
minChars :: forall i. Int -> AddressInputProp i
minChars n props = props { minChars = n }

-- | Set maximum suggestions to show
maxSuggestions :: forall i. Int -> AddressInputProp i
maxSuggestions n props = props { maxSuggestions = n }

-- | Set recent searches
recentSearches :: forall i. Array Place -> AddressInputProp i
recentSearches places props = props { recentSearches = places }

-- | Set geocoding provider
provider :: forall i. GeocodingProvider -> AddressInputProp i
provider p props = props { provider = p }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // component
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Address autocomplete input component
addressInput :: forall w i. Array (AddressInputProp i) -> HH.HTML w i
addressInput propMods =
  let props = foldl (\p f -> f p) defaultProps propMods
  in
    HH.div
      [ cls 
          [ "relative w-full"
          , props.className
          ]
      , HP.attr (HH.AttrName "data-address-input") "true"
      , HP.attr (HH.AttrName "data-debounce") (show props.debounceMs)
      , HP.attr (HH.AttrName "data-min-chars") (show props.minChars)
      , HP.attr (HH.AttrName "data-max-suggestions") (show props.maxSuggestions)
      , HP.attr (HH.AttrName "data-provider") props.provider.name
      ]
      [ -- Input container
        HH.div
          [ cls [ "relative flex items-center" ] ]
          [ -- Search icon
            HH.div
              [ cls [ "absolute left-3 pointer-events-none text-muted-foreground" ] ]
              [ searchIcon ]
          
          -- Input field
          , HH.input
              [ HP.type_ HP.InputText
              , HP.value props.value
              , HP.placeholder props.placeholder
              , HP.disabled props.disabled
              , cls 
                  [ "flex h-10 w-full rounded-md border border-input bg-background"
                  , "pl-10 pr-20 py-2 text-sm ring-offset-background"
                  , "file:border-0 file:bg-transparent file:text-sm file:font-medium"
                  , "placeholder:text-muted-foreground"
                  , "focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2"
                  , "disabled:cursor-not-allowed disabled:opacity-50"
                  ]
              , HP.attr (HH.AttrName "autocomplete") "off"
              , HP.attr (HH.AttrName "data-address-input-field") "true"
              , ARIA.role "combobox"
              , ARIA.expanded "false"
              , ARIA.hasPopup "listbox"
              , ARIA.autoComplete "list"
              ]
          
          -- Action buttons
          , HH.div
              [ cls [ "absolute right-2 flex items-center gap-1" ] ]
              [ -- Current location button
                if props.showCurrentLocation
                then
                  HH.button
                    [ HP.type_ HP.ButtonButton
                    , cls 
                        [ "p-1.5 rounded-md text-muted-foreground hover:text-foreground"
                        , "hover:bg-accent transition-colors"
                        , "focus:outline-none focus:ring-2 focus:ring-ring"
                        ]
                    , HP.attr (HH.AttrName "data-current-location-btn") "true"
                    , HP.title "Use current location"
                    , ARIA.label "Use current location"
                    ]
                    [ locationIcon ]
                else HH.text ""
              
              -- Clear button
              , if props.showClearButton
                then
                  HH.button
                    [ HP.type_ HP.ButtonButton
                    , cls 
                        [ "p-1.5 rounded-md text-muted-foreground hover:text-foreground"
                        , "hover:bg-accent transition-colors"
                        , "focus:outline-none focus:ring-2 focus:ring-ring"
                        , "hidden" -- Shown via JS when value exists
                        ]
                    , HP.attr (HH.AttrName "data-clear-btn") "true"
                    , HP.title "Clear"
                    , ARIA.label "Clear address"
                    ]
                    [ clearIcon ]
                else HH.text ""
              ]
          ]
      
      -- Suggestions dropdown
      , HH.div
          [ cls 
              [ "absolute z-50 w-full mt-1 bg-popover border border-border rounded-md shadow-lg"
              , "overflow-hidden hidden" -- Shown via JS
              ]
          , HP.attr (HH.AttrName "data-suggestions") "true"
          , ARIA.role "listbox"
          ]
          [ -- Loading state
            HH.div
              [ cls [ "p-3 text-center text-muted-foreground hidden" ]
              , HP.attr (HH.AttrName "data-loading") "true"
              ]
              [ HH.text "Searching..." ]
          
          -- Empty state
          , HH.div
              [ cls [ "p-3 text-center text-muted-foreground hidden" ]
              , HP.attr (HH.AttrName "data-empty") "true"
              ]
              [ HH.text "No results found" ]
          
          -- Suggestion list (populated via JS)
          , HH.ul
              [ cls [ "max-h-60 overflow-auto" ]
              , HP.attr (HH.AttrName "data-suggestion-list") "true"
              , ARIA.role "listbox"
              ]
              []
          
          -- Recent searches section
          , if not (null props.recentSearches)
            then
              HH.div
                [ cls [ "border-t border-border hidden" ]
                , HP.attr (HH.AttrName "data-recent-searches") "true"
                ]
                [ HH.div
                    [ cls [ "px-3 py-2 text-xs font-medium text-muted-foreground" ] ]
                    [ HH.text "Recent" ]
                , HH.ul
                    [ cls [ "max-h-40 overflow-auto" ] ]
                    []
                ]
            else HH.text ""
          ]
      
      -- Map preview
      , if props.showMapPreview
        then
          HH.div
            [ cls 
                [ "mt-2 h-32 rounded-md border border-border bg-muted overflow-hidden hidden"
                ]
            , HP.attr (HH.AttrName "data-map-preview") "true"
            ]
            []
        else HH.text ""
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // icons
-- ═══════════════════════════════════════════════════════════════════════════════

searchIcon :: forall w i. HH.HTML w i
searchIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "h-4 w-4" ]
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "stroke-linecap") "round"
        , HP.attr (HH.AttrName "stroke-linejoin") "round"
        , HP.attr (HH.AttrName "stroke-width") "2"
        , HP.attr (HH.AttrName "d") "M21 21l-6-6m2-5a7 7 0 11-14 0 7 7 0 0114 0z"
        ]
        []
    ]

locationIcon :: forall w i. HH.HTML w i
locationIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "h-4 w-4" ]
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "stroke-linecap") "round"
        , HP.attr (HH.AttrName "stroke-linejoin") "round"
        , HP.attr (HH.AttrName "stroke-width") "2"
        , HP.attr (HH.AttrName "d") "M17.657 16.657L13.414 20.9a1.998 1.998 0 01-2.827 0l-4.244-4.243a8 8 0 1111.314 0z"
        ]
        []
    , HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "stroke-linecap") "round"
        , HP.attr (HH.AttrName "stroke-linejoin") "round"
        , HP.attr (HH.AttrName "stroke-width") "2"
        , HP.attr (HH.AttrName "d") "M15 11a3 3 0 11-6 0 3 3 0 016 0z"
        ]
        []
    ]

clearIcon :: forall w i. HH.HTML w i
clearIcon =
  HH.element (HH.ElemName "svg")
    [ cls [ "h-4 w-4" ]
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "stroke-linecap") "round"
        , HP.attr (HH.AttrName "stroke-linejoin") "round"
        , HP.attr (HH.AttrName "stroke-width") "2"
        , HP.attr (HH.AttrName "d") "M6 18L18 6M6 6l12 12"
        ]
        []
    ]

-- Helper for null check
null :: forall a. Array a -> Boolean
null arr = arrayLength arr == 0

foreign import arrayLength :: forall a. Array a -> Int

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // geocoding
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Geocode an address string to coordinates
geocode :: String -> Aff GeocodeResult
geocode = geocodeImpl

foreign import geocodeImplAff :: String -> EffectFnAff GeocodeResult

geocodeImpl :: String -> Aff GeocodeResult
geocodeImpl query = fromEffectFnAff $ geocodeImplAff query

-- | Reverse geocode coordinates to an address
reverseGeocode :: { lat :: Number, lng :: Number } -> Aff (Either String Address)
reverseGeocode = reverseGeocodeImpl

foreign import reverseGeocodeImplAff :: { lat :: Number, lng :: Number } -> EffectFnAff (Either String Address)

reverseGeocodeImpl :: { lat :: Number, lng :: Number } -> Aff (Either String Address)
reverseGeocodeImpl coords = fromEffectFnAff $ reverseGeocodeImplAff coords

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // recent searches
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get recent searches from localStorage
getRecentSearches :: Effect (Array Place)
getRecentSearches = getRecentSearchesImpl

foreign import getRecentSearchesImpl :: Effect (Array Place)

-- | Add a place to recent searches
addRecentSearch :: Place -> Effect Unit
addRecentSearch = addRecentSearchImpl

foreign import addRecentSearchImpl :: Place -> Effect Unit

-- | Clear recent searches
clearRecentSearches :: Effect Unit
clearRecentSearches = clearRecentSearchesImpl

foreign import clearRecentSearchesImpl :: Effect Unit

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // utilities
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Format address for display
formatAddress :: Address -> String
formatAddress = _.formatted

-- | Get address component by type
getComponent :: ComponentType -> Address -> Maybe AddressComponent
getComponent compType addr =
  find (hasType compType) addr.components
  where
  hasType :: ComponentType -> AddressComponent -> Boolean
  hasType t comp = findType t comp.types
  
  findType :: ComponentType -> Array ComponentType -> Boolean
  findType t types = isJust (find (_ == t) types)
  
  isJust :: forall a. Maybe a -> Boolean
  isJust (Just _) = true
  isJust Nothing = false

-- | Get street address
getStreet :: Address -> Maybe String
getStreet = _.street

-- | Get city
getCity :: Address -> Maybe String
getCity = _.city

-- | Get state/province
getState :: Address -> Maybe String
getState = _.state

-- | Get country
getCountry :: Address -> Maybe String
getCountry = _.country

-- | Get postal code
getPostalCode :: Address -> Maybe String
getPostalCode = _.postalCode
