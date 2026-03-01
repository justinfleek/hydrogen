-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                    // hydrogen // element // compound // auto-complete // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | AutoComplete Types — Core data structures for the autocomplete component.
-- |
-- | This module defines:
-- | - `Suggestion` — A suggestion item with value, label, and disabled state
-- | - `AutoCompleteProps` — Full property record with Schema atoms
-- | - `AutoCompleteProp` — Property modifier function type
-- | - `defaultProps` — Default property values (all atoms `Nothing`)

module Hydrogen.Element.Compound.AutoComplete.Types
  ( -- * Suggestion Type
    Suggestion
  , mkSuggestion
  , suggestionWithLabel
  
  -- * Props Type
  , AutoCompleteProps
  , AutoCompleteProp
  , defaultProps
  ) where

import Data.Maybe (Maybe(Nothing))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Typography.FontSize as FontSize

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // suggestion types
-- ═════════════════════════════════════════════════════════════════════════════

-- | A suggestion with value, label, and disabled flag
type Suggestion =
  { value :: String
  , label :: String
  , disabled :: Boolean
  }

-- | Create a simple string suggestion
mkSuggestion :: String -> Suggestion
mkSuggestion s = { value: s, label: s, disabled: false }

-- | Create a suggestion with custom label
suggestionWithLabel :: String -> String -> Suggestion
suggestionWithLabel val lbl = { value: val, label: lbl, disabled: false }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | AutoComplete properties
-- |
-- | All visual properties accept concrete Schema atoms.
-- | `Maybe` indicates optional — `Nothing` means no style is emitted,
-- | allowing inheritance from parent/context/brand.
type AutoCompleteProps msg =
  { -- Content
    suggestions :: Array Suggestion
  , value :: String
  , placeholder :: String
  , disabled :: Boolean
  , loading :: Boolean
  , open :: Maybe Boolean
  , highlightedIndex :: Int
  , minChars :: Int
  , maxSuggestions :: Int
  , clearOnSelect :: Boolean
  , noResultsText :: String
  , loadingText :: String
  , id :: Maybe String
  , name :: Maybe String
  
  -- Color atoms - Input
  , inputBackgroundColor :: Maybe Color.RGB
  , inputTextColor :: Maybe Color.RGB
  , inputBorderColor :: Maybe Color.RGB
  , inputPlaceholderColor :: Maybe Color.RGB
  , inputFocusBorderColor :: Maybe Color.RGB
  
  -- Color atoms - Dropdown
  , dropdownBackgroundColor :: Maybe Color.RGB
  , dropdownBorderColor :: Maybe Color.RGB
  
  -- Color atoms - Items
  , itemTextColor :: Maybe Color.RGB
  , itemHighlightBgColor :: Maybe Color.RGB
  , itemHighlightTextColor :: Maybe Color.RGB
  , loadingTextColor :: Maybe Color.RGB
  , noResultsTextColor :: Maybe Color.RGB
  
  -- Geometry atoms
  , inputBorderRadius :: Maybe Geometry.Corners
  , dropdownBorderRadius :: Maybe Geometry.Corners
  , inputBorderWidth :: Maybe Device.Pixel
  , dropdownBorderWidth :: Maybe Device.Pixel
  
  -- Dimension atoms
  , inputHeight :: Maybe Device.Pixel
  , inputPaddingX :: Maybe Device.Pixel
  , inputPaddingY :: Maybe Device.Pixel
  , dropdownMaxHeight :: Maybe Device.Pixel
  , itemPaddingX :: Maybe Device.Pixel
  , itemPaddingY :: Maybe Device.Pixel
  
  -- Typography atoms
  , inputFontSize :: Maybe FontSize.FontSize
  , itemFontSize :: Maybe FontSize.FontSize
  
  -- Behavior
  , onInput :: Maybe (String -> msg)
  , onSelect :: Maybe (String -> msg)
  , onOpenChange :: Maybe (Boolean -> msg)
  , onHighlightChange :: Maybe (Int -> msg)
  , onFocus :: Maybe msg
  , onBlur :: Maybe msg
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier
type AutoCompleteProp msg = AutoCompleteProps msg -> AutoCompleteProps msg

-- | Default properties
-- |
-- | Visual atoms default to `Nothing` (no style emitted, inherit from context).
-- | This ensures the component works with any BrandSchema.
defaultProps :: forall msg. AutoCompleteProps msg
defaultProps =
  { suggestions: []
  , value: ""
  , placeholder: "Search..."
  , disabled: false
  , loading: false
  , open: Nothing
  , highlightedIndex: 0
  , minChars: 1
  , maxSuggestions: 10
  , clearOnSelect: false
  , noResultsText: "No results found"
  , loadingText: "Loading..."
  , id: Nothing
  , name: Nothing
  , inputBackgroundColor: Nothing
  , inputTextColor: Nothing
  , inputBorderColor: Nothing
  , inputPlaceholderColor: Nothing
  , inputFocusBorderColor: Nothing
  , dropdownBackgroundColor: Nothing
  , dropdownBorderColor: Nothing
  , itemTextColor: Nothing
  , itemHighlightBgColor: Nothing
  , itemHighlightTextColor: Nothing
  , loadingTextColor: Nothing
  , noResultsTextColor: Nothing
  , inputBorderRadius: Nothing
  , dropdownBorderRadius: Nothing
  , inputBorderWidth: Nothing
  , dropdownBorderWidth: Nothing
  , inputHeight: Nothing
  , inputPaddingX: Nothing
  , inputPaddingY: Nothing
  , dropdownMaxHeight: Nothing
  , itemPaddingX: Nothing
  , itemPaddingY: Nothing
  , inputFontSize: Nothing
  , itemFontSize: Nothing
  , onInput: Nothing
  , onSelect: Nothing
  , onOpenChange: Nothing
  , onHighlightChange: Nothing
  , onFocus: Nothing
  , onBlur: Nothing
  , extraAttributes: []
  }
