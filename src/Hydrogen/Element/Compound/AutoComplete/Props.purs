-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                    // hydrogen // element // compound // auto-complete // props
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | AutoComplete Props — Property builder functions for the autocomplete.
-- |
-- | This module provides all prop builder functions organized by category:
-- | - Content props (suggestions, value, placeholder, etc.)
-- | - Color atoms (input, dropdown, item colors)
-- | - Geometry atoms (border radius, border width)
-- | - Dimension atoms (height, padding, max-height)
-- | - Typography atoms (font sizes)
-- | - Behavior props (event handlers)
-- | - Escape hatch (extra attributes)

module Hydrogen.Element.Compound.AutoComplete.Props
  ( -- * Content Props
    suggestionStrings
  , suggestionsData
  , acValue
  , placeholder
  , acDisabled
  , acLoading
  , acOpen
  , highlightedIndex
  , minChars
  , maxSuggestions
  , clearOnSelect
  , noResultsText
  , loadingText
  , acId
  , acName
  
  -- * Color Atoms
  , inputBackgroundColor
  , inputTextColor
  , inputBorderColor
  , inputPlaceholderColor
  , inputFocusBorderColor
  , dropdownBackgroundColor
  , dropdownBorderColor
  , itemTextColor
  , itemHighlightBgColor
  , itemHighlightTextColor
  , loadingTextColor
  , noResultsTextColor
  
  -- * Geometry Atoms
  , inputBorderRadius
  , dropdownBorderRadius
  , inputBorderWidth
  , dropdownBorderWidth
  
  -- * Dimension Atoms
  , inputHeight
  , inputPaddingX
  , inputPaddingY
  , dropdownMaxHeight
  , itemPaddingX
  , itemPaddingY
  
  -- * Typography Atoms
  , inputFontSize
  , itemFontSize
  
  -- * Behavior Props
  , onAcInput
  , onSelect
  , onOpenChange
  , onHighlightChange
  , onAcFocus
  , onAcBlur
  
  -- * Escape Hatch
  , extraAttributes
  ) where

import Prelude (map, (<>))

import Data.Maybe (Maybe(Just))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Typography.FontSize as FontSize

import Hydrogen.Element.Compound.AutoComplete.Types
  ( Suggestion
  , AutoCompleteProp
  , mkSuggestion
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // prop builders: content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set suggestions from simple strings
suggestionStrings :: forall msg. Array String -> AutoCompleteProp msg
suggestionStrings strs props = props { suggestions = map mkSuggestion strs }

-- | Set suggestions with full Suggestion data
suggestionsData :: forall msg. Array Suggestion -> AutoCompleteProp msg
suggestionsData sugs props = props { suggestions = sugs }

-- | Set current input value
acValue :: forall msg. String -> AutoCompleteProp msg
acValue v props = props { value = v }

-- | Set placeholder text
placeholder :: forall msg. String -> AutoCompleteProp msg
placeholder p props = props { placeholder = p }

-- | Set disabled state
acDisabled :: forall msg. Boolean -> AutoCompleteProp msg
acDisabled d props = props { disabled = d }

-- | Set loading state
acLoading :: forall msg. Boolean -> AutoCompleteProp msg
acLoading l props = props { loading = l }

-- | Control open state (controlled mode)
acOpen :: forall msg. Boolean -> AutoCompleteProp msg
acOpen o props = props { open = Just o }

-- | Set highlighted suggestion index
highlightedIndex :: forall msg. Int -> AutoCompleteProp msg
highlightedIndex idx props = props { highlightedIndex = idx }

-- | Set minimum characters before showing suggestions
minChars :: forall msg. Int -> AutoCompleteProp msg
minChars n props = props { minChars = n }

-- | Set maximum suggestions to display
maxSuggestions :: forall msg. Int -> AutoCompleteProp msg
maxSuggestions n props = props { maxSuggestions = n }

-- | Clear input on selection
clearOnSelect :: forall msg. Boolean -> AutoCompleteProp msg
clearOnSelect c props = props { clearOnSelect = c }

-- | Set text shown when no results
noResultsText :: forall msg. String -> AutoCompleteProp msg
noResultsText t props = props { noResultsText = t }

-- | Set text shown while loading
loadingText :: forall msg. String -> AutoCompleteProp msg
loadingText t props = props { loadingText = t }

-- | Set input id
acId :: forall msg. String -> AutoCompleteProp msg
acId i props = props { id = Just i }

-- | Set input name
acName :: forall msg. String -> AutoCompleteProp msg
acName n props = props { name = Just n }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set input background color (Color.RGB atom)
inputBackgroundColor :: forall msg. Color.RGB -> AutoCompleteProp msg
inputBackgroundColor c props = props { inputBackgroundColor = Just c }

-- | Set input text color (Color.RGB atom)
inputTextColor :: forall msg. Color.RGB -> AutoCompleteProp msg
inputTextColor c props = props { inputTextColor = Just c }

-- | Set input border color (Color.RGB atom)
inputBorderColor :: forall msg. Color.RGB -> AutoCompleteProp msg
inputBorderColor c props = props { inputBorderColor = Just c }

-- | Set input placeholder color (Color.RGB atom)
inputPlaceholderColor :: forall msg. Color.RGB -> AutoCompleteProp msg
inputPlaceholderColor c props = props { inputPlaceholderColor = Just c }

-- | Set input focus border color (Color.RGB atom)
inputFocusBorderColor :: forall msg. Color.RGB -> AutoCompleteProp msg
inputFocusBorderColor c props = props { inputFocusBorderColor = Just c }

-- | Set dropdown background color (Color.RGB atom)
dropdownBackgroundColor :: forall msg. Color.RGB -> AutoCompleteProp msg
dropdownBackgroundColor c props = props { dropdownBackgroundColor = Just c }

-- | Set dropdown border color (Color.RGB atom)
dropdownBorderColor :: forall msg. Color.RGB -> AutoCompleteProp msg
dropdownBorderColor c props = props { dropdownBorderColor = Just c }

-- | Set suggestion item text color (Color.RGB atom)
itemTextColor :: forall msg. Color.RGB -> AutoCompleteProp msg
itemTextColor c props = props { itemTextColor = Just c }

-- | Set highlighted item background color (Color.RGB atom)
itemHighlightBgColor :: forall msg. Color.RGB -> AutoCompleteProp msg
itemHighlightBgColor c props = props { itemHighlightBgColor = Just c }

-- | Set highlighted item text color (Color.RGB atom)
itemHighlightTextColor :: forall msg. Color.RGB -> AutoCompleteProp msg
itemHighlightTextColor c props = props { itemHighlightTextColor = Just c }

-- | Set loading text color (Color.RGB atom)
loadingTextColor :: forall msg. Color.RGB -> AutoCompleteProp msg
loadingTextColor c props = props { loadingTextColor = Just c }

-- | Set "no results" text color (Color.RGB atom)
noResultsTextColor :: forall msg. Color.RGB -> AutoCompleteProp msg
noResultsTextColor c props = props { noResultsTextColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set input border radius (Geometry.Corners atom)
inputBorderRadius :: forall msg. Geometry.Corners -> AutoCompleteProp msg
inputBorderRadius r props = props { inputBorderRadius = Just r }

-- | Set dropdown border radius (Geometry.Corners atom)
dropdownBorderRadius :: forall msg. Geometry.Corners -> AutoCompleteProp msg
dropdownBorderRadius r props = props { dropdownBorderRadius = Just r }

-- | Set input border width (Device.Pixel atom)
inputBorderWidth :: forall msg. Device.Pixel -> AutoCompleteProp msg
inputBorderWidth w props = props { inputBorderWidth = Just w }

-- | Set dropdown border width (Device.Pixel atom)
dropdownBorderWidth :: forall msg. Device.Pixel -> AutoCompleteProp msg
dropdownBorderWidth w props = props { dropdownBorderWidth = Just w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set input height (Device.Pixel atom)
inputHeight :: forall msg. Device.Pixel -> AutoCompleteProp msg
inputHeight h props = props { inputHeight = Just h }

-- | Set input horizontal padding (Device.Pixel atom)
inputPaddingX :: forall msg. Device.Pixel -> AutoCompleteProp msg
inputPaddingX p props = props { inputPaddingX = Just p }

-- | Set input vertical padding (Device.Pixel atom)
inputPaddingY :: forall msg. Device.Pixel -> AutoCompleteProp msg
inputPaddingY p props = props { inputPaddingY = Just p }

-- | Set dropdown max height (Device.Pixel atom)
dropdownMaxHeight :: forall msg. Device.Pixel -> AutoCompleteProp msg
dropdownMaxHeight h props = props { dropdownMaxHeight = Just h }

-- | Set item horizontal padding (Device.Pixel atom)
itemPaddingX :: forall msg. Device.Pixel -> AutoCompleteProp msg
itemPaddingX p props = props { itemPaddingX = Just p }

-- | Set item vertical padding (Device.Pixel atom)
itemPaddingY :: forall msg. Device.Pixel -> AutoCompleteProp msg
itemPaddingY p props = props { itemPaddingY = Just p }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // prop builders: typography
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set input font size (FontSize atom)
inputFontSize :: forall msg. FontSize.FontSize -> AutoCompleteProp msg
inputFontSize s props = props { inputFontSize = Just s }

-- | Set item font size (FontSize atom)
itemFontSize :: forall msg. FontSize.FontSize -> AutoCompleteProp msg
itemFontSize s props = props { itemFontSize = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set input change handler
onAcInput :: forall msg. (String -> msg) -> AutoCompleteProp msg
onAcInput handler props = props { onInput = Just handler }

-- | Set selection handler (receives the selected value)
onSelect :: forall msg. (String -> msg) -> AutoCompleteProp msg
onSelect handler props = props { onSelect = Just handler }

-- | Set open state change handler
onOpenChange :: forall msg. (Boolean -> msg) -> AutoCompleteProp msg
onOpenChange handler props = props { onOpenChange = Just handler }

-- | Set highlight change handler (for keyboard navigation)
onHighlightChange :: forall msg. (Int -> msg) -> AutoCompleteProp msg
onHighlightChange handler props = props { onHighlightChange = Just handler }

-- | Set focus handler
onAcFocus :: forall msg. msg -> AutoCompleteProp msg
onAcFocus handler props = props { onFocus = Just handler }

-- | Set blur handler
onAcBlur :: forall msg. msg -> AutoCompleteProp msg
onAcBlur handler props = props { onBlur = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // prop builders: escape hatch
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add extra attributes (escape hatch)
extraAttributes :: forall msg. Array (E.Attribute msg) -> AutoCompleteProp msg
extraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }
