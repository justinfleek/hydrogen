-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // element // compound // auto-complete
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | AutoComplete — Schema-native combobox with suggestions dropdown.
-- |
-- | ## Design Philosophy
-- |
-- | This component accepts **concrete Schema atoms**, not semantic tokens.
-- | Every visual property maps directly to atoms from the 12 pillars.
-- | When an atom is `Nothing`, no style is emitted — the element inherits
-- | from its parent or browser defaults.
-- |
-- | **No hardcoded CSS values.** The BrandSchema provides all visual atoms.
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property                | Pillar     | Type                      | CSS Output              |
-- | |-------------------------|------------|---------------------------|-------------------------|
-- | | inputBackgroundColor    | Color      | Color.RGB                 | input background        |
-- | | inputTextColor          | Color      | Color.RGB                 | input text color        |
-- | | inputBorderColor        | Color      | Color.RGB                 | input border-color      |
-- | | dropdownBackgroundColor | Color      | Color.RGB                 | dropdown background     |
-- | | dropdownBorderColor     | Color      | Color.RGB                 | dropdown border         |
-- | | itemTextColor           | Color      | Color.RGB                 | suggestion text         |
-- | | itemHighlightBgColor    | Color      | Color.RGB                 | highlighted item bg     |
-- | | itemHighlightTextColor  | Color      | Color.RGB                 | highlighted item text   |
-- | | inputBorderRadius       | Geometry   | Geometry.Corners          | input border-radius     |
-- | | dropdownBorderRadius    | Geometry   | Geometry.Corners          | dropdown border-radius  |
-- | | inputHeight             | Dimension  | Device.Pixel              | input height            |
-- | | inputPaddingX           | Dimension  | Device.Pixel              | input padding-left/right|
-- | | dropdownMaxHeight       | Dimension  | Device.Pixel              | dropdown max-height     |
-- | | itemPaddingX            | Dimension  | Device.Pixel              | item padding-left/right |
-- | | itemPaddingY            | Dimension  | Device.Pixel              | item padding-top/bottom |
-- | | inputFontSize           | Typography | FontSize.FontSize         | input font-size         |
-- | | itemFontSize            | Typography | FontSize.FontSize         | item font-size          |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.AutoComplete as AC
-- | import Hydrogen.Render.Element as E
-- |
-- | -- Basic autocomplete (inherits all visual properties from context)
-- | AC.autoComplete
-- |   [ AC.suggestionStrings [ "Apple", "Apricot", "Avocado", "Banana" ]
-- |   , AC.acValue state.query
-- |   , AC.onAcInput UpdateQuery
-- |   , AC.onSelect SelectItem
-- |   ]
-- |
-- | -- With brand atoms
-- | AC.autoComplete
-- |   [ AC.suggestionStrings items
-- |   , AC.inputBackgroundColor brand.background
-- |   , AC.dropdownBackgroundColor brand.popover
-- |   , AC.itemHighlightBgColor brand.accent
-- |   , AC.inputBorderRadius brand.inputRadius
-- |   ]
-- |
-- | -- With loading state
-- | AC.autoComplete
-- |   [ AC.suggestionStrings results
-- |   , AC.acLoading state.isSearching
-- |   , AC.loadingText "Searching..."
-- |   ]
-- | ```
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from:
-- | - `AutoComplete.Types` — Core types (Suggestion, Props)
-- | - `AutoComplete.Props` — Property builder functions
-- | - `AutoComplete.Render` — Component rendering

module Hydrogen.Element.Compound.AutoComplete
  ( -- * AutoComplete Component (re-exported from Render)
    module ReexportRender
  
  -- * Types (re-exported from Types)
  , module ReexportTypes
  
  -- * Props (re-exported from Props)
  , module ReexportProps
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Element.Compound.AutoComplete.Types
  ( Suggestion
  , mkSuggestion
  , suggestionWithLabel
  , AutoCompleteProps
  , AutoCompleteProp
  , defaultProps
  ) as ReexportTypes

import Hydrogen.Element.Compound.AutoComplete.Props
  ( suggestionStrings
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
  , inputBorderRadius
  , dropdownBorderRadius
  , inputBorderWidth
  , dropdownBorderWidth
  , inputHeight
  , inputPaddingX
  , inputPaddingY
  , dropdownMaxHeight
  , itemPaddingX
  , itemPaddingY
  , inputFontSize
  , itemFontSize
  , onAcInput
  , onSelect
  , onOpenChange
  , onHighlightChange
  , onAcFocus
  , onAcBlur
  , extraAttributes
  ) as ReexportProps

import Hydrogen.Element.Compound.AutoComplete.Render
  ( autoComplete
  ) as ReexportRender
