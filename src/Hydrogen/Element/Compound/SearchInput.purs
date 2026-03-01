-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // element // search-input
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | SearchInput — Schema-native search input with icon, loading, and clear.
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
-- | | Property              | Pillar     | Type                      | CSS Output              |
-- | |-----------------------|------------|---------------------------|-------------------------|
-- | | backgroundColor       | Color      | Color.RGB                 | background-color        |
-- | | textColor             | Color      | Color.RGB                 | color                   |
-- | | borderColor           | Color      | Color.RGB                 | border-color            |
-- | | placeholderColor      | Color      | Color.RGB                 | ::placeholder color     |
-- | | focusBorderColor      | Color      | Color.RGB                 | :focus border-color     |
-- | | focusRingColor        | Color      | Color.RGB                 | :focus outline          |
-- | | iconColor             | Color      | Color.RGB                 | search icon color       |
-- | | clearButtonColor      | Color      | Color.RGB                 | clear button color      |
-- | | submitButtonColor     | Color      | Color.RGB                 | submit button color     |
-- | | borderRadius          | Geometry   | Geometry.Corners          | border-radius           |
-- | | borderWidth           | Dimension  | Device.Pixel              | border-width            |
-- | | height                | Dimension  | Device.Pixel              | height                  |
-- | | paddingX              | Dimension  | Device.Pixel              | padding-left/right      |
-- | | paddingY              | Dimension  | Device.Pixel              | padding-top/bottom      |
-- | | iconSize              | Dimension  | Device.Pixel              | icon width/height       |
-- | | fontSize              | Typography | FontSize.FontSize         | font-size               |
-- | | transitionDuration    | Motion     | Temporal.Milliseconds     | transition-duration     |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.SearchInput as SearchInput
-- | import Hydrogen.Render.Element as E
-- |
-- | -- Basic search input (inherits all visual properties from context)
-- | SearchInput.searchInput
-- |   [ SearchInput.searchValue state.query
-- |   , SearchInput.onSearchInput UpdateQuery
-- |   ]
-- |
-- | -- With loading state and brand atoms
-- | SearchInput.searchInput
-- |   [ SearchInput.searchValue state.query
-- |   , SearchInput.searchLoading state.isSearching
-- |   , SearchInput.iconColor brand.mutedForeground
-- |   , SearchInput.borderColor brand.inputBorder
-- |   , SearchInput.onSearchInput UpdateQuery
-- |   ]
-- |
-- | -- With clear button
-- | SearchInput.searchInput
-- |   [ SearchInput.searchValue state.query
-- |   , SearchInput.showClear true
-- |   , SearchInput.clearButtonColor brand.mutedForeground
-- |   , SearchInput.onClear ClearSearch
-- |   ]
-- | ```
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from:
-- | - `SearchInput.Types` — Core type definitions
-- | - `SearchInput.Props` — Property builder functions
-- | - `SearchInput.Icons` — SVG icon elements
-- | - `SearchInput.Builders` — Internal build functions

module Hydrogen.Element.Compound.SearchInput
  ( -- * SearchInput Component
    searchInput
  
  -- * Types (re-exported from Types)
  , module Types
  
  -- * Props (re-exported from Props)
  , module Props
  ) where

import Prelude
  ( show
  , (>)
  )

import Data.Array (foldl)
import Data.Maybe (maybe)
import Data.String as String

import Hydrogen.Render.Element as E

import Hydrogen.Element.Compound.SearchInput.Types (SearchInputProps, SearchInputProp, defaultProps) as Types
import Hydrogen.Element.Compound.SearchInput.Props
  ( searchValue
  , placeholder
  , searchDisabled
  , searchLoading
  , showClear
  , showSubmit
  , searchId
  , searchName
  , searchAriaLabel
  , backgroundColor
  , textColor
  , borderColor
  , placeholderColor
  , focusBorderColor
  , focusRingColor
  , iconColor
  , clearButtonColor
  , submitButtonColor
  , borderRadius
  , borderWidth
  , height
  , paddingX
  , paddingY
  , iconSize
  , fontSize
  , transitionDuration
  , onSearchInput
  , onSearchChange
  , onClear
  , onSubmit
  , onSearchFocus
  , onSearchBlur
  , extraAttributes
  ) as Props
import Hydrogen.Element.Compound.SearchInput.Builders (buildLeftIcon, buildSearchInput, buildRightButtons)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // main component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a search input with icon, optional loading spinner, and clear/submit
-- |
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
-- | All visual properties come from Schema atoms passed via props.
-- | When atoms are `Nothing`, no style is emitted (inherits from context).
searchInput :: forall msg. Array (Types.SearchInputProp msg) -> E.Element msg
searchInput propMods =
  let
    props = foldl (\p f -> f p) Types.defaultProps propMods
    hasValue = String.length props.value > 0
    iconSizeVal = maybe "16px" show props.iconSize
  in
    E.div_
      [ E.style "position" "relative"
      , E.style "display" "flex"
      , E.style "align-items" "center"
      , E.role "search"
      ]
      [ -- Search icon or loading spinner (left side)
        buildLeftIcon props iconSizeVal
      -- Input field
      , buildSearchInput props
      -- Right side buttons (clear and/or submit)
      , buildRightButtons props hasValue iconSizeVal
      ]
