-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // element // search-input // props
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | SearchInput Props — Property builder functions for SearchInput.
-- |
-- | Each function takes a Schema atom and returns a property modifier.
-- | This allows composable configuration via the builder pattern.

module Hydrogen.Element.Compound.SearchInput.Props
  ( -- * Content Props
    searchValue
  , placeholder
  , searchDisabled
  , searchLoading
  , showClear
  , showSubmit
  , searchId
  , searchName
  , searchAriaLabel
  
  -- * Color Atoms
  , backgroundColor
  , textColor
  , borderColor
  , placeholderColor
  , focusBorderColor
  , focusRingColor
  , iconColor
  , clearButtonColor
  , submitButtonColor
  
  -- * Geometry Atoms
  , borderRadius
  , borderWidth
  
  -- * Dimension Atoms
  , height
  , paddingX
  , paddingY
  , iconSize
  
  -- * Typography Atoms
  , fontSize
  
  -- * Motion Atoms
  , transitionDuration
  
  -- * Behavior Props
  , onSearchInput
  , onSearchChange
  , onClear
  , onSubmit
  , onSearchFocus
  , onSearchBlur
  
  -- * Escape Hatch
  , extraAttributes
  ) where

import Prelude ((<>))

import Data.Maybe (Maybe(Just))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Dimension.Temporal as Temporal
import Hydrogen.Schema.Typography.FontSize as FontSize

import Hydrogen.Element.Compound.SearchInput.Types (SearchInputProp)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // prop builders: content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set current search value
searchValue :: forall msg. String -> SearchInputProp msg
searchValue v props = props { value = v }

-- | Set placeholder text
placeholder :: forall msg. String -> SearchInputProp msg
placeholder p props = props { placeholder = p }

-- | Set disabled state
searchDisabled :: forall msg. Boolean -> SearchInputProp msg
searchDisabled d props = props { disabled = d }

-- | Set loading state
-- |
-- | When loading, the search icon is replaced with a spinner.
searchLoading :: forall msg. Boolean -> SearchInputProp msg
searchLoading l props = props { loading = l }

-- | Show clear button when input has value
showClear :: forall msg. Boolean -> SearchInputProp msg
showClear s props = props { showClear = s }

-- | Show submit button
showSubmit :: forall msg. Boolean -> SearchInputProp msg
showSubmit s props = props { showSubmit = s }

-- | Set input id
searchId :: forall msg. String -> SearchInputProp msg
searchId i props = props { id = Just i }

-- | Set input name
searchName :: forall msg. String -> SearchInputProp msg
searchName n props = props { name = Just n }

-- | Set aria-label
searchAriaLabel :: forall msg. String -> SearchInputProp msg
searchAriaLabel l props = props { ariaLabel = Just l }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set background color (Color.RGB atom)
backgroundColor :: forall msg. Color.RGB -> SearchInputProp msg
backgroundColor c props = props { backgroundColor = Just c }

-- | Set text color (Color.RGB atom)
textColor :: forall msg. Color.RGB -> SearchInputProp msg
textColor c props = props { textColor = Just c }

-- | Set border color (Color.RGB atom)
borderColor :: forall msg. Color.RGB -> SearchInputProp msg
borderColor c props = props { borderColor = Just c }

-- | Set placeholder text color (Color.RGB atom)
placeholderColor :: forall msg. Color.RGB -> SearchInputProp msg
placeholderColor c props = props { placeholderColor = Just c }

-- | Set focus border color (Color.RGB atom)
focusBorderColor :: forall msg. Color.RGB -> SearchInputProp msg
focusBorderColor c props = props { focusBorderColor = Just c }

-- | Set focus ring color (Color.RGB atom)
focusRingColor :: forall msg. Color.RGB -> SearchInputProp msg
focusRingColor c props = props { focusRingColor = Just c }

-- | Set search icon color (Color.RGB atom)
iconColor :: forall msg. Color.RGB -> SearchInputProp msg
iconColor c props = props { iconColor = Just c }

-- | Set clear button icon color (Color.RGB atom)
clearButtonColor :: forall msg. Color.RGB -> SearchInputProp msg
clearButtonColor c props = props { clearButtonColor = Just c }

-- | Set submit button icon color (Color.RGB atom)
submitButtonColor :: forall msg. Color.RGB -> SearchInputProp msg
submitButtonColor c props = props { submitButtonColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set border radius (Geometry.Corners atom)
borderRadius :: forall msg. Geometry.Corners -> SearchInputProp msg
borderRadius r props = props { borderRadius = Just r }

-- | Set border width (Device.Pixel atom)
borderWidth :: forall msg. Device.Pixel -> SearchInputProp msg
borderWidth w props = props { borderWidth = Just w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set input height (Device.Pixel atom)
height :: forall msg. Device.Pixel -> SearchInputProp msg
height h props = props { height = Just h }

-- | Set horizontal padding (Device.Pixel atom)
paddingX :: forall msg. Device.Pixel -> SearchInputProp msg
paddingX p props = props { paddingX = Just p }

-- | Set vertical padding (Device.Pixel atom)
paddingY :: forall msg. Device.Pixel -> SearchInputProp msg
paddingY p props = props { paddingY = Just p }

-- | Set icon size (Device.Pixel atom)
iconSize :: forall msg. Device.Pixel -> SearchInputProp msg
iconSize s props = props { iconSize = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // prop builders: typography
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set font size (FontSize atom)
fontSize :: forall msg. FontSize.FontSize -> SearchInputProp msg
fontSize s props = props { fontSize = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // prop builders: motion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set transition duration (Temporal.Milliseconds atom)
transitionDuration :: forall msg. Temporal.Milliseconds -> SearchInputProp msg
transitionDuration d props = props { transitionDuration = Just d }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set input handler (fires on each keystroke)
-- |
-- | Receives the current input value as a String.
onSearchInput :: forall msg. (String -> msg) -> SearchInputProp msg
onSearchInput handler props = props { onInput = Just handler }

-- | Set change handler (fires on blur after change)
-- |
-- | Receives the current input value as a String.
onSearchChange :: forall msg. (String -> msg) -> SearchInputProp msg
onSearchChange handler props = props { onChange = Just handler }

-- | Set clear handler (fires when clear button is clicked)
onClear :: forall msg. msg -> SearchInputProp msg
onClear handler props = props { onClear = Just handler }

-- | Set submit handler (fires on Enter key or submit button click)
-- |
-- | Receives the current input value as a String.
onSubmit :: forall msg. (String -> msg) -> SearchInputProp msg
onSubmit handler props = props { onSubmit = Just handler }

-- | Set focus handler
onSearchFocus :: forall msg. msg -> SearchInputProp msg
onSearchFocus handler props = props { onFocus = Just handler }

-- | Set blur handler
onSearchBlur :: forall msg. msg -> SearchInputProp msg
onSearchBlur handler props = props { onBlur = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // prop builders: escape hatch
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add extra attributes (escape hatch)
extraAttributes :: forall msg. Array (E.Attribute msg) -> SearchInputProp msg
extraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }
