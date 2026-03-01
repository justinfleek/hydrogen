-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // element // search-input // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | SearchInput Types — Core type definitions and defaults.
-- |
-- | All visual properties accept concrete Schema atoms.
-- | `Maybe` indicates optional — `Nothing` means no style is emitted,
-- | allowing inheritance from parent or browser defaults.

module Hydrogen.Element.Compound.SearchInput.Types
  ( -- * Types
    SearchInputProps
  , SearchInputProp
  
  -- * Defaults
  , defaultProps
  ) where

import Data.Maybe (Maybe(Nothing))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Dimension.Temporal as Temporal
import Hydrogen.Schema.Typography.FontSize as FontSize

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | SearchInput properties
-- |
-- | All visual properties accept concrete Schema atoms.
-- | `Maybe` indicates optional — `Nothing` means no style is emitted,
-- | allowing inheritance from parent/context/brand.
type SearchInputProps msg =
  { -- Content
    value :: String
  , placeholder :: String
  , disabled :: Boolean
  , loading :: Boolean
  , showClear :: Boolean
  , showSubmit :: Boolean
  , id :: Maybe String
  , name :: Maybe String
  , ariaLabel :: Maybe String
  
  -- Color atoms
  , backgroundColor :: Maybe Color.RGB
  , textColor :: Maybe Color.RGB
  , borderColor :: Maybe Color.RGB
  , placeholderColor :: Maybe Color.RGB
  , focusBorderColor :: Maybe Color.RGB
  , focusRingColor :: Maybe Color.RGB
  , iconColor :: Maybe Color.RGB
  , clearButtonColor :: Maybe Color.RGB
  , submitButtonColor :: Maybe Color.RGB
  
  -- Geometry atoms
  , borderRadius :: Maybe Geometry.Corners
  , borderWidth :: Maybe Device.Pixel
  
  -- Dimension atoms
  , height :: Maybe Device.Pixel
  , paddingX :: Maybe Device.Pixel
  , paddingY :: Maybe Device.Pixel
  , iconSize :: Maybe Device.Pixel
  
  -- Typography atoms
  , fontSize :: Maybe FontSize.FontSize
  
  -- Motion atoms
  , transitionDuration :: Maybe Temporal.Milliseconds
  
  -- Behavior
  , onInput :: Maybe (String -> msg)
  , onChange :: Maybe (String -> msg)
  , onClear :: Maybe msg
  , onSubmit :: Maybe (String -> msg)
  , onFocus :: Maybe msg
  , onBlur :: Maybe msg
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier
type SearchInputProp msg = SearchInputProps msg -> SearchInputProps msg

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // defaults
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default properties
-- |
-- | Visual atoms default to `Nothing` (no style emitted, inherit from context).
-- | This ensures the component works with any BrandSchema.
defaultProps :: forall msg. SearchInputProps msg
defaultProps =
  { value: ""
  , placeholder: "Search..."
  , disabled: false
  , loading: false
  , showClear: true
  , showSubmit: false
  , id: Nothing
  , name: Nothing
  , ariaLabel: Nothing
  , backgroundColor: Nothing
  , textColor: Nothing
  , borderColor: Nothing
  , placeholderColor: Nothing
  , focusBorderColor: Nothing
  , focusRingColor: Nothing
  , iconColor: Nothing
  , clearButtonColor: Nothing
  , submitButtonColor: Nothing
  , borderRadius: Nothing
  , borderWidth: Nothing
  , height: Nothing
  , paddingX: Nothing
  , paddingY: Nothing
  , iconSize: Nothing
  , fontSize: Nothing
  , transitionDuration: Nothing
  , onInput: Nothing
  , onChange: Nothing
  , onClear: Nothing
  , onSubmit: Nothing
  , onFocus: Nothing
  , onBlur: Nothing
  , extraAttributes: []
  }
