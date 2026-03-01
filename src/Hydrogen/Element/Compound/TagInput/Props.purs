-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // element // tag-input // props
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TagInput Props — Property types and default values.
-- |
-- | All visual properties accept concrete Schema atoms.
-- | `Maybe` indicates optional — `Nothing` means no style is emitted,
-- | allowing inheritance from parent/context/brand.

module Hydrogen.Element.Compound.TagInput.Props
  ( -- * Types
    TagInputProps
  , TagInputProp
  
  -- * Defaults
  , defaultProps
  ) where

import Data.Maybe (Maybe(Nothing))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Typography.FontSize as FontSize

import Hydrogen.Element.Compound.TagInput.Types (Tag)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | TagInput properties
-- |
-- | All visual properties accept concrete Schema atoms.
-- | `Maybe` indicates optional — `Nothing` means no style is emitted,
-- | allowing inheritance from parent/context/brand.
type TagInputProps msg =
  { -- Content
    tags :: Array Tag
  , inputValue :: String
  , placeholder :: String
  , disabled :: Boolean
  , maxTags :: Maybe Int
  , allowDuplicates :: Boolean
  , allowCustom :: Boolean
  , delimiter :: String
  , id :: Maybe String
  , name :: Maybe String
  
  -- Color atoms
  , backgroundColor :: Maybe Color.RGB
  , textColor :: Maybe Color.RGB
  , borderColor :: Maybe Color.RGB
  , placeholderColor :: Maybe Color.RGB
  , focusBorderColor :: Maybe Color.RGB
  , tagBackgroundColor :: Maybe Color.RGB
  , tagTextColor :: Maybe Color.RGB
  , tagRemoveColor :: Maybe Color.RGB
  
  -- Geometry atoms
  , borderRadius :: Maybe Geometry.Corners
  , tagBorderRadius :: Maybe Geometry.Corners
  , borderWidth :: Maybe Device.Pixel
  
  -- Dimension atoms
  , minHeight :: Maybe Device.Pixel
  , paddingX :: Maybe Device.Pixel
  , paddingY :: Maybe Device.Pixel
  , gap :: Maybe Device.Pixel
  , tagPaddingX :: Maybe Device.Pixel
  , tagPaddingY :: Maybe Device.Pixel
  
  -- Typography atoms
  , fontSize :: Maybe FontSize.FontSize
  , tagFontSize :: Maybe FontSize.FontSize
  
  -- Behavior
  , onAdd :: Maybe (String -> msg)
  , onRemove :: Maybe (String -> msg)
  , onInputChange :: Maybe (String -> msg)
  , onFocus :: Maybe msg
  , onBlur :: Maybe msg
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier
type TagInputProp msg = TagInputProps msg -> TagInputProps msg

-- | Default properties
-- |
-- | Visual atoms default to `Nothing` (no style emitted, inherit from context).
-- | This ensures the component works with any BrandSchema.
defaultProps :: forall msg. TagInputProps msg
defaultProps =
  { tags: []
  , inputValue: ""
  , placeholder: "Add tags..."
  , disabled: false
  , maxTags: Nothing
  , allowDuplicates: false
  , allowCustom: true
  , delimiter: ","
  , id: Nothing
  , name: Nothing
  , backgroundColor: Nothing
  , textColor: Nothing
  , borderColor: Nothing
  , placeholderColor: Nothing
  , focusBorderColor: Nothing
  , tagBackgroundColor: Nothing
  , tagTextColor: Nothing
  , tagRemoveColor: Nothing
  , borderRadius: Nothing
  , tagBorderRadius: Nothing
  , borderWidth: Nothing
  , minHeight: Nothing
  , paddingX: Nothing
  , paddingY: Nothing
  , gap: Nothing
  , tagPaddingX: Nothing
  , tagPaddingY: Nothing
  , fontSize: Nothing
  , tagFontSize: Nothing
  , onAdd: Nothing
  , onRemove: Nothing
  , onInputChange: Nothing
  , onFocus: Nothing
  , onBlur: Nothing
  , extraAttributes: []
  }
