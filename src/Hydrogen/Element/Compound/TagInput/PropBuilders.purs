-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // element // tag-input // prop-builders
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TagInput PropBuilders — Functions to modify TagInput properties.
-- |
-- | All prop builders accept Schema atoms directly.
-- | When atoms are `Nothing`, no style is emitted (inherits from context).

module Hydrogen.Element.Compound.TagInput.PropBuilders
  ( -- * Content Props
    tagValues
  , tagsData
  , inputValue
  , placeholder
  , tagDisabled
  , maxTags
  , allowDuplicates
  , allowCustom
  , delimiter
  , tagInputId
  , tagInputName
  
  -- * Color Atoms
  , backgroundColor
  , textColor
  , borderColor
  , placeholderColor
  , focusBorderColor
  , tagBackgroundColor
  , tagTextColor
  , tagRemoveColor
  
  -- * Geometry Atoms
  , borderRadius
  , tagBorderRadius
  , borderWidth
  
  -- * Dimension Atoms
  , minHeight
  , paddingX
  , paddingY
  , gap
  , tagPaddingX
  , tagPaddingY
  
  -- * Typography Atoms
  , fontSize
  , tagFontSize
  
  -- * Behavior Props
  , onAdd
  , onRemove
  , onInputChange
  , onTagInputFocus
  , onTagInputBlur
  
  -- * Escape Hatch
  , extraAttributes
  ) where

import Prelude
  ( map
  , (<>)
  )

import Data.Maybe (Maybe(Just))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Typography.FontSize as FontSize

import Hydrogen.Element.Compound.TagInput.Types (Tag, mkTag)
import Hydrogen.Element.Compound.TagInput.Props (TagInputProp)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // prop builders: content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set tags from simple strings
tagValues :: forall msg. Array String -> TagInputProp msg
tagValues strs props = props { tags = map mkTag strs }

-- | Set tags with full Tag data
tagsData :: forall msg. Array Tag -> TagInputProp msg
tagsData ts props = props { tags = ts }

-- | Set current input value
inputValue :: forall msg. String -> TagInputProp msg
inputValue v props = props { inputValue = v }

-- | Set placeholder text
placeholder :: forall msg. String -> TagInputProp msg
placeholder p props = props { placeholder = p }

-- | Set disabled state
tagDisabled :: forall msg. Boolean -> TagInputProp msg
tagDisabled d props = props { disabled = d }

-- | Set maximum number of tags
maxTags :: forall msg. Int -> TagInputProp msg
maxTags n props = props { maxTags = Just n }

-- | Allow duplicate tags
allowDuplicates :: forall msg. Boolean -> TagInputProp msg
allowDuplicates a props = props { allowDuplicates = a }

-- | Allow custom tags (not from suggestions)
allowCustom :: forall msg. Boolean -> TagInputProp msg
allowCustom a props = props { allowCustom = a }

-- | Set delimiter for splitting input (e.g., "," or ";")
delimiter :: forall msg. String -> TagInputProp msg
delimiter d props = props { delimiter = d }

-- | Set input id
tagInputId :: forall msg. String -> TagInputProp msg
tagInputId i props = props { id = Just i }

-- | Set input name
tagInputName :: forall msg. String -> TagInputProp msg
tagInputName n props = props { name = Just n }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set container background color (Color.RGB atom)
backgroundColor :: forall msg. Color.RGB -> TagInputProp msg
backgroundColor c props = props { backgroundColor = Just c }

-- | Set text color (Color.RGB atom)
textColor :: forall msg. Color.RGB -> TagInputProp msg
textColor c props = props { textColor = Just c }

-- | Set border color (Color.RGB atom)
borderColor :: forall msg. Color.RGB -> TagInputProp msg
borderColor c props = props { borderColor = Just c }

-- | Set placeholder text color (Color.RGB atom)
placeholderColor :: forall msg. Color.RGB -> TagInputProp msg
placeholderColor c props = props { placeholderColor = Just c }

-- | Set focus border color (Color.RGB atom)
focusBorderColor :: forall msg. Color.RGB -> TagInputProp msg
focusBorderColor c props = props { focusBorderColor = Just c }

-- | Set tag background color (Color.RGB atom)
tagBackgroundColor :: forall msg. Color.RGB -> TagInputProp msg
tagBackgroundColor c props = props { tagBackgroundColor = Just c }

-- | Set tag text color (Color.RGB atom)
tagTextColor :: forall msg. Color.RGB -> TagInputProp msg
tagTextColor c props = props { tagTextColor = Just c }

-- | Set tag remove button color (Color.RGB atom)
tagRemoveColor :: forall msg. Color.RGB -> TagInputProp msg
tagRemoveColor c props = props { tagRemoveColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set container border radius (Geometry.Corners atom)
borderRadius :: forall msg. Geometry.Corners -> TagInputProp msg
borderRadius r props = props { borderRadius = Just r }

-- | Set tag border radius (Geometry.Corners atom)
tagBorderRadius :: forall msg. Geometry.Corners -> TagInputProp msg
tagBorderRadius r props = props { tagBorderRadius = Just r }

-- | Set border width (Device.Pixel atom)
borderWidth :: forall msg. Device.Pixel -> TagInputProp msg
borderWidth w props = props { borderWidth = Just w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set container minimum height (Device.Pixel atom)
minHeight :: forall msg. Device.Pixel -> TagInputProp msg
minHeight h props = props { minHeight = Just h }

-- | Set horizontal padding (Device.Pixel atom)
paddingX :: forall msg. Device.Pixel -> TagInputProp msg
paddingX p props = props { paddingX = Just p }

-- | Set vertical padding (Device.Pixel atom)
paddingY :: forall msg. Device.Pixel -> TagInputProp msg
paddingY p props = props { paddingY = Just p }

-- | Set gap between tags (Device.Pixel atom)
gap :: forall msg. Device.Pixel -> TagInputProp msg
gap g props = props { gap = Just g }

-- | Set tag horizontal padding (Device.Pixel atom)
tagPaddingX :: forall msg. Device.Pixel -> TagInputProp msg
tagPaddingX p props = props { tagPaddingX = Just p }

-- | Set tag vertical padding (Device.Pixel atom)
tagPaddingY :: forall msg. Device.Pixel -> TagInputProp msg
tagPaddingY p props = props { tagPaddingY = Just p }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // prop builders: typography
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set font size (FontSize atom)
fontSize :: forall msg. FontSize.FontSize -> TagInputProp msg
fontSize s props = props { fontSize = Just s }

-- | Set tag font size (FontSize atom)
tagFontSize :: forall msg. FontSize.FontSize -> TagInputProp msg
tagFontSize s props = props { tagFontSize = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set add handler (fires when Enter or delimiter is pressed)
-- |
-- | Receives the trimmed input value as a String.
onAdd :: forall msg. (String -> msg) -> TagInputProp msg
onAdd handler props = props { onAdd = Just handler }

-- | Set remove handler (fires when a tag's remove button is clicked)
-- |
-- | Receives the tag value as a String.
onRemove :: forall msg. (String -> msg) -> TagInputProp msg
onRemove handler props = props { onRemove = Just handler }

-- | Set input change handler
onInputChange :: forall msg. (String -> msg) -> TagInputProp msg
onInputChange handler props = props { onInputChange = Just handler }

-- | Set focus handler
onTagInputFocus :: forall msg. msg -> TagInputProp msg
onTagInputFocus handler props = props { onFocus = Just handler }

-- | Set blur handler
onTagInputBlur :: forall msg. msg -> TagInputProp msg
onTagInputBlur handler props = props { onBlur = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // prop builders: escape hatch
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add extra attributes (escape hatch)
extraAttributes :: forall msg. Array (E.Attribute msg) -> TagInputProp msg
extraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }
