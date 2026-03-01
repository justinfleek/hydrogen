-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // element // tag-input
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TagInput — Schema-native multi-tag input component.
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
-- | | backgroundColor       | Color      | Color.RGB                 | container background    |
-- | | textColor             | Color      | Color.RGB                 | text color              |
-- | | borderColor           | Color      | Color.RGB                 | border-color            |
-- | | focusBorderColor      | Color      | Color.RGB                 | :focus border-color     |
-- | | tagBackgroundColor    | Color      | Color.RGB                 | tag background          |
-- | | tagTextColor          | Color      | Color.RGB                 | tag text color          |
-- | | tagRemoveColor        | Color      | Color.RGB                 | tag remove button color |
-- | | borderRadius          | Geometry   | Geometry.Corners          | container border-radius |
-- | | tagBorderRadius       | Geometry   | Geometry.Corners          | tag border-radius       |
-- | | borderWidth           | Dimension  | Device.Pixel              | border-width            |
-- | | height                | Dimension  | Device.Pixel              | min-height              |
-- | | paddingX              | Dimension  | Device.Pixel              | padding-left/right      |
-- | | paddingY              | Dimension  | Device.Pixel              | padding-top/bottom      |
-- | | gap                   | Dimension  | Device.Pixel              | gap between tags        |
-- | | fontSize              | Typography | FontSize.FontSize         | font-size               |
-- | | tagFontSize           | Typography | FontSize.FontSize         | tag font-size           |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.TagInput as TagInput
-- | import Hydrogen.Render.Element as E
-- |
-- | -- Basic tag input (inherits all visual properties from context)
-- | TagInput.tagInput
-- |   [ TagInput.tagValues state.tags
-- |   , TagInput.onAdd AddTag
-- |   , TagInput.onRemove RemoveTag
-- |   ]
-- |
-- | -- With brand atoms
-- | TagInput.tagInput
-- |   [ TagInput.tagValues state.tags
-- |   , TagInput.tagBackgroundColor brand.secondary
-- |   , TagInput.tagTextColor brand.secondaryForeground
-- |   , TagInput.borderColor brand.inputBorder
-- |   , TagInput.borderRadius brand.inputRadius
-- |   , TagInput.onAdd AddTag
-- |   , TagInput.onRemove RemoveTag
-- |   ]
-- |
-- | -- With max tags limit
-- | TagInput.tagInput
-- |   [ TagInput.tagValues state.tags
-- |   , TagInput.maxTags 5
-- |   ]
-- | ```
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from:
-- | - `Types` — Tag type and constructors
-- | - `Props` — Property types and defaults
-- | - `PropBuilders` — Functions to modify properties
-- | - `Render` — Component rendering functions
-- | - `Icons` — SVG icons

module Hydrogen.Element.Compound.TagInput
  ( module Types
  , module Props
  , module PropBuilders
  , module Render
  , module Icons
  ) where

import Hydrogen.Element.Compound.TagInput.Types
  ( Tag
  , mkTag
  , tagWithLabel
  ) as Types

import Hydrogen.Element.Compound.TagInput.Props
  ( TagInputProp
  , TagInputProps
  , defaultProps
  ) as Props

import Hydrogen.Element.Compound.TagInput.PropBuilders
  ( allowCustom
  , allowDuplicates
  , backgroundColor
  , borderColor
  , borderRadius
  , borderWidth
  , delimiter
  , extraAttributes
  , focusBorderColor
  , fontSize
  , gap
  , inputValue
  , maxTags
  , minHeight
  , onAdd
  , onInputChange
  , onRemove
  , onTagInputBlur
  , onTagInputFocus
  , paddingX
  , paddingY
  , placeholder
  , placeholderColor
  , tagBackgroundColor
  , tagBorderRadius
  , tagDisabled
  , tagFontSize
  , tagInputId
  , tagInputName
  , tagPaddingX
  , tagPaddingY
  , tagRemoveColor
  , tagTextColor
  , tagValues
  , tagsData
  , textColor
  ) as PropBuilders

import Hydrogen.Element.Compound.TagInput.Render
  ( tagBadge
  , tagInput
  , tagList
  ) as Render

import Hydrogen.Element.Compound.TagInput.Icons
  ( removeIcon
  ) as Icons
