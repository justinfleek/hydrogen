-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // element // text-area
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Textarea — Schema-native multi-line text input component.
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
-- | | errorBorderColor      | Color      | Color.RGB                 | error border-color      |
-- | | errorTextColor        | Color      | Color.RGB                 | error message color     |
-- | | labelColor            | Color      | Color.RGB                 | label text color        |
-- | | counterColor          | Color      | Color.RGB                 | counter text color      |
-- | | requiredColor         | Color      | Color.RGB                 | required asterisk color |
-- | | borderRadius          | Geometry   | Geometry.Corners          | border-radius           |
-- | | borderWidth           | Dimension  | Device.Pixel              | border-width            |
-- | | minHeight             | Dimension  | Device.Pixel              | min-height              |
-- | | paddingX              | Dimension  | Device.Pixel              | padding-left/right      |
-- | | paddingY              | Dimension  | Device.Pixel              | padding-top/bottom      |
-- | | fontSize              | Typography | FontSize.FontSize         | font-size               |
-- | | lineHeight            | Typography | LineHeight.LineHeight     | line-height             |
-- | | labelFontSize         | Typography | FontSize.FontSize         | label font-size         |
-- | | labelFontWeight       | Typography | FontWeight.FontWeight     | label font-weight       |
-- | | counterFontSize       | Typography | FontSize.FontSize         | counter font-size       |
-- | | transitionDuration    | Motion     | Temporal.Milliseconds     | transition-duration     |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Textarea as Textarea
-- | import Hydrogen.Render.Element as E
-- |
-- | -- Basic textarea (inherits all visual properties from context)
-- | Textarea.textarea
-- |   [ Textarea.placeholder "Enter your message..."
-- |   , Textarea.onTextareaInput UpdateMessage
-- |   ]
-- |
-- | -- With brand atoms
-- | Textarea.textarea
-- |   [ Textarea.placeholder "Enter your message..."
-- |   , Textarea.backgroundColor brand.inputBackground
-- |   , Textarea.textColor brand.foreground
-- |   , Textarea.borderColor brand.inputBorder
-- |   , Textarea.borderRadius brand.inputRadius
-- |   , Textarea.fontSize brand.bodyFontSize
-- |   , Textarea.onTextareaInput UpdateMessage
-- |   ]
-- |
-- | -- Full field with label, counter, and error
-- | Textarea.textareaField "Bio"
-- |   [ Textarea.maxLength 280
-- |   , Textarea.textareaValue state.bio
-- |   , Textarea.textareaRequired true
-- |   , Textarea.labelColor brand.foreground
-- |   , Textarea.errorTextColor brand.destructive
-- |   , Textarea.requiredColor brand.destructive
-- |   ]
-- | ```
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from:
-- | - `Textarea.Types` — Core type definitions
-- | - `Textarea.Props` — Property builders
-- | - `Textarea.Core` — Main component and style builders
-- | - `Textarea.Field` — Labeled components and helpers

module Hydrogen.Element.Compound.Textarea
  ( -- * Re-export Types module
    module Types
  
  -- * Re-export Props module
  , module Props
  
  -- * Re-export Core module
  , module Core
  
  -- * Re-export Field module
  , module Field
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

-- Types: Core type definitions
import Hydrogen.Element.Compound.Textarea.Types
  ( TextareaProps
  , TextareaProp
  , defaultProps
  ) as Types

-- Props: Property builder functions
import Hydrogen.Element.Compound.Textarea.Props
  ( placeholder
  , textareaValue
  , textareaDisabled
  , textareaReadOnly
  , textareaRequired
  , textareaId
  , textareaName
  , minRows
  , maxRows
  , maxLength
  , autoResize
  , textareaError
  , errorMessage
  , backgroundColor
  , textColor
  , borderColor
  , placeholderColor
  , focusBorderColor
  , focusRingColor
  , errorBorderColor
  , errorTextColor
  , labelColor
  , counterColor
  , requiredColor
  , borderRadius
  , borderWidth
  , minHeight
  , paddingX
  , paddingY
  , fontSize
  , lineHeight
  , labelFontSize
  , labelFontWeight
  , counterFontSize
  , transitionDuration
  , onTextareaInput
  , onTextareaChange
  , onTextareaFocus
  , onTextareaBlur
  , extraAttributes
  ) as Props

-- Core: Main component and style builders
import Hydrogen.Element.Compound.Textarea.Core
  ( textarea
  , buildTextareaAttrs
  , buildTextareaStyles
  ) as Core

-- Field: Labeled components and helpers
import Hydrogen.Element.Compound.Textarea.Field
  ( textareaWithLabel
  , textareaWithCounter
  , textareaField
  , renderErrorMessage
  ) as Field
