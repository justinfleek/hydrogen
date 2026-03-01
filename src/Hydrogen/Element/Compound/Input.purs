-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                               // hydrogen // element // input
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Input — Schema-native text input component.
-- |
-- | ## Design Philosophy
-- |
-- | This component accepts **concrete Schema atoms**, not semantic tokens.
-- | Every visual property maps directly to atoms from the 12 pillars:
-- |
-- | - **Color**: Background, text, border, placeholder, focus ring
-- | - **Geometry**: Border radius, border width
-- | - **Dimension**: Height, padding
-- | - **Typography**: Font size, font weight
-- | - **Motion**: Transition timing
-- |
-- | The **BrandSchema** defines what these atoms are for a given brand.
-- | This component just renders them faithfully.
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
-- | | focusRingColor        | Color      | Color.RGB                 | focus outline           |
-- | | borderRadius          | Geometry   | Geometry.Corners          | border-radius           |
-- | | borderWidth           | Dimension  | Device.Pixel              | border-width            |
-- | | height                | Dimension  | Device.Pixel              | height                  |
-- | | paddingX              | Dimension  | Device.Pixel              | padding-left/right      |
-- | | paddingY              | Dimension  | Device.Pixel              | padding-top/bottom      |
-- | | fontSize              | Typography | Typography.FontSize       | font-size               |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Input as Input
-- | import Hydrogen.Schema.Color.RGB as Color
-- | import Hydrogen.Schema.Dimension.Device as Device
-- |
-- | -- Basic input
-- | Input.input
-- |   [ Input.placeholder "Enter text..."
-- |   , Input.onInputChange UpdateText
-- |   ]
-- |
-- | -- With brand atoms
-- | Input.input
-- |   [ Input.placeholder "Email address"
-- |   , Input.inputType Input.Email
-- |   , Input.backgroundColor brand.inputBackground
-- |   , Input.borderColor brand.inputBorder
-- |   , Input.focusBorderColor brand.primaryColor
-- |   , Input.borderRadius brand.inputRadius
-- |   , Input.height brand.inputHeight
-- |   ]
-- |
-- | -- Textarea
-- | Input.textarea
-- |   [ Input.placeholder "Write your message..."
-- |   , Input.rows 4
-- |   ]
-- |
-- | -- With label
-- | Input.inputWithLabel "Email"
-- |   [ Input.inputType Input.Email
-- |   , Input.inputRequired true
-- |   ]
-- | ```
-- |
-- | ## Companion Components
-- |
-- | - `input` — Single-line text input
-- | - `textarea` — Multi-line text input
-- | - `inputWithLabel` — Input with associated label
-- | - `textareaWithLabel` — Textarea with associated label
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from:
-- | - `Input.Types` — Core types (InputType, InputProps, InputProp, defaultProps)
-- | - `Input.Props` — Property builder functions
-- | - `Input.Render` — Main input and textarea components
-- | - `Input.Labeled` — Labeled component variants

module Hydrogen.Element.Compound.Input
  ( module Types
  , module Props
  , module Render
  , module Labeled
  ) where

import Hydrogen.Element.Compound.Input.Types
  ( InputProp
  , InputProps
  , InputType
      ( Text
      , Password
      , Email
      , Number
      , Tel
      , Url
      , Search
      , Date
      , Time
      , DatetimeLocal
      , Month
      , Week
      , Color
      , File
      , Hidden
      )
  , defaultProps
  , inputTypeToString
  ) as Types

import Hydrogen.Element.Compound.Input.Props
  ( backgroundColor
  , borderColor
  , borderRadius
  , borderWidth
  , extraAttributes
  , focusBorderColor
  , focusRingColor
  , fontSize
  , height
  , inputDisabled
  , inputId
  , inputName
  , inputReadOnly
  , inputRequired
  , inputType
  , inputValue
  , labelColor
  , labelFontSize
  , labelFontWeight
  , minHeight
  , onInputChange
  , paddingX
  , paddingY
  , placeholder
  , placeholderColor
  , rows
  , textColor
  , transitionDuration
  ) as Props

import Hydrogen.Element.Compound.Input.Render
  ( buildInputStyles
  , input
  , textarea
  ) as Render

import Hydrogen.Element.Compound.Input.Labeled
  ( inputWithLabel
  , sanitizeForId
  , textareaWithLabel
  ) as Labeled
