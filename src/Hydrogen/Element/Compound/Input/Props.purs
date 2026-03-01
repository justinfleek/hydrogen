-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // element // input // props
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Input.Props — Property builder functions for Input components.
-- |
-- | This module provides builder functions that create InputProp modifiers.
-- | Each function accepts a Schema atom and returns a property modifier.
-- |
-- | Organized by Schema pillar:
-- | - Content props (type, placeholder, value, etc.)
-- | - Color atoms
-- | - Geometry atoms
-- | - Dimension atoms
-- | - Typography atoms
-- | - Motion atoms
-- | - Behavior props

module Hydrogen.Element.Compound.Input.Props
  ( -- * Content Props
    inputType
  , placeholder
  , inputValue
  , inputDisabled
  , inputRequired
  , inputReadOnly
  , inputId
  , inputName
  , rows
  
  -- * Color Atoms
  , backgroundColor
  , textColor
  , borderColor
  , placeholderColor
  , focusBorderColor
  , focusRingColor
  , labelColor
  
  -- * Geometry Atoms
  , borderRadius
  , borderWidth
  
  -- * Dimension Atoms
  , height
  , paddingX
  , paddingY
  , minHeight
  
  -- * Typography Atoms
  , fontSize
  , labelFontSize
  , labelFontWeight
  
  -- * Motion Atoms
  , transitionDuration
  
  -- * Behavior Props
  , onInputChange
  
  -- * Escape Hatch
  , extraAttributes
  ) where

import Prelude
  ( (<>)
  )

import Data.Maybe (Maybe(Just))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Dimension.Temporal as Temporal
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Typography.FontWeight as FontWeight

import Hydrogen.Element.Compound.Input.Types
  ( InputType
  , InputProp
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // prop builders: content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set input type
inputType :: forall msg. InputType -> InputProp msg
inputType t props = props { inputType = t }

-- | Set placeholder text
placeholder :: forall msg. String -> InputProp msg
placeholder p props = props { placeholder = p }

-- | Set current value
inputValue :: forall msg. String -> InputProp msg
inputValue v props = props { value = v }

-- | Set disabled state
inputDisabled :: forall msg. Boolean -> InputProp msg
inputDisabled d props = props { disabled = d }

-- | Set required state
inputRequired :: forall msg. Boolean -> InputProp msg
inputRequired r props = props { required = r }

-- | Set read-only state
inputReadOnly :: forall msg. Boolean -> InputProp msg
inputReadOnly r props = props { readOnly = r }

-- | Set input id
inputId :: forall msg. String -> InputProp msg
inputId i props = props { id = Just i }

-- | Set input name
inputName :: forall msg. String -> InputProp msg
inputName n props = props { name = Just n }

-- | Set rows (for textarea)
rows :: forall msg. Int -> InputProp msg
rows r props = props { rows = r }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set input background color (Color.RGB atom)
backgroundColor :: forall msg. Color.RGB -> InputProp msg
backgroundColor c props = props { backgroundColor = Just c }

-- | Set input text color (Color.RGB atom)
textColor :: forall msg. Color.RGB -> InputProp msg
textColor c props = props { textColor = Just c }

-- | Set input border color (Color.RGB atom)
borderColor :: forall msg. Color.RGB -> InputProp msg
borderColor c props = props { borderColor = Just c }

-- | Set placeholder text color (Color.RGB atom)
placeholderColor :: forall msg. Color.RGB -> InputProp msg
placeholderColor c props = props { placeholderColor = Just c }

-- | Set focus border color (Color.RGB atom)
focusBorderColor :: forall msg. Color.RGB -> InputProp msg
focusBorderColor c props = props { focusBorderColor = Just c }

-- | Set focus ring color (Color.RGB atom)
focusRingColor :: forall msg. Color.RGB -> InputProp msg
focusRingColor c props = props { focusRingColor = Just c }

-- | Set label text color (Color.RGB atom)
labelColor :: forall msg. Color.RGB -> InputProp msg
labelColor c props = props { labelColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set border radius (Geometry.Corners atom)
borderRadius :: forall msg. Geometry.Corners -> InputProp msg
borderRadius r props = props { borderRadius = Just r }

-- | Set border width (Device.Pixel atom)
borderWidth :: forall msg. Device.Pixel -> InputProp msg
borderWidth w props = props { borderWidth = Just w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set input height (Device.Pixel atom)
height :: forall msg. Device.Pixel -> InputProp msg
height h props = props { height = Just h }

-- | Set horizontal padding (Device.Pixel atom)
paddingX :: forall msg. Device.Pixel -> InputProp msg
paddingX p props = props { paddingX = Just p }

-- | Set vertical padding (Device.Pixel atom)
paddingY :: forall msg. Device.Pixel -> InputProp msg
paddingY p props = props { paddingY = Just p }

-- | Set minimum height for textarea (Device.Pixel atom)
minHeight :: forall msg. Device.Pixel -> InputProp msg
minHeight h props = props { minHeight = Just h }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // prop builders: typography
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set font size (FontSize atom)
fontSize :: forall msg. FontSize.FontSize -> InputProp msg
fontSize s props = props { fontSize = Just s }

-- | Set label font size (FontSize atom)
labelFontSize :: forall msg. FontSize.FontSize -> InputProp msg
labelFontSize s props = props { labelFontSize = Just s }

-- | Set label font weight (FontWeight atom)
labelFontWeight :: forall msg. FontWeight.FontWeight -> InputProp msg
labelFontWeight w props = props { labelFontWeight = Just w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // prop builders: motion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set transition duration (Temporal.Milliseconds atom)
transitionDuration :: forall msg. Temporal.Milliseconds -> InputProp msg
transitionDuration d props = props { transitionDuration = Just d }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set input change handler
-- |
-- | Receives the current input value as a String.
onInputChange :: forall msg. (String -> msg) -> InputProp msg
onInputChange handler props = props { onInputChange = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // prop builders: escape hatch
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add extra attributes (escape hatch)
extraAttributes :: forall msg. Array (E.Attribute msg) -> InputProp msg
extraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }
