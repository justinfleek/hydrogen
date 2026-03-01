-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // element // textarea-props
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Textarea Props — Property builder functions for Textarea component.
-- |
-- | All prop builders accept concrete Schema atoms and return property
-- | modifiers that can be composed to configure a textarea.

module Hydrogen.Element.Compound.Textarea.Props
  ( -- * Content Props
    placeholder
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
  
  -- * Error Props
  , textareaError
  , errorMessage
  
  -- * Color Atoms
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
  
  -- * Geometry Atoms
  , borderRadius
  , borderWidth
  
  -- * Dimension Atoms
  , minHeight
  , paddingX
  , paddingY
  
  -- * Typography Atoms
  , fontSize
  , lineHeight
  , labelFontSize
  , labelFontWeight
  , counterFontSize
  
  -- * Motion Atoms
  , transitionDuration
  
  -- * Behavior Props
  , onTextareaInput
  , onTextareaChange
  , onTextareaFocus
  , onTextareaBlur
  
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
import Hydrogen.Schema.Typography.FontWeight as FontWeight
import Hydrogen.Schema.Typography.LineHeight as LineHeight

import Hydrogen.Element.Compound.Textarea.Types (TextareaProp)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // prop builders: content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set placeholder text
placeholder :: forall msg. String -> TextareaProp msg
placeholder p props = props { placeholder = p }

-- | Set current value
textareaValue :: forall msg. String -> TextareaProp msg
textareaValue v props = props { value = v }

-- | Set disabled state
textareaDisabled :: forall msg. Boolean -> TextareaProp msg
textareaDisabled d props = props { disabled = d }

-- | Set read-only state
textareaReadOnly :: forall msg. Boolean -> TextareaProp msg
textareaReadOnly r props = props { readOnly = r }

-- | Set required state
textareaRequired :: forall msg. Boolean -> TextareaProp msg
textareaRequired r props = props { required = r }

-- | Set textarea id
textareaId :: forall msg. String -> TextareaProp msg
textareaId i props = props { id = Just i }

-- | Set textarea name
textareaName :: forall msg. String -> TextareaProp msg
textareaName n props = props { name = Just n }

-- | Set minimum rows
minRows :: forall msg. Int -> TextareaProp msg
minRows r props = props { minRows = r }

-- | Set maximum rows (for auto-resize)
maxRows :: forall msg. Int -> TextareaProp msg
maxRows r props = props { maxRows = r }

-- | Set maximum character length
maxLength :: forall msg. Int -> TextareaProp msg
maxLength l props = props { maxLength = Just l }

-- | Enable auto-resize to content
autoResize :: forall msg. Boolean -> TextareaProp msg
autoResize a props = props { autoResize = a }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: error
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set error state
textareaError :: forall msg. Boolean -> TextareaProp msg
textareaError e props = props { error = e }

-- | Set error message (also sets error state to true)
errorMessage :: forall msg. String -> TextareaProp msg
errorMessage msg props = props { errorMsg = msg, error = true }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set background color (Color.RGB atom)
backgroundColor :: forall msg. Color.RGB -> TextareaProp msg
backgroundColor c props = props { backgroundColor = Just c }

-- | Set text color (Color.RGB atom)
textColor :: forall msg. Color.RGB -> TextareaProp msg
textColor c props = props { textColor = Just c }

-- | Set border color (Color.RGB atom)
borderColor :: forall msg. Color.RGB -> TextareaProp msg
borderColor c props = props { borderColor = Just c }

-- | Set placeholder text color (Color.RGB atom)
placeholderColor :: forall msg. Color.RGB -> TextareaProp msg
placeholderColor c props = props { placeholderColor = Just c }

-- | Set focus border color (Color.RGB atom)
focusBorderColor :: forall msg. Color.RGB -> TextareaProp msg
focusBorderColor c props = props { focusBorderColor = Just c }

-- | Set focus ring color (Color.RGB atom)
focusRingColor :: forall msg. Color.RGB -> TextareaProp msg
focusRingColor c props = props { focusRingColor = Just c }

-- | Set error state border color (Color.RGB atom)
errorBorderColor :: forall msg. Color.RGB -> TextareaProp msg
errorBorderColor c props = props { errorBorderColor = Just c }

-- | Set error message text color (Color.RGB atom)
errorTextColor :: forall msg. Color.RGB -> TextareaProp msg
errorTextColor c props = props { errorTextColor = Just c }

-- | Set label text color (Color.RGB atom)
labelColor :: forall msg. Color.RGB -> TextareaProp msg
labelColor c props = props { labelColor = Just c }

-- | Set counter text color (Color.RGB atom)
counterColor :: forall msg. Color.RGB -> TextareaProp msg
counterColor c props = props { counterColor = Just c }

-- | Set required asterisk color (Color.RGB atom)
requiredColor :: forall msg. Color.RGB -> TextareaProp msg
requiredColor c props = props { requiredColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set border radius (Geometry.Corners atom)
borderRadius :: forall msg. Geometry.Corners -> TextareaProp msg
borderRadius r props = props { borderRadius = Just r }

-- | Set border width (Device.Pixel atom)
borderWidth :: forall msg. Device.Pixel -> TextareaProp msg
borderWidth w props = props { borderWidth = Just w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set minimum height (Device.Pixel atom)
minHeight :: forall msg. Device.Pixel -> TextareaProp msg
minHeight h props = props { minHeight = Just h }

-- | Set horizontal padding (Device.Pixel atom)
paddingX :: forall msg. Device.Pixel -> TextareaProp msg
paddingX p props = props { paddingX = Just p }

-- | Set vertical padding (Device.Pixel atom)
paddingY :: forall msg. Device.Pixel -> TextareaProp msg
paddingY p props = props { paddingY = Just p }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // prop builders: typography
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set font size (FontSize atom)
fontSize :: forall msg. FontSize.FontSize -> TextareaProp msg
fontSize s props = props { fontSize = Just s }

-- | Set line height (LineHeight atom)
lineHeight :: forall msg. LineHeight.LineHeight -> TextareaProp msg
lineHeight h props = props { lineHeight = Just h }

-- | Set label font size (FontSize atom)
labelFontSize :: forall msg. FontSize.FontSize -> TextareaProp msg
labelFontSize s props = props { labelFontSize = Just s }

-- | Set label font weight (FontWeight atom)
labelFontWeight :: forall msg. FontWeight.FontWeight -> TextareaProp msg
labelFontWeight w props = props { labelFontWeight = Just w }

-- | Set counter font size (FontSize atom)
counterFontSize :: forall msg. FontSize.FontSize -> TextareaProp msg
counterFontSize s props = props { counterFontSize = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // prop builders: motion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set transition duration (Temporal.Milliseconds atom)
transitionDuration :: forall msg. Temporal.Milliseconds -> TextareaProp msg
transitionDuration d props = props { transitionDuration = Just d }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set input handler (fires on each keystroke)
-- |
-- | Receives the current textarea value as a String.
onTextareaInput :: forall msg. (String -> msg) -> TextareaProp msg
onTextareaInput handler props = props { onInput = Just handler }

-- | Set change handler (fires on blur after change)
-- |
-- | Receives the current textarea value as a String.
onTextareaChange :: forall msg. (String -> msg) -> TextareaProp msg
onTextareaChange handler props = props { onChange = Just handler }

-- | Set focus handler (fires when textarea receives focus)
onTextareaFocus :: forall msg. msg -> TextareaProp msg
onTextareaFocus handler props = props { onFocus = Just handler }

-- | Set blur handler (fires when textarea loses focus)
onTextareaBlur :: forall msg. msg -> TextareaProp msg
onTextareaBlur handler props = props { onBlur = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // prop builders: escape hatch
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add extra attributes (escape hatch)
extraAttributes :: forall msg. Array (E.Attribute msg) -> TextareaProp msg
extraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }
