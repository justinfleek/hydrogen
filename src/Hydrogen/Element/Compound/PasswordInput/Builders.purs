-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // element // password-input //
--                                                                     builders
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Property builder functions for PasswordInput.
-- |
-- | These functions modify PasswordInputProps to set various attributes,
-- | styles, and event handlers. All visual properties accept concrete
-- | Schema atoms from the 12 pillars.

module Hydrogen.Element.Compound.PasswordInput.Builders
  ( -- * Content Props
    passwordValue
  , passwordVisible
  , showToggle
  , showStrength
  , placeholder
  , passwordDisabled
  , passwordRequired
  , autoComplete
  , passwordMinLength
  , passwordMaxLength
  , passwordId
  , passwordName
  , passwordAriaLabel
  
  -- * Color Atoms
  , backgroundColor
  , textColor
  , borderColor
  , placeholderColor
  , focusBorderColor
  , focusRingColor
  , toggleButtonColor
  , strengthVeryWeakColor
  , strengthWeakColor
  , strengthFairColor
  , strengthStrongColor
  , strengthVeryStrongColor
  , strengthLabelColor
  , strengthBarBgColor
  
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
  , strengthLabelFontSize
  
  -- * Motion Atoms
  , transitionDuration
  
  -- * Behavior Props
  , onPasswordInput
  , onPasswordChange
  , onToggle
  , onPasswordFocus
  , onPasswordBlur
  
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

import Hydrogen.Element.Compound.PasswordInput.Props (PasswordInputProp)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // prop builders: content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set current password value
passwordValue :: forall msg. String -> PasswordInputProp msg
passwordValue v props = props { value = v }

-- | Set visibility state (true = show password as text)
passwordVisible :: forall msg. Boolean -> PasswordInputProp msg
passwordVisible v props = props { visible = v }

-- | Show visibility toggle button
showToggle :: forall msg. Boolean -> PasswordInputProp msg
showToggle s props = props { showToggle = s }

-- | Show password strength indicator
showStrength :: forall msg. Boolean -> PasswordInputProp msg
showStrength s props = props { showStrength = s }

-- | Set placeholder text
placeholder :: forall msg. String -> PasswordInputProp msg
placeholder p props = props { placeholder = p }

-- | Set disabled state
passwordDisabled :: forall msg. Boolean -> PasswordInputProp msg
passwordDisabled d props = props { disabled = d }

-- | Set required state
passwordRequired :: forall msg. Boolean -> PasswordInputProp msg
passwordRequired r props = props { required = r }

-- | Set autocomplete attribute
-- |
-- | Common values: "current-password", "new-password"
autoComplete :: forall msg. String -> PasswordInputProp msg
autoComplete a props = props { autoComplete = a }

-- | Set minimum password length
passwordMinLength :: forall msg. Int -> PasswordInputProp msg
passwordMinLength m props = props { minLength = Just m }

-- | Set maximum password length
passwordMaxLength :: forall msg. Int -> PasswordInputProp msg
passwordMaxLength m props = props { maxLength = Just m }

-- | Set input id
passwordId :: forall msg. String -> PasswordInputProp msg
passwordId i props = props { id = Just i }

-- | Set input name
passwordName :: forall msg. String -> PasswordInputProp msg
passwordName n props = props { name = Just n }

-- | Set aria-label
passwordAriaLabel :: forall msg. String -> PasswordInputProp msg
passwordAriaLabel l props = props { ariaLabel = Just l }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set background color (Color.RGB atom)
backgroundColor :: forall msg. Color.RGB -> PasswordInputProp msg
backgroundColor c props = props { backgroundColor = Just c }

-- | Set text color (Color.RGB atom)
textColor :: forall msg. Color.RGB -> PasswordInputProp msg
textColor c props = props { textColor = Just c }

-- | Set border color (Color.RGB atom)
borderColor :: forall msg. Color.RGB -> PasswordInputProp msg
borderColor c props = props { borderColor = Just c }

-- | Set placeholder text color (Color.RGB atom)
placeholderColor :: forall msg. Color.RGB -> PasswordInputProp msg
placeholderColor c props = props { placeholderColor = Just c }

-- | Set focus border color (Color.RGB atom)
focusBorderColor :: forall msg. Color.RGB -> PasswordInputProp msg
focusBorderColor c props = props { focusBorderColor = Just c }

-- | Set focus ring color (Color.RGB atom)
focusRingColor :: forall msg. Color.RGB -> PasswordInputProp msg
focusRingColor c props = props { focusRingColor = Just c }

-- | Set toggle button icon color (Color.RGB atom)
toggleButtonColor :: forall msg. Color.RGB -> PasswordInputProp msg
toggleButtonColor c props = props { toggleButtonColor = Just c }

-- | Set "Very Weak" strength bar color (Color.RGB atom)
strengthVeryWeakColor :: forall msg. Color.RGB -> PasswordInputProp msg
strengthVeryWeakColor c props = props { strengthVeryWeakColor = Just c }

-- | Set "Weak" strength bar color (Color.RGB atom)
strengthWeakColor :: forall msg. Color.RGB -> PasswordInputProp msg
strengthWeakColor c props = props { strengthWeakColor = Just c }

-- | Set "Fair" strength bar color (Color.RGB atom)
strengthFairColor :: forall msg. Color.RGB -> PasswordInputProp msg
strengthFairColor c props = props { strengthFairColor = Just c }

-- | Set "Strong" strength bar color (Color.RGB atom)
strengthStrongColor :: forall msg. Color.RGB -> PasswordInputProp msg
strengthStrongColor c props = props { strengthStrongColor = Just c }

-- | Set "Very Strong" strength bar color (Color.RGB atom)
strengthVeryStrongColor :: forall msg. Color.RGB -> PasswordInputProp msg
strengthVeryStrongColor c props = props { strengthVeryStrongColor = Just c }

-- | Set strength label text color (Color.RGB atom)
strengthLabelColor :: forall msg. Color.RGB -> PasswordInputProp msg
strengthLabelColor c props = props { strengthLabelColor = Just c }

-- | Set strength bar background color (Color.RGB atom)
strengthBarBgColor :: forall msg. Color.RGB -> PasswordInputProp msg
strengthBarBgColor c props = props { strengthBarBgColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set border radius (Geometry.Corners atom)
borderRadius :: forall msg. Geometry.Corners -> PasswordInputProp msg
borderRadius r props = props { borderRadius = Just r }

-- | Set border width (Device.Pixel atom)
borderWidth :: forall msg. Device.Pixel -> PasswordInputProp msg
borderWidth w props = props { borderWidth = Just w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set input height (Device.Pixel atom)
height :: forall msg. Device.Pixel -> PasswordInputProp msg
height h props = props { height = Just h }

-- | Set horizontal padding (Device.Pixel atom)
paddingX :: forall msg. Device.Pixel -> PasswordInputProp msg
paddingX p props = props { paddingX = Just p }

-- | Set vertical padding (Device.Pixel atom)
paddingY :: forall msg. Device.Pixel -> PasswordInputProp msg
paddingY p props = props { paddingY = Just p }

-- | Set toggle icon size (Device.Pixel atom)
iconSize :: forall msg. Device.Pixel -> PasswordInputProp msg
iconSize s props = props { iconSize = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // prop builders: typography
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set font size (FontSize atom)
fontSize :: forall msg. FontSize.FontSize -> PasswordInputProp msg
fontSize s props = props { fontSize = Just s }

-- | Set strength label font size (FontSize atom)
strengthLabelFontSize :: forall msg. FontSize.FontSize -> PasswordInputProp msg
strengthLabelFontSize s props = props { strengthLabelFontSize = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // prop builders: motion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set transition duration (Temporal.Milliseconds atom)
transitionDuration :: forall msg. Temporal.Milliseconds -> PasswordInputProp msg
transitionDuration d props = props { transitionDuration = Just d }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set input handler (fires on each keystroke)
-- |
-- | Receives the current input value as a String.
onPasswordInput :: forall msg. (String -> msg) -> PasswordInputProp msg
onPasswordInput handler props = props { onInput = Just handler }

-- | Set change handler (fires on blur after change)
-- |
-- | Receives the current input value as a String.
onPasswordChange :: forall msg. (String -> msg) -> PasswordInputProp msg
onPasswordChange handler props = props { onChange = Just handler }

-- | Set toggle visibility handler
onToggle :: forall msg. msg -> PasswordInputProp msg
onToggle handler props = props { onToggle = Just handler }

-- | Set focus handler
onPasswordFocus :: forall msg. msg -> PasswordInputProp msg
onPasswordFocus handler props = props { onFocus = Just handler }

-- | Set blur handler
onPasswordBlur :: forall msg. msg -> PasswordInputProp msg
onPasswordBlur handler props = props { onBlur = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // prop builders: escape hatch
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add extra attributes (escape hatch)
extraAttributes :: forall msg. Array (E.Attribute msg) -> PasswordInputProp msg
extraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }
