-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // otpinput // props // color
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | OTPInput Color Props — Builders for color-related properties.
-- |
-- | All colors use Schema.Color.RGB atoms. No CSS strings.
-- | Colors default to Nothing — theme layer provides actual values.

module Hydrogen.Element.Compound.OTPInput.Props.Color
  ( -- * Background Colors
    backgroundColorProp
  , focusBackgroundColorProp
  , hoverBackgroundColorProp
  
  -- * Border Colors
  , borderColorProp
  , focusBorderColorProp
  , hoverBorderColorProp
  , errorBorderColorProp
  , successBorderColorProp
  , filledBorderColorProp
  
  -- * Text Colors
  , textColorProp
  , placeholderColorProp
  , placeholderCharProp
  , errorTextColorProp
  , successTextColorProp
  , mutedTextColorProp
  , labelColorProp
  
  -- * Accent Colors
  , primaryColorProp
  , separatorColorProp
  ) where

import Data.Maybe (Maybe(Just))

import Hydrogen.Element.Compound.OTPInput.Props.Types (OTPInputProp)

import Hydrogen.Schema.Color.RGB as Color

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // background color props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set digit input background color
-- |
-- | Schema.Color.RGB atom — bounded 0-255 channels.
backgroundColorProp :: forall msg. Color.RGB -> OTPInputProp msg
backgroundColorProp c props = props { backgroundColor = Just c }

-- | Set focused digit background color
-- |
-- | Applied when a digit has keyboard focus.
focusBackgroundColorProp :: forall msg. Color.RGB -> OTPInputProp msg
focusBackgroundColorProp c props = props { focusBackgroundColor = Just c }

-- | Set hovered digit background color
-- |
-- | Applied on mouse hover (pointer devices).
hoverBackgroundColorProp :: forall msg. Color.RGB -> OTPInputProp msg
hoverBackgroundColorProp c props = props { hoverBackgroundColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // border color props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set default digit border color
-- |
-- | Applied in idle state.
borderColorProp :: forall msg. Color.RGB -> OTPInputProp msg
borderColorProp c props = props { borderColor = Just c }

-- | Set focused digit border color
-- |
-- | Applied when digit has keyboard focus.
focusBorderColorProp :: forall msg. Color.RGB -> OTPInputProp msg
focusBorderColorProp c props = props { focusBorderColor = Just c }

-- | Set hovered digit border color
-- |
-- | Applied on mouse hover.
hoverBorderColorProp :: forall msg. Color.RGB -> OTPInputProp msg
hoverBorderColorProp c props = props { hoverBorderColor = Just c }

-- | Set error state border color
-- |
-- | Applied when component is in Error state.
errorBorderColorProp :: forall msg. Color.RGB -> OTPInputProp msg
errorBorderColorProp c props = props { errorBorderColor = Just c }

-- | Set success state border color
-- |
-- | Applied when component is in Success state.
successBorderColorProp :: forall msg. Color.RGB -> OTPInputProp msg
successBorderColorProp c props = props { successBorderColor = Just c }

-- | Set filled (has value) digit border color
-- |
-- | Applied to digits that have a character entered.
filledBorderColorProp :: forall msg. Color.RGB -> OTPInputProp msg
filledBorderColorProp c props = props { filledBorderColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // text color props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set digit text color
-- |
-- | Color of the entered digit characters.
textColorProp :: forall msg. Color.RGB -> OTPInputProp msg
textColorProp c props = props { textColor = Just c }

-- | Set placeholder/empty digit color
-- |
-- | Color of the placeholder character in empty digits.
placeholderColorProp :: forall msg. Color.RGB -> OTPInputProp msg
placeholderColorProp c props = props { placeholderColor = Just c }

-- | Set placeholder character (e.g., '-' or bullet)
-- |
-- | Displayed in empty digit slots.
placeholderCharProp :: forall msg. Char -> OTPInputProp msg
placeholderCharProp c props = props { placeholderChar = Just c }

-- | Set error message text color
-- |
-- | Color of the error message below input.
errorTextColorProp :: forall msg. Color.RGB -> OTPInputProp msg
errorTextColorProp c props = props { errorTextColor = Just c }

-- | Set success message text color
-- |
-- | Color of the success message below input.
successTextColorProp :: forall msg. Color.RGB -> OTPInputProp msg
successTextColorProp c props = props { successTextColor = Just c }

-- | Set muted/secondary text color
-- |
-- | Color for help text and secondary labels.
mutedTextColorProp :: forall msg. Color.RGB -> OTPInputProp msg
mutedTextColorProp c props = props { mutedTextColor = Just c }

-- | Set label color (Schema Color.RGB)
-- |
-- | Color of the label text above the input.
labelColorProp :: forall msg. Color.RGB -> OTPInputProp msg
labelColorProp c props = props { labelColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // accent color props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set primary/accent color
-- |
-- | Used for focus rings, active states, links.
primaryColorProp :: forall msg. Color.RGB -> OTPInputProp msg
primaryColorProp c props = props { primaryColor = Just c }

-- | Set separator color (Schema Color.RGB)
-- |
-- | Color of the separator character between digit groups.
separatorColorProp :: forall msg. Color.RGB -> OTPInputProp msg
separatorColorProp c props = props { separatorColor = Just c }
