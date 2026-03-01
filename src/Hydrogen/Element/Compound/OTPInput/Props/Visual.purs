-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // otpinput // props // visual
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | OTPInput Visual Props — Builders for visual appearance properties.
-- |
-- | Visual props control:
-- | - Gradients (Schema.Color.Gradient)
-- | - Elevation/Shadows (Schema.Elevation.Shadow)
-- | - Geometry (Schema.Geometry: Radius, Transform)
-- | - Dimensions (Schema.Dimension.Device: Pixel)
-- | - Typography (Schema.Typography: FontSize, FontWeight, FontFamily)

module Hydrogen.Element.Compound.OTPInput.Props.Visual
  ( -- * Gradient Props
    backgroundGradientProp
  , focusBackgroundGradientProp
  
  -- * Elevation/Shadow Props
  , shadowProp
  , focusShadowProp
  , hoverShadowProp
  , errorShadowProp
  , successShadowProp
  
  -- * Geometry Props
  , borderRadiusProp
  , borderWidthProp
  , focusScaleProp
  , hoverScaleProp
  , pressScaleProp
  
  -- * Dimension Props
  , digitWidthProp
  , digitHeightProp
  , gapProp
  , separatorWidthProp
  
  -- * Typography Props
  , fontSizeProp
  , fontWeightProp
  , fontFamilyProp
  , letterSpacingProp
  
  -- * Cursor Props
  , cursorStyleProp
  ) where

import Data.Maybe (Maybe(Just))

import Hydrogen.Element.Compound.OTPInput.Props.Types (OTPInputProp)

import Hydrogen.Schema.Color.Gradient as Gradient
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Geometry.Transform as Transform
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Elevation.Shadow as Shadow
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Typography.FontWeight as FontWeight
import Hydrogen.Schema.Typography.FontFamily as FontFamily

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // gradient prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set background gradient (takes precedence over solid color)
-- |
-- | Schema.Color.Gradient atom — linear, radial, or conic gradients.
backgroundGradientProp :: forall msg. Gradient.Gradient -> OTPInputProp msg
backgroundGradientProp g props = props { backgroundGradient = Just g }

-- | Set focused digit background gradient
-- |
-- | Applied when digit has keyboard focus.
focusBackgroundGradientProp :: forall msg. Gradient.Gradient -> OTPInputProp msg
focusBackgroundGradientProp g props = props { focusBackgroundGradient = Just g }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // elevation prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set digit box shadow
-- |
-- | Schema.Elevation.Shadow.LayeredShadow — multiple shadow layers.
shadowProp :: forall msg. Shadow.LayeredShadow -> OTPInputProp msg
shadowProp s props = props { shadow = Just s }

-- | Set focused digit box shadow (focus ring effect)
-- |
-- | Applied when digit has keyboard focus.
focusShadowProp :: forall msg. Shadow.LayeredShadow -> OTPInputProp msg
focusShadowProp s props = props { focusShadow = Just s }

-- | Set hovered digit box shadow
-- |
-- | Applied on mouse hover.
hoverShadowProp :: forall msg. Shadow.LayeredShadow -> OTPInputProp msg
hoverShadowProp s props = props { hoverShadow = Just s }

-- | Set error state box shadow (red glow)
-- |
-- | Applied when component is in Error state.
errorShadowProp :: forall msg. Shadow.LayeredShadow -> OTPInputProp msg
errorShadowProp s props = props { errorShadow = Just s }

-- | Set success state box shadow (green glow)
-- |
-- | Applied when component is in Success state.
successShadowProp :: forall msg. Shadow.LayeredShadow -> OTPInputProp msg
successShadowProp s props = props { successShadow = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // geometry prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set digit border radius
-- |
-- | Schema.Geometry.Radius — uniform or per-corner radii.
borderRadiusProp :: forall msg. Geometry.Radius -> OTPInputProp msg
borderRadiusProp r props = props { borderRadius = Just r }

-- | Set digit border width
-- |
-- | Schema.Dimension.Device.Pixel — bounded pixel value.
borderWidthProp :: forall msg. Device.Pixel -> OTPInputProp msg
borderWidthProp w props = props { borderWidth = Just w }

-- | Set focused digit scale transform
-- |
-- | Schema.Geometry.Transform.Scale — slight enlargement on focus.
focusScaleProp :: forall msg. Transform.Scale -> OTPInputProp msg
focusScaleProp s props = props { focusScale = Just s }

-- | Set hovered digit scale transform
-- |
-- | Slight enlargement on mouse hover.
hoverScaleProp :: forall msg. Transform.Scale -> OTPInputProp msg
hoverScaleProp s props = props { hoverScale = Just s }

-- | Set pressed digit scale transform
-- |
-- | Slight shrink on click/tap for tactile feedback.
pressScaleProp :: forall msg. Transform.Scale -> OTPInputProp msg
pressScaleProp s props = props { pressScale = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // dimension prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set digit input width
-- |
-- | Schema.Dimension.Device.Pixel — bounded pixel value.
digitWidthProp :: forall msg. Device.Pixel -> OTPInputProp msg
digitWidthProp w props = props { digitWidth = Just w }

-- | Set digit input height
-- |
-- | Typically matches or slightly exceeds width for square appearance.
digitHeightProp :: forall msg. Device.Pixel -> OTPInputProp msg
digitHeightProp h props = props { digitHeight = Just h }

-- | Set gap between digit inputs
-- |
-- | Space between adjacent digit boxes.
gapProp :: forall msg. Device.Pixel -> OTPInputProp msg
gapProp g props = props { gap = Just g }

-- | Set separator element width
-- |
-- | Width of the separator character container.
separatorWidthProp :: forall msg. Device.Pixel -> OTPInputProp msg
separatorWidthProp w props = props { separatorWidth = Just w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // typography prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set digit font size
-- |
-- | Schema.Typography.FontSize — bounded scale values.
fontSizeProp :: forall msg. FontSize.FontSize -> OTPInputProp msg
fontSizeProp s props = props { fontSize = Just s }

-- | Set digit font weight (Schema.Typography.FontWeight)
-- |
-- | 100-900 in 100 increments.
fontWeightProp :: forall msg. FontWeight.FontWeight -> OTPInputProp msg
fontWeightProp w props = props { fontWeight = Just w }

-- | Set digit font family
-- |
-- | Schema.Typography.FontFamily — system fonts or custom.
fontFamilyProp :: forall msg. FontFamily.FontFamily -> OTPInputProp msg
fontFamilyProp f props = props { fontFamily = Just f }

-- | Set digit letter spacing
-- |
-- | Additional spacing between characters (usually 0 for OTP).
letterSpacingProp :: forall msg. Device.Pixel -> OTPInputProp msg
letterSpacingProp s props = props { letterSpacing = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // cursor prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set cursor style (text, pointer, not-allowed)
-- |
-- | Controls the mouse cursor appearance over the input.
cursorStyleProp :: forall msg. String -> OTPInputProp msg
cursorStyleProp style props = props { cursorStyle = style }
