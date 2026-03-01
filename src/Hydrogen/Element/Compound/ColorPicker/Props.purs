-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // element // color picker // props
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ColorPicker Props — Property types and builder functions.
-- |
-- | This module defines the props record type and all prop builder functions
-- | for configuring the ColorPicker component.

module Hydrogen.Element.Compound.ColorPicker.Props
  ( -- * Props Type
    ColorPickerProps
  , ColorPickerProp
  , defaultProps
  
  -- * State Props
  , color
  , enabledModes
  
  -- * Color Atoms
  , backgroundColor
  , borderColor
  , labelColor
  , primaryColor
  , sliderTrackColor
  
  -- * Geometry Atoms
  , previewBorderRadius
  , panelBorderRadius
  
  -- * Dimension Atoms
  , padding
  , gap
  , borderWidth
  , previewHeight
  
  -- * Typography Atoms
  , labelFontSize
  , labelFontWeight
  , headerFontSize
  , headerFontWeight
  
  -- * Behavior Props
  , onChange
  , onModeToggle
  ) where

import Data.Maybe (Maybe(Nothing, Just))

import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Typography.FontWeight as FontWeight

import Hydrogen.Element.Compound.ColorPicker.Types (ColorMode)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // props type
-- ═════════════════════════════════════════════════════════════════════════════

-- | ColorPicker properties
-- |
-- | All visual properties accept Schema atoms directly.
type ColorPickerProps msg =
  { -- State
    color :: Color.RGB
  , enabledModes :: Array ColorMode
  
  -- Color atoms
  , backgroundColor :: Maybe Color.RGB
  , borderColor :: Maybe Color.RGB
  , labelColor :: Maybe Color.RGB
  , primaryColor :: Maybe Color.RGB
  , sliderTrackColor :: Maybe Color.RGB
  
  -- Geometry atoms
  , previewBorderRadius :: Maybe Geometry.Radius
  , panelBorderRadius :: Maybe Geometry.Radius
  
  -- Dimension atoms
  , padding :: Maybe Device.Pixel
  , gap :: Maybe Device.Pixel
  , borderWidth :: Maybe Device.Pixel
  , previewHeight :: Maybe Device.Pixel
  
  -- Typography atoms
  , labelFontSize :: Maybe FontSize.FontSize
  , labelFontWeight :: Maybe FontWeight.FontWeight
  , headerFontSize :: Maybe FontSize.FontSize
  , headerFontWeight :: Maybe FontWeight.FontWeight
  
  -- Behavior
  , onChange :: Maybe (Color.RGB -> msg)
  , onModeToggle :: Maybe (ColorMode -> Boolean -> msg)
  }

-- | Property modifier function
type ColorPickerProp msg = ColorPickerProps msg -> ColorPickerProps msg

-- | Default properties
defaultProps :: forall msg. ColorPickerProps msg
defaultProps =
  { color: Color.rgb 128 128 128
  , enabledModes: [ ]  -- Will be set to allModes by leader module
  , backgroundColor: Nothing
  , borderColor: Nothing
  , labelColor: Nothing
  , primaryColor: Nothing
  , sliderTrackColor: Nothing
  , previewBorderRadius: Nothing
  , panelBorderRadius: Nothing
  , padding: Nothing
  , gap: Nothing
  , borderWidth: Nothing
  , previewHeight: Nothing
  , labelFontSize: Nothing
  , labelFontWeight: Nothing
  , headerFontSize: Nothing
  , headerFontWeight: Nothing
  , onChange: Nothing
  , onModeToggle: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set current color
color :: forall msg. Color.RGB -> ColorPickerProp msg
color c props = props { color = c }

-- | Set which color modes are enabled
enabledModes :: forall msg. Array ColorMode -> ColorPickerProp msg
enabledModes modes props = props { enabledModes = modes }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set panel background color (Color.RGB atom)
backgroundColor :: forall msg. Color.RGB -> ColorPickerProp msg
backgroundColor c props = props { backgroundColor = Just c }

-- | Set panel border color (Color.RGB atom)
borderColor :: forall msg. Color.RGB -> ColorPickerProp msg
borderColor c props = props { borderColor = Just c }

-- | Set label text color (Color.RGB atom)
labelColor :: forall msg. Color.RGB -> ColorPickerProp msg
labelColor c props = props { labelColor = Just c }

-- | Set primary/accent color (Color.RGB atom)
primaryColor :: forall msg. Color.RGB -> ColorPickerProp msg
primaryColor c props = props { primaryColor = Just c }

-- | Set slider track color (Color.RGB atom)
sliderTrackColor :: forall msg. Color.RGB -> ColorPickerProp msg
sliderTrackColor c props = props { sliderTrackColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set color preview border radius (Geometry.Radius atom)
previewBorderRadius :: forall msg. Geometry.Radius -> ColorPickerProp msg
previewBorderRadius r props = props { previewBorderRadius = Just r }

-- | Set panel border radius (Geometry.Radius atom)
panelBorderRadius :: forall msg. Geometry.Radius -> ColorPickerProp msg
panelBorderRadius r props = props { panelBorderRadius = Just r }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set internal padding (Device.Pixel atom)
padding :: forall msg. Device.Pixel -> ColorPickerProp msg
padding p props = props { padding = Just p }

-- | Set gap between sections (Device.Pixel atom)
gap :: forall msg. Device.Pixel -> ColorPickerProp msg
gap g props = props { gap = Just g }

-- | Set panel border width (Device.Pixel atom)
borderWidth :: forall msg. Device.Pixel -> ColorPickerProp msg
borderWidth w props = props { borderWidth = Just w }

-- | Set color preview height (Device.Pixel atom)
previewHeight :: forall msg. Device.Pixel -> ColorPickerProp msg
previewHeight h props = props { previewHeight = Just h }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // prop builders: typography
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set label font size (Typography.FontSize atom)
labelFontSize :: forall msg. FontSize.FontSize -> ColorPickerProp msg
labelFontSize s props = props { labelFontSize = Just s }

-- | Set label font weight (Typography.FontWeight atom)
labelFontWeight :: forall msg. FontWeight.FontWeight -> ColorPickerProp msg
labelFontWeight w props = props { labelFontWeight = Just w }

-- | Set mode header font size (Typography.FontSize atom)
headerFontSize :: forall msg. FontSize.FontSize -> ColorPickerProp msg
headerFontSize s props = props { headerFontSize = Just s }

-- | Set mode header font weight (Typography.FontWeight atom)
headerFontWeight :: forall msg. FontWeight.FontWeight -> ColorPickerProp msg
headerFontWeight w props = props { headerFontWeight = Just w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set color change handler
onChange :: forall msg. (Color.RGB -> msg) -> ColorPickerProp msg
onChange handler props = props { onChange = Just handler }

-- | Set mode toggle handler
onModeToggle :: forall msg. (ColorMode -> Boolean -> msg) -> ColorPickerProp msg
onModeToggle handler props = props { onModeToggle = Just handler }
