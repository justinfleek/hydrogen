-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // element // color picker
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ColorPicker — Schema-native color selection component.
-- |
-- | ## Design Philosophy
-- |
-- | This component is a **compound** of Schema atoms. It composes Slider and
-- | Checkbox sub-components to allow interactive color selection across
-- | multiple color spaces:
-- |
-- | - **HSL**: Hue (0-359), Saturation (0-100), Lightness (0-100)
-- | - **RGB**: Red (0-255), Green (0-255), Blue (0-255)
-- | - **HWB**: Hue (0-359), Whiteness (0-100), Blackness (0-100)
-- | - **OKLAB**: L (0-1), a (-0.4 to 0.4), b (-0.4 to 0.4)
-- | - **OKLCH**: L (0-1), Chroma (0-0.4), Hue (0-359)
-- |
-- | All color math uses the Schema conversion functions, ensuring consistency
-- | across all representations.
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property               | Pillar     | Type                      | CSS Output              |
-- | |------------------------|------------|---------------------------|-------------------------|
-- | | backgroundColor        | Color      | Color.RGB                 | panel background        |
-- | | borderColor            | Color      | Color.RGB                 | panel border            |
-- | | labelColor             | Color      | Color.RGB                 | mode/slider labels      |
-- | | primaryColor           | Color      | Color.RGB                 | accent elements         |
-- | | sliderTrackColor       | Color      | Color.RGB                 | slider track bg         |
-- | | previewBorderRadius    | Geometry   | Geometry.Radius           | color preview rounding  |
-- | | panelBorderRadius      | Geometry   | Geometry.Radius           | panel rounding          |
-- | | padding                | Dimension  | Device.Pixel              | internal padding        |
-- | | gap                    | Dimension  | Device.Pixel              | spacing between sections|
-- | | borderWidth            | Dimension  | Device.Pixel              | panel border width      |
-- | | previewHeight          | Dimension  | Device.Pixel              | color preview height    |
-- | | labelFontSize          | Typography | Typography.FontSize       | label font size         |
-- | | labelFontWeight        | Typography | Typography.FontWeight     | label font weight       |
-- | | headerFontSize         | Typography | Typography.FontSize       | mode header font size   |
-- | | headerFontWeight       | Typography | Typography.FontWeight     | mode header font weight |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.ColorPicker as ColorPicker
-- | import Hydrogen.Schema.Color.RGB as Color
-- |
-- | -- Basic color picker
-- | ColorPicker.colorPicker
-- |   [ ColorPicker.color (Color.rgb 100 150 200)
-- |   , ColorPicker.onChange HandleColorChange
-- |   ]
-- |
-- | -- With enabled modes and brand atoms
-- | ColorPicker.colorPicker
-- |   [ ColorPicker.color state.currentColor
-- |   , ColorPicker.onChange HandleColorChange
-- |   , ColorPicker.enabledModes [ColorPicker.ModeHSL, ColorPicker.ModeRGB]
-- |   , ColorPicker.backgroundColor brand.surfaceColor
-- |   , ColorPicker.primaryColor brand.primaryColor
-- |   ]
-- | ```

module Hydrogen.Element.Compound.ColorPicker
  ( -- * Component
    colorPicker
  
  -- * Re-exports: Props
  , module Hydrogen.Element.Compound.ColorPicker.Props
  
  -- * Re-exports: Types
  , module Hydrogen.Element.Compound.ColorPicker.Types
  ) where

import Prelude
  ( map
  , not
  , show
  , (<>)
  )

import Data.Array (foldl, elem)
import Data.Maybe (Maybe(Nothing, Just))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry

import Hydrogen.Element.Compound.Checkbox as Checkbox
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Typography.FontWeight as FontWeight

import Hydrogen.Element.Compound.ColorPicker.Types
  ( ColorMode(ModeHSL, ModeRGB, ModeHWB, ModeOKLAB, ModeOKLCH)
  , modeName
  , allModes
  )

import Hydrogen.Element.Compound.ColorPicker.Props
  ( ColorPickerProps
  , ColorPickerProp
  , defaultProps
  , color
  , enabledModes
  , backgroundColor
  , borderColor
  , labelColor
  , primaryColor
  , sliderTrackColor
  , previewBorderRadius
  , panelBorderRadius
  , padding
  , gap
  , borderWidth
  , previewHeight
  , labelFontSize
  , labelFontWeight
  , headerFontSize
  , headerFontWeight
  , onChange
  , onModeToggle
  )

import Hydrogen.Element.Compound.ColorPicker.Defaults
  ( ResolvedConfig
  , defaultBackgroundColor
  , defaultBorderColor
  , defaultLabelColor
  , defaultPrimaryColor
  , defaultSliderTrackColor
  , defaultPreviewRadius
  , defaultPanelRadius
  , defaultPadding
  , defaultGap
  , defaultBorderWidth
  , defaultPreviewHeight
  , defaultLabelFontSize
  , defaultLabelFontWeight
  , defaultHeaderFontSize
  , defaultHeaderFontWeight
  , getColor
  , getRadius
  , getPixel
  , getFontSize
  , getFontWeight
  )

import Hydrogen.Element.Compound.ColorPicker.Sliders (renderModeSection)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // main component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a color picker
-- |
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
colorPicker :: forall msg. Array (ColorPickerProp msg) -> E.Element msg
colorPicker propMods =
  let
    -- Apply prop modifiers, ensuring enabledModes defaults to allModes
    baseProps = defaultProps { enabledModes = allModes }
    props = foldl (\p f -> f p) baseProps propMods
    
    -- Resolve colors
    bgColor = getColor props.backgroundColor defaultBackgroundColor
    brdColor = getColor props.borderColor defaultBorderColor
    lblColor = getColor props.labelColor defaultLabelColor
    primColor = getColor props.primaryColor defaultPrimaryColor
    trkColor = getColor props.sliderTrackColor defaultSliderTrackColor
    
    -- Resolve geometry
    prevRadius = getRadius props.previewBorderRadius defaultPreviewRadius
    pnlRadius = getRadius props.panelBorderRadius defaultPanelRadius
    
    -- Resolve dimensions
    pad = getPixel props.padding defaultPadding
    gapVal = getPixel props.gap defaultGap
    brdWidth = getPixel props.borderWidth defaultBorderWidth
    prevHeight = getPixel props.previewHeight defaultPreviewHeight
    
    -- Resolve typography
    lblFontSz = getFontSize props.labelFontSize defaultLabelFontSize
    lblFontWt = getFontWeight props.labelFontWeight defaultLabelFontWeight
    hdrFontSz = getFontSize props.headerFontSize defaultHeaderFontSize
    hdrFontWt = getFontWeight props.headerFontWeight defaultHeaderFontWeight
    
    -- Container styles
    containerStyles =
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" (show gapVal)
      , E.style "padding" (show pad)
      , E.style "background-color" (Color.toLegacyCss bgColor)
      , E.style "border-width" (show brdWidth)
      , E.style "border-style" "solid"
      , E.style "border-color" (Color.toLegacyCss brdColor)
      , E.style "border-radius" (Geometry.toLegacyCss pnlRadius)
      ]
    
    -- Resolved config for render functions
    resolvedConfig =
      { lblColor
      , primColor
      , trkColor
      , lblFontSize: lblFontSz
      , lblFontWeight: lblFontWt
      , hdrFontSize: hdrFontSz
      , hdrFontWeight: hdrFontWt
      }
  in
    E.div_
      containerStyles
      [ -- Color preview
        renderColorPreview props.color prevRadius prevHeight brdColor brdWidth
      
      -- Mode toggles
      , renderModeToggles props resolvedConfig
      
      -- Enabled mode sections
      , E.div_
          [ E.style "display" "flex"
          , E.style "flex-direction" "column"
          , E.style "gap" (show gapVal)
          ]
          ( map (renderModeSection props resolvedConfig) props.enabledModes )
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // color preview
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render color preview swatch
renderColorPreview :: forall msg. Color.RGB -> Geometry.Radius -> Device.Pixel -> Color.RGB -> Device.Pixel -> E.Element msg
renderColorPreview currentColor radius height borderClr borderWdth =
  E.div_
    [ E.style "width" "100%"
    , E.style "height" (show height)
    , E.style "background-color" (Color.toLegacyCss currentColor)
    , E.style "border-radius" (Geometry.toLegacyCss radius)
    , E.style "border-width" (show borderWdth)
    , E.style "border-style" "solid"
    , E.style "border-color" (Color.toLegacyCss borderClr)
    ]
    []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // mode toggles
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render mode toggle checkboxes
renderModeToggles :: forall msg. ColorPickerProps msg -> ResolvedConfig -> E.Element msg
renderModeToggles props cfg =
  E.div_
    [ E.style "display" "flex"
    , E.style "flex-wrap" "wrap"
    , E.style "gap" "12px"
    , E.style "padding-bottom" "8px"
    , E.style "border-bottom" "1px solid rgba(255, 255, 255, 0.1)"
    ]
    ( map (renderModeCheckbox props cfg) allModes )

-- | Render a single mode checkbox
renderModeCheckbox :: forall msg. ColorPickerProps msg -> ResolvedConfig -> ColorMode -> E.Element msg
renderModeCheckbox props cfg mode =
  let
    isEnabled = elem mode props.enabledModes
    
    toggleHandler = case props.onModeToggle of
      Just handler -> Just (handler mode (not isEnabled))
      Nothing -> Nothing
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "align-items" "center"
      , E.style "gap" "8px"
      ]
      [ Checkbox.checkbox
          ( [ Checkbox.isChecked isEnabled
            , Checkbox.backgroundColor cfg.primColor
            , Checkbox.checkColor (Color.rgb 255 255 255)
            , Checkbox.size (Device.px 16.0)
            ] <> case toggleHandler of
                    Just h -> [ Checkbox.onToggle h ]
                    Nothing -> [ Checkbox.isDisabled true ]
          )
      , E.span_
          [ E.style "font-size" (show cfg.hdrFontSize)
          , E.style "font-weight" (FontWeight.toLegacyCss cfg.lblFontWeight)
          , E.style "color" (Color.toLegacyCss cfg.lblColor)
          ]
          [ E.text (modeName mode) ]
      ]
