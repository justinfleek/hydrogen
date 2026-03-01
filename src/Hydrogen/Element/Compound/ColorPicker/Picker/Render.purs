-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // colorpicker // picker // render
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Render functions for the ColorPicker component.
-- |
-- | This module contains the main component and section renderers:
-- | - `colorPicker`: Main component entry point
-- | - Section renderers for header, tabs, modes, etc.

module Hydrogen.Element.Compound.ColorPicker.Picker.Render
  ( -- * Component
    colorPicker
  
  -- * Section Renders
  , renderHeader
  , renderTabBar
  , renderTab
  , renderMainArea
  , renderWheelMode
  , renderSwatchMode
  , renderHarmonyMode
  , renderAlphaSection
  , renderInputSection
  , renderContrastSection
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , ($)
  , (<>)
  , (==)
  , (&&)
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Color.HSL as HSL
import Hydrogen.Schema.Color.Opacity as Opacity
import Hydrogen.Schema.Color.Channel as Channel
import Hydrogen.Schema.Color.Conversion as Convert
import Hydrogen.Schema.Dimension.Device as Device

-- Sub-components
import Hydrogen.Element.Compound.ColorPicker.Wheel as Wheel
import Hydrogen.Element.Compound.ColorPicker.Panel as Panel
import Hydrogen.Element.Compound.ColorPicker.Input as Input
import Hydrogen.Element.Compound.ColorPicker.Preview as Preview
import Hydrogen.Element.Compound.ColorPicker.Swatches as Swatches
import Hydrogen.Element.Compound.ColorPicker.Harmony as Harmony
import Hydrogen.Element.Compound.ColorPicker.Contrast as Contrast
import Hydrogen.Element.Compound.ColorPicker.Alpha as Alpha
import Hydrogen.Element.Compound.ColorPicker.Magnifier as Magnifier
import Hydrogen.Element.Compound.ColorPicker.Eyedropper as Eyedropper

-- Local modules
import Hydrogen.Element.Compound.ColorPicker.Picker.Types 
  ( PickerTab(TabWheel, TabSliders, TabSwatches, TabHarmony)
  , PickerMsg(SetColor, SetHue, SetSaturation, SetOpacity, SetTab, SelectSwatch, SelectHarmony, CopyValue, ActivateEyedropper)
  )
import Hydrogen.Element.Compound.ColorPicker.Picker.Props (PickerProps, defaultPickerProps)
import Hydrogen.Element.Compound.ColorPicker.Picker.State (PickerState, rgbaToHsl)
import Hydrogen.Element.Compound.ColorPicker.Picker.Sliders (renderSliderMode)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render the ULTIMATE color picker
-- |
-- | This composes all sub-components into a unified interface.
-- | State management is external - this is a pure view function.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | colorPicker state
-- |   [ onMsg MyPickerMsg        -- Required for interactivity
-- |   , onChange MyColorChanged  -- Optional final color callback
-- |   , showAlpha true
-- |   ]
-- | ```
colorPicker :: forall msg. PickerState -> Array (PickerProps msg -> PickerProps msg) -> E.Element msg
colorPicker state propModifiers =
  let
    props = foldl (\p f -> f p) defaultPickerProps propModifiers
    
    widthPx = show (Device.unwrapPixel props.pickerWidth) <> "px"
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "16px"
      , E.style "width" widthPx
      , E.style "padding" "16px"
      , E.style "background" "#fff"
      , E.style "border-radius" "12px"
      , E.style "box-shadow" "0 4px 24px rgba(0,0,0,0.15)"
      , E.style "font-family" "-apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif"
      ]
      [ -- Header with eyedropper
        renderHeader props state
        
        -- Tab bar
      , renderTabBar props state.activeTab
        
        -- Main picking area (based on active tab)
      , renderMainArea props state
        
        -- Alpha slider (if enabled)
      , if props.showAlpha
          then renderAlphaSection props state
          else E.span_ [] []
        
        -- Input fields (if enabled)
      , if props.showInputs
          then renderInputSection props state
          else E.span_ [] []
        
        -- Preview section
      , if props.showPreview
          then 
            let
              previewHandlers = case props.onMsg of
                Just toMsg ->
                  [ Preview.onCopyHex $ \hex -> toMsg (CopyValue hex)
                  , Preview.onCopyRgb $ \rgbStr -> toMsg (CopyValue rgbStr)
                  , Preview.onCopyHsl $ \hslStr -> toMsg (CopyValue hslStr)
                  ]
                Nothing -> []
            in
              Preview.colorPreview
                (previewHandlers <>
                [ Preview.currentColor state.currentColor
                , Preview.originalColor state.originalColor
                ])
          else E.span_ [] []
        
        -- Contrast checker (if enabled)
      , if props.showContrast
          then renderContrastSection state
          else E.span_ [] []
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // section renders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render header with eyedropper button
renderHeader :: forall msg. PickerProps msg -> PickerState -> E.Element msg
renderHeader props _state =
  E.div_
    [ E.style "display" "flex"
    , E.style "justify-content" "space-between"
    , E.style "align-items" "center"
    ]
    [ E.span_
        [ E.style "font-size" "14px"
        , E.style "font-weight" "600"
        , E.style "color" "#374151"
        ]
        [ E.text "Color Picker" ]
    
    , if props.showEyedropper
        then 
          let
            eyedropperHandlers = case props.onMsg of
              Just toMsg -> [ Eyedropper.onActivate (toMsg ActivateEyedropper) ]
              Nothing -> []
          in
            Eyedropper.eyedropperButton eyedropperHandlers
        else E.span_ [] []
    ]

-- | Render tab bar
renderTabBar :: forall msg. PickerProps msg -> PickerTab -> E.Element msg
renderTabBar props activeTab =
  E.div_
    [ E.style "display" "flex"
    , E.style "gap" "4px"
    , E.style "padding" "4px"
    , E.style "background" "#f3f4f6"
    , E.style "border-radius" "8px"
    ]
    [ renderTab props TabWheel activeTab
    , renderTab props TabSliders activeTab
    , renderTab props TabSwatches activeTab
    , renderTab props TabHarmony activeTab
    ]

-- | Render a single tab
renderTab :: forall msg. PickerProps msg -> PickerTab -> PickerTab -> E.Element msg
renderTab props tab activeTab =
  let
    isActive = tab == activeTab
    bgColor = if isActive then "#fff" else "transparent"
    textColor = if isActive then "#374151" else "#6b7280"
    shadow = if isActive then "0 1px 3px rgba(0,0,0,0.1)" else "none"
    
    -- Wire click handler if onMsg is provided
    clickAttr = case props.onMsg of
      Just toMsg -> [ E.onClick (toMsg (SetTab tab)) ]
      Nothing -> []
  in
    E.button_
      (clickAttr <>
      [ E.style "flex" "1"
      , E.style "padding" "8px 12px"
      , E.style "font-size" "12px"
      , E.style "font-weight" "500"
      , E.style "background" bgColor
      , E.style "color" textColor
      , E.style "border" "none"
      , E.style "border-radius" "6px"
      , E.style "cursor" "pointer"
      , E.style "box-shadow" shadow
      , E.style "transition" "all 0.15s"
      ])
      [ E.text (show tab) ]

-- | Render main picking area based on active tab
renderMainArea :: forall msg. PickerProps msg -> PickerState -> E.Element msg
renderMainArea props state =
  case state.activeTab of
    TabWheel -> renderWheelMode props state
    TabSliders -> renderSliderMode props state
    TabSwatches -> renderSwatchMode props
    TabHarmony -> renderHarmonyMode props state

-- | Render wheel mode (wheel + panel + magnifier)
renderWheelMode :: forall msg. PickerProps msg -> PickerState -> E.Element msg
renderWheelMode props state =
  let
    -- Extract HSL from current color
    currentHsl = rgbaToHsl state.currentColor
    currentHue = HSL.hue currentHsl
    currentSat = HSL.saturation currentHsl
    currentLight = HSL.lightness currentHsl
    
    -- Wire handlers if onMsg is provided
    wheelHandlers = case props.onMsg of
      Just toMsg -> 
        [ Wheel.onHueChange $ \h -> toMsg (SetHue h) ]
      Nothing -> []
    
    panelHandlers = case props.onMsg of
      Just toMsg ->
        [ Panel.onChange $ \change -> toMsg (SetSaturation change.saturation) ]
      Nothing -> []
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "gap" "12px"
      ]
      [ -- Hue wheel for selecting hue angle
        Wheel.colorWheel
          (wheelHandlers <>
          [ Wheel.hue currentHue
          , Wheel.size (Device.px 180.0)
          ])
        
        -- Panel (saturation/brightness)
      , Panel.saturationPanel
          (panelHandlers <>
          [ Panel.hue currentHue
          , Panel.saturation currentSat
          , Panel.brightness currentLight
          ])
        
        -- Magnifier (if enabled and active)
      , if props.showMagnifier && state.magnifierActive
          then Magnifier.magnifier
              [ Magnifier.cursorX state.cursorX
              , Magnifier.cursorY state.cursorY
              ]
          else E.span_ [] []
      ]

-- | Render swatch palette mode
renderSwatchMode :: forall msg. PickerProps msg -> E.Element msg
renderSwatchMode props =
  let
    -- Wire handler if onMsg is provided
    swatchHandlers = case props.onMsg of
      Just toMsg ->
        [ Swatches.onSelect $ \rgba -> toMsg (SelectSwatch rgba) ]
      Nothing -> []
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "12px"
      ]
      [ E.div_
          [ E.style "font-size" "11px"
          , E.style "color" "#6b7280"
          , E.style "text-transform" "uppercase"
          , E.style "font-weight" "500"
          ]
          [ E.text "Material Colors" ]
      , Swatches.swatchGrid
          (swatchHandlers <>
          [ Swatches.swatches Swatches.materialPrimary
          , Swatches.columns 8
          ])
      ]

-- | Render harmony mode
renderHarmonyMode :: forall msg. PickerProps msg -> PickerState -> E.Element msg
renderHarmonyMode props state =
  let
    -- Base color for harmony calculations
    baseHsl = rgbaToHsl state.currentColor
    
    -- Wire handler if onMsg is provided
    harmonyHandlers = case props.onMsg of
      Just toMsg ->
        [ Harmony.onSelect $ \hsl -> toMsg (SelectHarmony hsl) ]
      Nothing -> []
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "16px"
      ]
      [ Harmony.harmonyPalette 
          (harmonyHandlers <>
          [ Harmony.harmonyType Harmony.Complementary
          , Harmony.baseColor baseHsl
          ])
      , Harmony.harmonyPalette 
          (harmonyHandlers <>
          [ Harmony.harmonyType Harmony.Analogous
          , Harmony.baseColor baseHsl
          ])
      , Harmony.harmonyPalette 
          (harmonyHandlers <>
          [ Harmony.harmonyType Harmony.Triadic
          , Harmony.baseColor baseHsl
          ])
      ]

-- | Render alpha slider section
renderAlphaSection :: forall msg. PickerProps msg -> PickerState -> E.Element msg
renderAlphaSection props state =
  let
    rgb = RGB.fromRGBA state.currentColor
    opacity = RGB.alpha state.currentColor
    
    -- Wire change handler if onMsg is provided
    changeHandler = case props.onMsg of
      Just toMsg -> [ Alpha.onChange (\change -> toMsg (SetOpacity change.opacity)) ]
      Nothing -> []
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "4px"
      ]
      [ E.div_
          [ E.style "font-size" "11px"
          , E.style "color" "#6b7280"
          , E.style "text-transform" "uppercase"
          , E.style "font-weight" "500"
          ]
          [ E.text "Opacity" ]
      , Alpha.alphaSlider
          (changeHandler <>
          [ Alpha.color rgb
          , Alpha.opacity opacity
          ])
      ]

-- | Render input fields section
renderInputSection :: forall msg. PickerProps msg -> PickerState -> E.Element msg
renderInputSection props state =
  let
    -- Current values
    rgb = RGB.fromRGBA state.currentColor
    currentAlpha = Opacity.unwrap (RGB.alpha state.currentColor)
    
    -- Wire hex input handler
    hexHandlers = case props.onMsg of
      Just toMsg ->
        [ Input.onHexChange $ \change ->
            if change.valid
              then 
                let 
                  newRgb = Convert.hexToRgb change.hex
                  r = RGB.rgbToRecord newRgb
                in toMsg (SetColor (RGB.rgba r.r r.g r.b currentAlpha))
              else toMsg (SetColor state.currentColor)
        ]
      Nothing -> []
    
    -- Wire RGB input handler
    rgbHandlers = case props.onMsg of
      Just toMsg ->
        [ Input.onRgbChange $ \change ->
            toMsg (SetColor (RGB.rgba 
              (Channel.unwrap change.red) 
              (Channel.unwrap change.green) 
              (Channel.unwrap change.blue) 
              currentAlpha))
        ]
      Nothing -> []
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "8px"
      ]
      [ -- Hex input
        E.div_
          [ E.style "display" "flex"
          , E.style "align-items" "center"
          , E.style "gap" "8px"
          ]
          [ E.span_
              [ E.style "width" "32px"
              , E.style "font-size" "11px"
              , E.style "color" "#6b7280"
              ]
              [ E.text "HEX" ]
          , Input.hexInput
              (hexHandlers <>
              [ Input.hexValue (RGB.rgbToHex rgb) ])
          ]
        
        -- RGB inputs
      , E.div_
          [ E.style "display" "flex"
          , E.style "align-items" "center"
          , E.style "gap" "8px"
          ]
          [ E.span_
              [ E.style "width" "32px"
              , E.style "font-size" "11px"
              , E.style "color" "#6b7280"
              ]
              [ E.text "RGB" ]
          , Input.rgbInput
              (rgbHandlers <>
              [ Input.rgbValue rgb ])
          ]
      ]

-- | Render contrast checker section
renderContrastSection :: forall msg. PickerState -> E.Element msg
renderContrastSection state =
  let
    rgb = RGB.fromRGBA state.currentColor
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "8px"
      ]
      [ E.div_
          [ E.style "font-size" "11px"
          , E.style "color" "#6b7280"
          , E.style "text-transform" "uppercase"
          , E.style "font-weight" "500"
          ]
          [ E.text "Contrast Check" ]
      , Contrast.contrastChecker
          [ Contrast.foreground rgb
          , Contrast.background (RGB.rgb 255 255 255)
          ]
      ]
