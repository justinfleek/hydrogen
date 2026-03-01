-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // colorpicker // picker // sliders
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | HSL slider rendering for the ColorPicker component.
-- |
-- | This module contains the slider mode render functions:
-- | - Hue slider (0-359 degrees)
-- | - Saturation slider (0-100%)
-- | - Lightness slider (0-100%)

module Hydrogen.Element.Compound.ColorPicker.Picker.Sliders
  ( -- * Slider Mode
    renderSliderMode
  
  -- * Individual Sliders
  , renderHueSlider
  , renderSaturationSlider
  , renderLightnessSlider
  
  -- * Utilities
  , stringToInt
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , ($)
  , (<>)
  , (/)
  , (*)
  )

import Data.Int (fromString) as Int
import Data.Maybe (Maybe(Nothing, Just))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.Hue as Hue
import Hydrogen.Schema.Color.Saturation as Sat
import Hydrogen.Schema.Color.Lightness as Light

import Hydrogen.Element.Compound.ColorPicker.Picker.Types 
  ( PickerMsg(SetHue, SetSaturation, SetLightness)
  )
import Hydrogen.Element.Compound.ColorPicker.Picker.Props (PickerProps)
import Hydrogen.Element.Compound.ColorPicker.Picker.State (PickerState, rgbaToHsl)

import Hydrogen.Schema.Color.HSL as HSL

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // slider mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render slider mode with HSL sliders
-- |
-- | Displays three sliders for independent control of:
-- | - Hue (color angle)
-- | - Saturation (color intensity)
-- | - Lightness (brightness)
renderSliderMode :: forall msg. PickerProps msg -> PickerState -> E.Element msg
renderSliderMode props state =
  let
    -- Extract HSL from current color
    currentHsl = rgbaToHsl state.currentColor
    currentHue = HSL.hue currentHsl
    currentSat = HSL.saturation currentHsl
    currentLight = HSL.lightness currentHsl
    
    -- Common slider style
    sliderRowStyle = 
      [ E.style "display" "flex"
      , E.style "align-items" "center"
      , E.style "gap" "12px"
      ]
    
    sliderLabelStyle =
      [ E.style "width" "80px"
      , E.style "font-size" "12px"
      , E.style "color" "#374151"
      ]
    
    sliderValueStyle =
      [ E.style "width" "40px"
      , E.style "font-size" "12px"
      , E.style "color" "#6b7280"
      , E.style "text-align" "right"
      ]
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "12px"
      ]
      [ -- Section header
        E.div_
          [ E.style "font-size" "11px"
          , E.style "color" "#6b7280"
          , E.style "text-transform" "uppercase"
          , E.style "font-weight" "500"
          ]
          [ E.text "HSL Sliders" ]
      
        -- Hue slider (0-359)
      , E.div_ sliderRowStyle
          [ E.span_ sliderLabelStyle [ E.text "Hue" ]
          , renderHueSlider props currentHue
          , E.span_ sliderValueStyle [ E.text (show (Hue.unwrap currentHue) <> "\x00B0") ]
          ]
      
        -- Saturation slider (0-100)  
      , E.div_ sliderRowStyle
          [ E.span_ sliderLabelStyle [ E.text "Saturation" ]
          , renderSaturationSlider props currentHue currentSat
          , E.span_ sliderValueStyle [ E.text (show (Sat.unwrap currentSat) <> "%") ]
          ]
      
        -- Lightness slider (0-100)
      , E.div_ sliderRowStyle
          [ E.span_ sliderLabelStyle [ E.text "Lightness" ]
          , renderLightnessSlider props currentHue currentLight
          , E.span_ sliderValueStyle [ E.text (show (Light.unwrap currentLight) <> "%") ]
          ]
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // individual sliders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render hue slider (0-359 degrees)
-- |
-- | Displays a rainbow gradient with draggable thumb.
-- | Full spectrum from red (0) through yellow, green, cyan, blue, magenta, back to red (359).
renderHueSlider :: forall msg. PickerProps msg -> Hue.Hue -> E.Element msg
renderHueSlider props currentHue =
  let
    -- Hue gradient background
    hueGradient = "linear-gradient(to right, hsl(0,100%,50%), hsl(60,100%,50%), hsl(120,100%,50%), hsl(180,100%,50%), hsl(240,100%,50%), hsl(300,100%,50%), hsl(360,100%,50%))"
    
    -- Calculate thumb position (0-100%)
    thumbPos = show ((Hue.unwrap currentHue * 100) / 359) <> "%"
    
    -- Wire handler
    inputHandler = case props.onMsg of
      Just toMsg ->
        [ E.onInput $ \val -> toMsg (SetHue (Hue.hue (stringToInt val))) ]
      Nothing -> []
  in
    E.div_
      [ E.style "position" "relative"
      , E.style "flex" "1"
      , E.style "height" "20px"
      , E.style "border-radius" "10px"
      , E.style "background" hueGradient
      ]
      [ E.input_
          (inputHandler <>
          [ E.attr "type" "range"
          , E.attr "min" "0"
          , E.attr "max" "359"
          , E.attr "value" (show (Hue.unwrap currentHue))
          , E.style "position" "absolute"
          , E.style "width" "100%"
          , E.style "height" "100%"
          , E.style "opacity" "0"
          , E.style "cursor" "pointer"
          ])
      , E.div_
          [ E.style "position" "absolute"
          , E.style "left" thumbPos
          , E.style "top" "50%"
          , E.style "transform" "translate(-50%, -50%)"
          , E.style "width" "16px"
          , E.style "height" "16px"
          , E.style "border-radius" "50%"
          , E.style "background" "#fff"
          , E.style "box-shadow" "0 1px 3px rgba(0,0,0,0.3)"
          , E.style "pointer-events" "none"
          ]
          []
      ]

-- | Render saturation slider (0-100%)
-- |
-- | Gradient goes from gray (0%) to full saturation (100%) at the current hue.
renderSaturationSlider :: forall msg. PickerProps msg -> Hue.Hue -> Sat.Saturation -> E.Element msg
renderSaturationSlider props currentHue currentSat =
  let
    -- Saturation gradient (gray to full saturation at current hue)
    h = Hue.unwrap currentHue
    satGradient = "linear-gradient(to right, hsl(" <> show h <> ",0%,50%), hsl(" <> show h <> ",100%,50%))"
    
    -- Calculate thumb position
    thumbPos = show (Sat.unwrap currentSat) <> "%"
    
    -- Wire handler
    inputHandler = case props.onMsg of
      Just toMsg ->
        [ E.onInput $ \val -> toMsg (SetSaturation (Sat.saturation (stringToInt val))) ]
      Nothing -> []
  in
    E.div_
      [ E.style "position" "relative"
      , E.style "flex" "1"
      , E.style "height" "20px"
      , E.style "border-radius" "10px"
      , E.style "background" satGradient
      ]
      [ E.input_
          (inputHandler <>
          [ E.attr "type" "range"
          , E.attr "min" "0"
          , E.attr "max" "100"
          , E.attr "value" (show (Sat.unwrap currentSat))
          , E.style "position" "absolute"
          , E.style "width" "100%"
          , E.style "height" "100%"
          , E.style "opacity" "0"
          , E.style "cursor" "pointer"
          ])
      , E.div_
          [ E.style "position" "absolute"
          , E.style "left" thumbPos
          , E.style "top" "50%"
          , E.style "transform" "translate(-50%, -50%)"
          , E.style "width" "16px"
          , E.style "height" "16px"
          , E.style "border-radius" "50%"
          , E.style "background" "#fff"
          , E.style "box-shadow" "0 1px 3px rgba(0,0,0,0.3)"
          , E.style "pointer-events" "none"
          ]
          []
      ]

-- | Render lightness slider (0-100%)
-- |
-- | Gradient goes from black (0%) through the hue (50%) to white (100%).
renderLightnessSlider :: forall msg. PickerProps msg -> Hue.Hue -> Light.Lightness -> E.Element msg
renderLightnessSlider props currentHue currentLight =
  let
    -- Lightness gradient (black to white through the hue)
    h = Hue.unwrap currentHue
    lightGradient = "linear-gradient(to right, hsl(" <> show h <> ",100%,0%), hsl(" <> show h <> ",100%,50%), hsl(" <> show h <> ",100%,100%))"
    
    -- Calculate thumb position
    thumbPos = show (Light.unwrap currentLight) <> "%"
    
    -- Wire handler
    inputHandler = case props.onMsg of
      Just toMsg ->
        [ E.onInput $ \val -> toMsg (SetLightness (Light.lightness (stringToInt val))) ]
      Nothing -> []
  in
    E.div_
      [ E.style "position" "relative"
      , E.style "flex" "1"
      , E.style "height" "20px"
      , E.style "border-radius" "10px"
      , E.style "background" lightGradient
      ]
      [ E.input_
          (inputHandler <>
          [ E.attr "type" "range"
          , E.attr "min" "0"
          , E.attr "max" "100"
          , E.attr "value" (show (Light.unwrap currentLight))
          , E.style "position" "absolute"
          , E.style "width" "100%"
          , E.style "height" "100%"
          , E.style "opacity" "0"
          , E.style "cursor" "pointer"
          ])
      , E.div_
          [ E.style "position" "absolute"
          , E.style "left" thumbPos
          , E.style "top" "50%"
          , E.style "transform" "translate(-50%, -50%)"
          , E.style "width" "16px"
          , E.style "height" "16px"
          , E.style "border-radius" "50%"
          , E.style "background" "#fff"
          , E.style "box-shadow" "0 1px 3px rgba(0,0,0,0.3)"
          , E.style "pointer-events" "none"
          ]
          []
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Parse string to int (for slider values)
-- |
-- | Returns 0 for invalid input (safe default for slider ranges).
stringToInt :: String -> Int
stringToInt s = case Int.fromString s of
  Just n -> n
  Nothing -> 0
