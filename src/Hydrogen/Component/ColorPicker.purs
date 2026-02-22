-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // hydrogen // color picker
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ColorPicker component
-- |
-- | Interactive color selection with multiple color space modes:
-- | - HSL sliders (Hue 0-359, Saturation 0-100, Lightness 0-100)
-- | - RGB sliders (Red 0-255, Green 0-255, Blue 0-255)
-- | - HWB sliders (Hue 0-359, Whiteness 0-100, Blackness 0-100)
-- | - OKLAB sliders (L 0-1, a -0.4 to 0.4, b -0.4 to 0.4)
-- | - OKLCH sliders (L 0-1, C 0-0.4, H 0-359)
-- | - Checkboxes to enable/disable each color space
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.ColorPicker as ColorPicker
-- | import Hydrogen.Schema.Color.RGB (rgb)
-- |
-- | ColorPicker.colorPicker
-- |   [ ColorPicker.initialColor (rgb 100 150 200)
-- |   , ColorPicker.onChange HandleColorChange
-- |   , ColorPicker.enabledModes [ColorPicker.ModeHSL, ColorPicker.ModeRGB]
-- |   ]
-- | ```

module Hydrogen.Component.ColorPicker
  ( -- * Component
    colorPicker
    -- * Props
  , ColorPickerProps
  , ColorPickerProp
  , defaultProps
    -- * Prop Builders
  , initialColor
  , onChange
  , enabledModes
  , onModeToggle
  , className
    -- * Types
  , ColorMode(ModeHSL, ModeRGB, ModeHWB, ModeOKLAB, ModeOKLCH)
  , modeName
  ) where

import Prelude

import Data.Array (elem, foldl)
import Data.Int (round, toNumber)
import Data.Maybe (Maybe(Nothing, Just))
import Data.Number.Format (fixed, toStringWith)
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Hydrogen.Component.Checkbox as Checkbox
import Hydrogen.Component.Slider as Slider
import Hydrogen.Schema.Color.RGB (RGB, rgb, rgbToRecord, rgbToCss)
import Hydrogen.Schema.Color.HSL (hsl, hslToRecord)
import Hydrogen.Schema.Color.HWB (hwb, hwbToRecord)
import Hydrogen.Schema.Color.OKLAB (oklab, oklabToRecord)
import Hydrogen.Schema.Color.OKLCH (oklch, oklchToRecord)
import Hydrogen.Schema.Color.Conversion (rgbToHsl, rgbToHwb, rgbToOklab, rgbToOklch, hslToRgb, hwbToRgb, oklabToRgb, oklchToRgb)
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Color picker input mode
data ColorMode
  = ModeHSL
  | ModeRGB
  | ModeHWB
  | ModeOKLAB
  | ModeOKLCH

derive instance eqColorMode :: Eq ColorMode

-- | Get display name for mode
modeName :: ColorMode -> String
modeName = case _ of
  ModeHSL -> "HSL"
  ModeRGB -> "RGB"
  ModeHWB -> "HWB"
  ModeOKLAB -> "OKLAB"
  ModeOKLCH -> "OKLCH"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | ColorPicker properties
type ColorPickerProps i =
  { color :: RGB
  , enabledModes :: Array ColorMode
  , className :: String
  , onChange :: Maybe (RGB -> i)
  , onModeToggle :: Maybe (ColorMode -> Boolean -> i)
  }

-- | Property modifier
type ColorPickerProp i = ColorPickerProps i -> ColorPickerProps i

-- | Default color picker properties
defaultProps :: forall i. ColorPickerProps i
defaultProps =
  { color: rgb 128 128 128
  , enabledModes: [ModeHSL, ModeRGB, ModeHWB, ModeOKLAB, ModeOKLCH]
  , className: ""
  , onChange: Nothing
  , onModeToggle: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set initial color
initialColor :: forall i. RGB -> ColorPickerProp i
initialColor c props = props { color = c }

-- | Set change handler
onChange :: forall i. (RGB -> i) -> ColorPickerProp i
onChange handler props = props { onChange = Just handler }

-- | Set which color modes are enabled
enabledModes :: forall i. Array ColorMode -> ColorPickerProp i
enabledModes modes props = props { enabledModes = modes }

-- | Set mode toggle handler
onModeToggle :: forall i. (ColorMode -> Boolean -> i) -> ColorPickerProp i
onModeToggle handler props = props { onModeToggle = Just handler }

-- | Add custom class
className :: forall i. String -> ColorPickerProp i
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // component
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render a color picker
colorPicker :: forall w i. Array (ColorPickerProp i) -> HH.HTML w i
colorPicker propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
  in
    HH.div
      [ cls [ "color-picker space-y-4 p-4 border border-white/20 rounded-lg", props.className ] ]
      [ -- Color preview
        HH.div
          [ cls [ "color-preview w-full h-16 rounded border border-white/20" ]
          , HP.style ("background-color: " <> rgbToCss props.color)
          ]
          []
        
        -- Mode toggles
        , renderModeToggles props.enabledModes props.onModeToggle
        
        -- HSL mode
        , if elem ModeHSL props.enabledModes
            then renderHSLSliders props.color props.onChange
            else HH.text ""
        
        -- RGB mode
        , if elem ModeRGB props.enabledModes
            then renderRGBSliders props.color props.onChange
            else HH.text ""
        
        -- HWB mode
        , if elem ModeHWB props.enabledModes
            then renderHWBSliders props.color props.onChange
            else HH.text ""
        
        -- OKLAB mode
        , if elem ModeOKLAB props.enabledModes
            then renderOKLABSliders props.color props.onChange
            else HH.text ""
        
        -- OKLCH mode
        , if elem ModeOKLCH props.enabledModes
            then renderOKLCHSliders props.color props.onChange
            else HH.text ""
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // mode // toggles
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render mode toggle checkboxes
renderModeToggles :: forall w i. Array ColorMode -> Maybe (ColorMode -> Boolean -> i) -> HH.HTML w i
renderModeToggles enabledModes onToggle =
  HH.div [ cls [ "flex flex-wrap gap-3 pb-2 border-b border-white/10" ] ]
    [ renderModeCheckbox ModeHSL enabledModes onToggle
    , renderModeCheckbox ModeRGB enabledModes onToggle
    , renderModeCheckbox ModeHWB enabledModes onToggle
    , renderModeCheckbox ModeOKLAB enabledModes onToggle
    , renderModeCheckbox ModeOKLCH enabledModes onToggle
    ]

-- | Render a single mode checkbox
renderModeCheckbox :: forall w i. ColorMode -> Array ColorMode -> Maybe (ColorMode -> Boolean -> i) -> HH.HTML w i
renderModeCheckbox mode enabledModes onToggle =
  let
    isChecked = elem mode enabledModes
  in
    HH.label [ cls [ "flex items-center gap-2 cursor-pointer" ] ]
      [ case onToggle of
          Nothing ->
            Checkbox.checkbox
              [ Checkbox.checked isChecked
              , Checkbox.disabled true
              ]
          Just handler ->
            Checkbox.checkbox
              [ Checkbox.checked isChecked
              , Checkbox.onChange (\_ -> handler mode (not isChecked))
              ]
      , HH.span [ cls [ "text-sm font-medium" ] ] [ HH.text (modeName mode) ]
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // hsl // sliders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render HSL sliders
renderHSLSliders :: forall w i. RGB -> Maybe (RGB -> i) -> HH.HTML w i
renderHSLSliders rgb onChange =
  let
    hslColor = rgbToHsl rgb
    hslRec = hslToRecord hslColor
  in
    HH.div [ cls [ "space-y-2 pt-2" ] ]
      [ HH.h3 [ cls [ "text-sm font-bold text-white/60" ] ] [ HH.text "HSL" ]
      , case onChange of
          Nothing ->
            HH.div [ cls [ "space-y-2" ] ]
              [ renderSliderReadonly "Hue" 0 359 hslRec.h
              , renderSliderReadonly "Saturation" 0 100 hslRec.s
              , renderSliderReadonly "Lightness" 0 100 hslRec.l
              ]
          Just handler ->
            HH.div [ cls [ "space-y-2" ] ]
              [ renderSlider "Hue" 0 359 hslRec.h (\v -> handler (hslToRgb (hsl v hslRec.s hslRec.l)))
              , renderSlider "Saturation" 0 100 hslRec.s (\v -> handler (hslToRgb (hsl hslRec.h v hslRec.l)))
              , renderSlider "Lightness" 0 100 hslRec.l (\v -> handler (hslToRgb (hsl hslRec.h hslRec.s v)))
              ]
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // rgb // sliders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render RGB sliders
renderRGBSliders :: forall w i. RGB -> Maybe (RGB -> i) -> HH.HTML w i
renderRGBSliders rgbColor onChange =
  let
    rgbRec = rgbToRecord rgbColor
  in
    HH.div [ cls [ "space-y-2 pt-2" ] ]
      [ HH.h3 [ cls [ "text-sm font-bold text-white/60" ] ] [ HH.text "RGB" ]
      , case onChange of
          Nothing ->
            HH.div [ cls [ "space-y-2" ] ]
              [ renderSliderReadonly "Red" 0 255 rgbRec.r
              , renderSliderReadonly "Green" 0 255 rgbRec.g
              , renderSliderReadonly "Blue" 0 255 rgbRec.b
              ]
          Just handler ->
            HH.div [ cls [ "space-y-2" ] ]
              [ renderSlider "Red" 0 255 rgbRec.r (\v -> handler (rgb v rgbRec.g rgbRec.b))
              , renderSlider "Green" 0 255 rgbRec.g (\v -> handler (rgb rgbRec.r v rgbRec.b))
              , renderSlider "Blue" 0 255 rgbRec.b (\v -> handler (rgb rgbRec.r rgbRec.g v))
              ]
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // hwb // sliders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render HWB sliders
renderHWBSliders :: forall w i. RGB -> Maybe (RGB -> i) -> HH.HTML w i
renderHWBSliders rgb onChange =
  let
    hwbColor = rgbToHwb rgb
    hwbRec = hwbToRecord hwbColor
  in
    HH.div [ cls [ "space-y-2 pt-2" ] ]
      [ HH.h3 [ cls [ "text-sm font-bold text-white/60" ] ] [ HH.text "HWB" ]
      , case onChange of
          Nothing ->
            HH.div [ cls [ "space-y-2" ] ]
              [ renderSliderReadonly "Hue" 0 359 hwbRec.h
              , renderSliderReadonly "Whiteness" 0 100 hwbRec.w
              , renderSliderReadonly "Blackness" 0 100 hwbRec.b
              ]
          Just handler ->
            HH.div [ cls [ "space-y-2" ] ]
              [ renderSlider "Hue" 0 359 hwbRec.h (\v -> handler (hwbToRgb (hwb v hwbRec.w hwbRec.b)))
              , renderSlider "Whiteness" 0 100 hwbRec.w (\v -> handler (hwbToRgb (hwb hwbRec.h v hwbRec.b)))
              , renderSlider "Blackness" 0 100 hwbRec.b (\v -> handler (hwbToRgb (hwb hwbRec.h hwbRec.w v)))
              ]
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // oklab // sliders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render OKLAB sliders
renderOKLABSliders :: forall w i. RGB -> Maybe (RGB -> i) -> HH.HTML w i
renderOKLABSliders rgb onChange =
  let
    oklabColor = rgbToOklab rgb
    oklabRec = oklabToRecord oklabColor
  in
    HH.div [ cls [ "space-y-2 pt-2" ] ]
      [ HH.h3 [ cls [ "text-sm font-bold text-white/60" ] ] [ HH.text "OKLAB" ]
      , case onChange of
          Nothing ->
            HH.div [ cls [ "space-y-2" ] ]
              [ renderSliderReadonlyFloat "L" 0.0 1.0 oklabRec.l
              , renderSliderReadonlyFloat "a" (-0.4) 0.4 oklabRec.a
              , renderSliderReadonlyFloat "b" (-0.4) 0.4 oklabRec.b
              ]
          Just handler ->
            HH.div [ cls [ "space-y-2" ] ]
              [ renderSliderFloat "L" 0.0 1.0 0.01 oklabRec.l (\v -> handler (oklabToRgb (oklab v oklabRec.a oklabRec.b)))
              , renderSliderFloat "a" (-0.4) 0.4 0.01 oklabRec.a (\v -> handler (oklabToRgb (oklab oklabRec.l v oklabRec.b)))
              , renderSliderFloat "b" (-0.4) 0.4 0.01 oklabRec.b (\v -> handler (oklabToRgb (oklab oklabRec.l oklabRec.a v)))
              ]
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // oklch // sliders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render OKLCH sliders
renderOKLCHSliders :: forall w i. RGB -> Maybe (RGB -> i) -> HH.HTML w i
renderOKLCHSliders rgb onChange =
  let
    oklchColor = rgbToOklch rgb
    oklchRec = oklchToRecord oklchColor
  in
    HH.div [ cls [ "space-y-2 pt-2" ] ]
      [ HH.h3 [ cls [ "text-sm font-bold text-white/60" ] ] [ HH.text "OKLCH" ]
      , case onChange of
          Nothing ->
            HH.div [ cls [ "space-y-2" ] ]
              [ renderSliderReadonlyFloat "L" 0.0 1.0 oklchRec.l
              , renderSliderReadonlyFloat "C" 0.0 0.4 oklchRec.c
              , renderSliderReadonly "H" 0 359 oklchRec.h
              ]
          Just handler ->
            HH.div [ cls [ "space-y-2" ] ]
              [ renderSliderFloat "L" 0.0 1.0 0.01 oklchRec.l (\v -> handler (oklchToRgb (oklch v oklchRec.c oklchRec.h)))
              , renderSliderFloat "C" 0.0 0.4 0.01 oklchRec.c (\v -> handler (oklchToRgb (oklch oklchRec.l v oklchRec.h)))
              , renderSlider "H" 0 359 oklchRec.h (\v -> handler (oklchToRgb (oklch oklchRec.l oklchRec.c v)))
              ]
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render a labeled slider (Int)
renderSlider :: forall w i. String -> Int -> Int -> Int -> (Int -> i) -> HH.HTML w i
renderSlider label minVal maxVal value handler =
  HH.div [ cls [ "space-y-1" ] ]
    [ HH.label [ cls [ "text-sm font-medium" ] ] [ HH.text (label <> ": " <> show value) ]
    , Slider.slider
        [ Slider.value (toNumber value)
        , Slider.min (toNumber minVal)
        , Slider.max (toNumber maxVal)
        , Slider.onChange (\v -> handler (round v))
        ]
    ]

-- | Render a readonly labeled slider (Int)
renderSliderReadonly :: forall w i. String -> Int -> Int -> Int -> HH.HTML w i
renderSliderReadonly label minVal maxVal value =
  HH.div [ cls [ "space-y-1" ] ]
    [ HH.label [ cls [ "text-sm font-medium" ] ] [ HH.text (label <> ": " <> show value) ]
    , Slider.slider
        [ Slider.value (toNumber value)
        , Slider.min (toNumber minVal)
        , Slider.max (toNumber maxVal)
        , Slider.disabled true
        ]
    ]

-- | Render a labeled slider (Number)
renderSliderFloat :: forall w i. String -> Number -> Number -> Number -> Number -> (Number -> i) -> HH.HTML w i
renderSliderFloat label minVal maxVal step value handler =
  HH.div [ cls [ "space-y-1" ] ]
    [ HH.label [ cls [ "text-sm font-medium" ] ] 
        [ HH.text (label <> ": " <> toStringWith (fixed 3) value) ]
    , Slider.slider
        [ Slider.value value
        , Slider.min minVal
        , Slider.max maxVal
        , Slider.step step
        , Slider.onChange handler
        ]
    ]

-- | Render a readonly labeled slider (Number)
renderSliderReadonlyFloat :: forall w i. String -> Number -> Number -> Number -> HH.HTML w i
renderSliderReadonlyFloat label minVal maxVal value =
  HH.div [ cls [ "space-y-1" ] ]
    [ HH.label [ cls [ "text-sm font-medium" ] ] 
        [ HH.text (label <> ": " <> toStringWith (fixed 3) value) ]
    , Slider.slider
        [ Slider.value value
        , Slider.min minVal
        , Slider.max maxVal
        , Slider.disabled true
        ]
    ]
