-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // element // color picker // sliders
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ColorPicker Sliders — Slider rendering for all color spaces.
-- |
-- | This module handles rendering the slider controls for each color mode:
-- | HSL, RGB, HWB, OKLAB, and OKLCH.

module Hydrogen.Element.Compound.ColorPicker.Sliders
  ( -- * Mode Section Renderer
    renderModeSection
  
  -- * Individual Slider Renderers
  , renderHSLSliders
  , renderRGBSliders
  , renderHWBSliders
  , renderOKLABSliders
  , renderOKLCHSliders
  
  -- * Slider Row Helpers
  , renderSliderRow
  , renderSliderRowFloat
  ) where

import Prelude
  ( negate
  , show
  , (<>)
  )

import Data.Int (round, toNumber)
import Data.Maybe (Maybe(Nothing, Just))
import Data.Number.Format (fixed, toStringWith)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Color.HSL as HSL
import Hydrogen.Schema.Color.HWB as HWB
import Hydrogen.Schema.Color.OKLAB as OKLAB
import Hydrogen.Schema.Color.OKLCH as OKLCH
import Hydrogen.Schema.Color.Conversion as Convert
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Typography.FontWeight as FontWeight

import Hydrogen.Element.Compound.Slider as Slider

import Hydrogen.Element.Compound.ColorPicker.Types (ColorMode(ModeHSL, ModeRGB, ModeHWB, ModeOKLAB, ModeOKLCH), modeName)
import Hydrogen.Element.Compound.ColorPicker.Props (ColorPickerProps)
import Hydrogen.Element.Compound.ColorPicker.Defaults (ResolvedConfig)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // mode sections
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a mode section with sliders
renderModeSection :: forall msg. ColorPickerProps msg -> ResolvedConfig -> ColorMode -> E.Element msg
renderModeSection props cfg mode =
  E.div_
    [ E.style "display" "flex"
    , E.style "flex-direction" "column"
    , E.style "gap" "8px"
    ]
    [ -- Mode header
      E.h3_
        [ E.style "font-size" (show cfg.hdrFontSize)
        , E.style "font-weight" (FontWeight.toLegacyCss cfg.hdrFontWeight)
        , E.style "color" (Color.toLegacyCss cfg.lblColor)
        , E.style "text-transform" "uppercase"
        , E.style "letter-spacing" "0.05em"
        , E.style "margin" "0"
        ]
        [ E.text (modeName mode) ]
    
    -- Sliders
    , case mode of
        ModeHSL -> renderHSLSliders props cfg
        ModeRGB -> renderRGBSliders props cfg
        ModeHWB -> renderHWBSliders props cfg
        ModeOKLAB -> renderOKLABSliders props cfg
        ModeOKLCH -> renderOKLCHSliders props cfg
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // hsl sliders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render HSL sliders
renderHSLSliders :: forall msg. ColorPickerProps msg -> ResolvedConfig -> E.Element msg
renderHSLSliders props cfg =
  let
    hslColor = Convert.rgbToHsl props.color
    hslRec = HSL.hslToRecord hslColor
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "8px"
      ]
      [ renderSliderRow "Hue" (toNumber hslRec.h) 0.0 359.0 1.0 cfg
          (buildHSLHandler props hslRec (\v -> HSL.hsl (round v) hslRec.s hslRec.l))
      , renderSliderRow "Saturation" (toNumber hslRec.s) 0.0 100.0 1.0 cfg
          (buildHSLHandler props hslRec (\v -> HSL.hsl hslRec.h (round v) hslRec.l))
      , renderSliderRow "Lightness" (toNumber hslRec.l) 0.0 100.0 1.0 cfg
          (buildHSLHandler props hslRec (\v -> HSL.hsl hslRec.h hslRec.s (round v)))
      ]

-- | Build HSL change handler
buildHSLHandler :: forall msg. ColorPickerProps msg -> { h :: Int, s :: Int, l :: Int } -> (Number -> HSL.HSL) -> Maybe (Number -> msg)
buildHSLHandler props _ mkHsl = case props.onChange of
  Just handler -> Just (\v -> handler (Convert.hslToRgb (mkHsl v)))
  Nothing -> Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // rgb sliders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render RGB sliders
renderRGBSliders :: forall msg. ColorPickerProps msg -> ResolvedConfig -> E.Element msg
renderRGBSliders props cfg =
  let
    rgbRec = Color.rgbToRecord props.color
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "8px"
      ]
      [ renderSliderRow "Red" (toNumber rgbRec.r) 0.0 255.0 1.0 cfg
          (buildRGBHandler props (\v -> Color.rgb (round v) rgbRec.g rgbRec.b))
      , renderSliderRow "Green" (toNumber rgbRec.g) 0.0 255.0 1.0 cfg
          (buildRGBHandler props (\v -> Color.rgb rgbRec.r (round v) rgbRec.b))
      , renderSliderRow "Blue" (toNumber rgbRec.b) 0.0 255.0 1.0 cfg
          (buildRGBHandler props (\v -> Color.rgb rgbRec.r rgbRec.g (round v)))
      ]

-- | Build RGB change handler
buildRGBHandler :: forall msg. ColorPickerProps msg -> (Number -> Color.RGB) -> Maybe (Number -> msg)
buildRGBHandler props mkRgb = case props.onChange of
  Just handler -> Just (\v -> handler (mkRgb v))
  Nothing -> Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // hwb sliders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render HWB sliders
renderHWBSliders :: forall msg. ColorPickerProps msg -> ResolvedConfig -> E.Element msg
renderHWBSliders props cfg =
  let
    hwbColor = Convert.rgbToHwb props.color
    hwbRec = HWB.hwbToRecord hwbColor
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "8px"
      ]
      [ renderSliderRow "Hue" (toNumber hwbRec.h) 0.0 359.0 1.0 cfg
          (buildHWBHandler props hwbRec (\v -> HWB.hwb (round v) hwbRec.w hwbRec.b))
      , renderSliderRow "Whiteness" (toNumber hwbRec.w) 0.0 100.0 1.0 cfg
          (buildHWBHandler props hwbRec (\v -> HWB.hwb hwbRec.h (round v) hwbRec.b))
      , renderSliderRow "Blackness" (toNumber hwbRec.b) 0.0 100.0 1.0 cfg
          (buildHWBHandler props hwbRec (\v -> HWB.hwb hwbRec.h hwbRec.w (round v)))
      ]

-- | Build HWB change handler
buildHWBHandler :: forall msg. ColorPickerProps msg -> { h :: Int, w :: Int, b :: Int } -> (Number -> HWB.HWB) -> Maybe (Number -> msg)
buildHWBHandler props _ mkHwb = case props.onChange of
  Just handler -> Just (\v -> handler (Convert.hwbToRgb (mkHwb v)))
  Nothing -> Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // oklab sliders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render OKLAB sliders
renderOKLABSliders :: forall msg. ColorPickerProps msg -> ResolvedConfig -> E.Element msg
renderOKLABSliders props cfg =
  let
    oklabColor = Convert.rgbToOklab props.color
    oklabRec = OKLAB.oklabToRecord oklabColor
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "8px"
      ]
      [ renderSliderRowFloat "L" oklabRec.l 0.0 1.0 0.01 cfg
          (buildOKLABHandler props oklabRec (\v -> OKLAB.oklab v oklabRec.a oklabRec.b))
      , renderSliderRowFloat "a" oklabRec.a (-0.4) 0.4 0.01 cfg
          (buildOKLABHandler props oklabRec (\v -> OKLAB.oklab oklabRec.l v oklabRec.b))
      , renderSliderRowFloat "b" oklabRec.b (-0.4) 0.4 0.01 cfg
          (buildOKLABHandler props oklabRec (\v -> OKLAB.oklab oklabRec.l oklabRec.a v))
      ]

-- | Build OKLAB change handler
buildOKLABHandler :: forall msg. ColorPickerProps msg -> { l :: Number, a :: Number, b :: Number } -> (Number -> OKLAB.OKLAB) -> Maybe (Number -> msg)
buildOKLABHandler props _ mkOklab = case props.onChange of
  Just handler -> Just (\v -> handler (Convert.oklabToRgb (mkOklab v)))
  Nothing -> Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // oklch sliders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render OKLCH sliders
renderOKLCHSliders :: forall msg. ColorPickerProps msg -> ResolvedConfig -> E.Element msg
renderOKLCHSliders props cfg =
  let
    oklchColor = Convert.rgbToOklch props.color
    oklchRec = OKLCH.oklchToRecord oklchColor
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "8px"
      ]
      [ renderSliderRowFloat "L" oklchRec.l 0.0 1.0 0.01 cfg
          (buildOKLCHHandler props oklchRec (\v -> OKLCH.oklch v oklchRec.c oklchRec.h))
      , renderSliderRowFloat "C" oklchRec.c 0.0 0.4 0.01 cfg
          (buildOKLCHHandler props oklchRec (\v -> OKLCH.oklch oklchRec.l v oklchRec.h))
      , renderSliderRow "H" (toNumber oklchRec.h) 0.0 359.0 1.0 cfg
          (buildOKLCHHueHandler props oklchRec)
      ]

-- | Build OKLCH change handler
buildOKLCHHandler :: forall msg. ColorPickerProps msg -> { l :: Number, c :: Number, h :: Int } -> (Number -> OKLCH.OKLCH) -> Maybe (Number -> msg)
buildOKLCHHandler props _ mkOklch = case props.onChange of
  Just handler -> Just (\v -> handler (Convert.oklchToRgb (mkOklch v)))
  Nothing -> Nothing

-- | Build OKLCH hue handler (Int-based)
buildOKLCHHueHandler :: forall msg. ColorPickerProps msg -> { l :: Number, c :: Number, h :: Int } -> Maybe (Number -> msg)
buildOKLCHHueHandler props oklchRec = case props.onChange of
  Just handler -> Just (\v -> handler (Convert.oklchToRgb (OKLCH.oklch oklchRec.l oklchRec.c (round v))))
  Nothing -> Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // slider row
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a labeled slider row (Int values)
renderSliderRow :: forall msg. String -> Number -> Number -> Number -> Number -> ResolvedConfig -> Maybe (Number -> msg) -> E.Element msg
renderSliderRow label val minVal maxVal stepVal cfg handler =
  E.div_
    [ E.style "display" "flex"
    , E.style "flex-direction" "column"
    , E.style "gap" "4px"
    ]
    [ E.label_
        [ E.style "font-size" (show cfg.lblFontSize)
        , E.style "font-weight" (FontWeight.toLegacyCss cfg.lblFontWeight)
        , E.style "color" (Color.toLegacyCss cfg.lblColor)
        ]
        [ E.text (label <> ": " <> show (round val)) ]
    , Slider.slider
        ( [ Slider.value val
          , Slider.minValue minVal
          , Slider.maxValue maxVal
          , Slider.step stepVal
          , Slider.trackColor cfg.trkColor
          , Slider.rangeColor cfg.primColor
          , Slider.thumbBorderColor cfg.primColor
          , Slider.trackHeight (Device.px 6.0)
          , Slider.thumbSize (Device.px 16.0)
          ] <> case handler of
                  Just h -> [ Slider.onChange h ]
                  Nothing -> [ Slider.sliderDisabled true ]
        )
    ]

-- | Render a labeled slider row (Float values)
renderSliderRowFloat :: forall msg. String -> Number -> Number -> Number -> Number -> ResolvedConfig -> Maybe (Number -> msg) -> E.Element msg
renderSliderRowFloat label val minVal maxVal stepVal cfg handler =
  E.div_
    [ E.style "display" "flex"
    , E.style "flex-direction" "column"
    , E.style "gap" "4px"
    ]
    [ E.label_
        [ E.style "font-size" (show cfg.lblFontSize)
        , E.style "font-weight" (FontWeight.toLegacyCss cfg.lblFontWeight)
        , E.style "color" (Color.toLegacyCss cfg.lblColor)
        ]
        [ E.text (label <> ": " <> toStringWith (fixed 3) val) ]
    , Slider.slider
        ( [ Slider.value val
          , Slider.minValue minVal
          , Slider.maxValue maxVal
          , Slider.step stepVal
          , Slider.trackColor cfg.trkColor
          , Slider.rangeColor cfg.primColor
          , Slider.thumbBorderColor cfg.primColor
          , Slider.trackHeight (Device.px 6.0)
          , Slider.thumbSize (Device.px 16.0)
          ] <> case handler of
                  Just h -> [ Slider.onChange h ]
                  Nothing -> [ Slider.sliderDisabled true ]
        )
    ]
