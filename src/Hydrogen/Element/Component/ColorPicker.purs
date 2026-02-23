-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // element // color picker
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ColorPicker — Schema-native color selection component.
-- |
-- | Interactive color selection with multiple color space modes:
-- | - HSL sliders (Hue 0-359, Saturation 0-100, Lightness 0-100)
-- | - RGB sliders (Red 0-255, Green 0-255, Blue 0-255)
-- | - HWB sliders (Hue 0-359, Whiteness 0-100, Blackness 0-100)
-- | - OKLAB sliders (L 0-1, a -0.4 to 0.4, b -0.4 to 0.4)
-- | - OKLCH sliders (L 0-1, C 0-0.4, H 0-359)
-- |
-- | ## Design Philosophy
-- |
-- | This component accepts **concrete Schema atoms** for ALL visual properties.
-- | No hardcoded CSS strings. No Tailwind classes. Pure Schema.
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property              | Pillar     | Type                   | CSS Output           |
-- | |-----------------------|------------|------------------------|----------------------|
-- | | backgroundColor       | Color      | Color.RGB              | background           |
-- | | borderColor           | Color      | Color.RGB              | border-color         |
-- | | labelColor            | Color      | Color.RGB              | color (labels)       |
-- | | primaryColor          | Color      | Color.RGB              | accent color         |
-- | | sliderTrackColor      | Color      | Color.RGB              | slider track         |
-- | | panelBorderRadius     | Geometry   | Geometry.Corners       | border-radius        |
-- | | previewBorderRadius   | Geometry   | Geometry.Corners       | preview border-radius|
-- | | padding               | Dimension  | Device.Pixel           | padding              |
-- | | gap                   | Dimension  | Device.Pixel           | gap                  |
-- | | borderWidth           | Dimension  | Device.Pixel           | border-width         |
-- | | previewHeight         | Dimension  | Device.Pixel           | preview height       |
-- | | labelFontSize         | Typography | FontSize.FontSize      | font-size (labels)   |
-- | | labelFontWeight       | Typography | FontWeight.FontWeight  | font-weight (labels) |
-- | | headerFontSize        | Typography | FontSize.FontSize      | font-size (headers)  |
-- | | headerFontWeight      | Typography | FontWeight.FontWeight  | font-weight (headers)|
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Component.ColorPicker as ColorPicker
-- | import Hydrogen.Schema.Color.RGB as Color
-- |
-- | -- Minimal usage
-- | ColorPicker.colorPicker
-- |   [ ColorPicker.initialColor (Color.rgb 100 150 200)
-- |   , ColorPicker.onChange HandleColorChange
-- |   ]
-- |
-- | -- With brand atoms
-- | ColorPicker.colorPicker
-- |   [ ColorPicker.initialColor brand.primary
-- |   , ColorPicker.onChange HandleColorChange
-- |   , ColorPicker.backgroundColor brand.surfaceColor
-- |   , ColorPicker.borderColor brand.borderColor
-- |   , ColorPicker.labelColor brand.textColor
-- |   , ColorPicker.panelBorderRadius brand.corners
-- |   ]
-- | ```

module Hydrogen.Element.Component.ColorPicker
  ( -- * Component
    colorPicker
  
  -- * Props
  , ColorPickerProps
  , ColorPickerProp
  , defaultProps
  
  -- * Prop Builders: State
  , initialColor
  , enabledModes
  
  -- * Prop Builders: Color Atoms
  , backgroundColor
  , borderColor
  , labelColor
  , primaryColor
  , sliderTrackColor
  
  -- * Prop Builders: Geometry Atoms
  , panelBorderRadius
  , previewBorderRadius
  
  -- * Prop Builders: Dimension Atoms
  , padding
  , gap
  , borderWidth
  , previewHeight
  
  -- * Prop Builders: Typography Atoms
  , labelFontSize
  , labelFontWeight
  , headerFontSize
  , headerFontWeight
  
  -- * Prop Builders: Behavior
  , onChange
  , onModeToggle
  
  -- * Types
  , ColorMode(ModeHSL, ModeRGB, ModeHWB, ModeOKLAB, ModeOKLCH)
  , modeName
  ) where

import Prelude
  ( class Eq
  , negate
  , not
  , show
  , (<>)
  , ($)
  , (-)
  , (*)
  , (/)
  )

import Data.Array (elem, foldl)
import Data.Int (round)
import Data.Int as Int
import Data.Maybe (Maybe(Nothing, Just), maybe)
import Data.Number as Number
import Data.Number.Format (fixed, toStringWith)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Color.HSL as HSL
import Hydrogen.Schema.Color.HWB as HWB
import Hydrogen.Schema.Color.OKLAB as OKLAB
import Hydrogen.Schema.Color.OKLCH as OKLCH
import Hydrogen.Schema.Color.Conversion as Conv
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Typography.FontWeight as FontWeight

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
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
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | ColorPicker properties
-- |
-- | All visual properties accept Schema atoms directly.
-- | Use `Maybe` for optional properties that should inherit defaults.
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
  , panelBorderRadius :: Maybe Geometry.Corners
  , previewBorderRadius :: Maybe Geometry.Corners
  
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

-- | Property modifier
type ColorPickerProp msg = ColorPickerProps msg -> ColorPickerProps msg

-- | Default properties
-- |
-- | Visual properties default to `Nothing` (inherit from context).
-- | This ensures components work with any brand without hardcoded values.
defaultProps :: forall msg. ColorPickerProps msg
defaultProps =
  { color: Color.rgb 128 128 128
  , enabledModes: [ ModeHSL, ModeRGB, ModeHWB, ModeOKLAB, ModeOKLCH ]
  , backgroundColor: Nothing
  , borderColor: Nothing
  , labelColor: Nothing
  , primaryColor: Nothing
  , sliderTrackColor: Nothing
  , panelBorderRadius: Nothing
  , previewBorderRadius: Nothing
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

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // prop builders: state
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set initial color
initialColor :: forall msg. Color.RGB -> ColorPickerProp msg
initialColor c props = props { color = c }

-- | Set which color modes are enabled
enabledModes :: forall msg. Array ColorMode -> ColorPickerProp msg
enabledModes modes props = props { enabledModes = modes }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // prop builders: color
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set background color (Color.RGB atom)
backgroundColor :: forall msg. Color.RGB -> ColorPickerProp msg
backgroundColor c props = props { backgroundColor = Just c }

-- | Set border color (Color.RGB atom)
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

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                      // prop builders: geometry
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set panel border radius (Geometry.Corners atom)
panelBorderRadius :: forall msg. Geometry.Corners -> ColorPickerProp msg
panelBorderRadius r props = props { panelBorderRadius = Just r }

-- | Set preview swatch border radius (Geometry.Corners atom)
previewBorderRadius :: forall msg. Geometry.Corners -> ColorPickerProp msg
previewBorderRadius r props = props { previewBorderRadius = Just r }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                     // prop builders: dimension
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set padding (Device.Pixel atom)
padding :: forall msg. Device.Pixel -> ColorPickerProp msg
padding p props = props { padding = Just p }

-- | Set gap between elements (Device.Pixel atom)
gap :: forall msg. Device.Pixel -> ColorPickerProp msg
gap g props = props { gap = Just g }

-- | Set border width (Device.Pixel atom)
borderWidth :: forall msg. Device.Pixel -> ColorPickerProp msg
borderWidth w props = props { borderWidth = Just w }

-- | Set preview swatch height (Device.Pixel atom)
previewHeight :: forall msg. Device.Pixel -> ColorPickerProp msg
previewHeight h props = props { previewHeight = Just h }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: typography
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set label font size (FontSize atom)
labelFontSize :: forall msg. FontSize.FontSize -> ColorPickerProp msg
labelFontSize s props = props { labelFontSize = Just s }

-- | Set label font weight (FontWeight atom)
labelFontWeight :: forall msg. FontWeight.FontWeight -> ColorPickerProp msg
labelFontWeight w props = props { labelFontWeight = Just w }

-- | Set header font size (FontSize atom)
headerFontSize :: forall msg. FontSize.FontSize -> ColorPickerProp msg
headerFontSize s props = props { headerFontSize = Just s }

-- | Set header font weight (FontWeight atom)
headerFontWeight :: forall msg. FontWeight.FontWeight -> ColorPickerProp msg
headerFontWeight w props = props { headerFontWeight = Just w }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                      // prop builders: behavior
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set change handler
onChange :: forall msg. (Color.RGB -> msg) -> ColorPickerProp msg
onChange handler props = props { onChange = Just handler }

-- | Set mode toggle handler
onModeToggle :: forall msg. (ColorMode -> Boolean -> msg) -> ColorPickerProp msg
onModeToggle handler props = props { onModeToggle = Just handler }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // resolved config
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Resolved configuration with defaults applied
-- |
-- | This bundles resolved atoms to pass to render functions,
-- | avoiding repetitive parameter lists.
type ResolvedConfig =
  { bgColor :: Color.RGB
  , borderCol :: Color.RGB
  , labelCol :: Color.RGB
  , primaryCol :: Color.RGB
  , trackColor :: Color.RGB
  , panelRadius :: String
  , previewRadius :: String
  , paddingVal :: String
  , gapVal :: String
  , borderWidthVal :: String
  , previewHeightVal :: String
  , labelFontSizeVal :: String
  , labelFontWeightVal :: String
  , headerFontSizeVal :: String
  , headerFontWeightVal :: String
  }

-- | Resolve props to config with defaults
resolveConfig :: forall msg. ColorPickerProps msg -> ResolvedConfig
resolveConfig props =
  { bgColor: maybe (Color.rgb 30 30 30) (\c -> c) props.backgroundColor
  , borderCol: maybe (Color.rgb 60 60 60) (\c -> c) props.borderColor
  , labelCol: maybe (Color.rgb 200 200 200) (\c -> c) props.labelColor
  , primaryCol: maybe (Color.rgb 59 130 246) (\c -> c) props.primaryColor
  , trackColor: maybe (Color.rgb 80 80 80) (\c -> c) props.sliderTrackColor
  , panelRadius: maybe "8px" Geometry.cornersToLegacyCss props.panelBorderRadius
  , previewRadius: maybe "4px" Geometry.cornersToLegacyCss props.previewBorderRadius
  , paddingVal: maybe "16px" show props.padding
  , gapVal: maybe "16px" show props.gap
  , borderWidthVal: maybe "1px" show props.borderWidth
  , previewHeightVal: maybe "64px" show props.previewHeight
  , labelFontSizeVal: maybe "14px" FontSize.toLegacyCss props.labelFontSize
  , labelFontWeightVal: maybe "500" FontWeight.toLegacyCss props.labelFontWeight
  , headerFontSizeVal: maybe "14px" FontSize.toLegacyCss props.headerFontSize
  , headerFontWeightVal: maybe "700" FontWeight.toLegacyCss props.headerFontWeight
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // main component
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render a color picker
-- |
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
colorPicker :: forall msg. Array (ColorPickerProp msg) -> E.Element msg
colorPicker propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    config = resolveConfig props
  in
    E.div_
      (buildPanelAttrs config) $
      [ renderColorPreview props config
      , renderModeToggles props config
      , renderColorSliders props config
      ]

-- | Build panel container attributes
buildPanelAttrs :: forall msg. ResolvedConfig -> Array (E.Attribute msg)
buildPanelAttrs config =
  [ E.style "display" "flex"
  , E.style "flex-direction" "column"
  , E.style "gap" config.gapVal
  , E.style "padding" config.paddingVal
  , E.style "background-color" (Color.toLegacyCss config.bgColor)
  , E.style "border-style" "solid"
  , E.style "border-width" config.borderWidthVal
  , E.style "border-color" (Color.toLegacyCss config.borderCol)
  , E.style "border-radius" config.panelRadius
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // color // preview
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render color preview swatch
renderColorPreview :: forall msg. ColorPickerProps msg -> ResolvedConfig -> E.Element msg
renderColorPreview props config =
  E.div_
    [ E.style "width" "100%"
    , E.style "height" config.previewHeightVal
    , E.style "background-color" (Color.toLegacyCss props.color)
    , E.style "border-style" "solid"
    , E.style "border-width" config.borderWidthVal
    , E.style "border-color" (Color.toLegacyCss config.borderCol)
    , E.style "border-radius" config.previewRadius
    ]
    []

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // mode // toggles
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render mode toggle checkboxes
renderModeToggles :: forall msg. ColorPickerProps msg -> ResolvedConfig -> E.Element msg
renderModeToggles props config =
  E.div_
    [ E.style "display" "flex"
    , E.style "flex-wrap" "wrap"
    , E.style "gap" "12px"
    , E.style "padding-bottom" "8px"
    , E.style "border-bottom" ("1px solid " <> Color.toLegacyCss config.borderCol)
    ]
    [ renderModeCheckbox ModeHSL props config
    , renderModeCheckbox ModeRGB props config
    , renderModeCheckbox ModeHWB props config
    , renderModeCheckbox ModeOKLAB props config
    , renderModeCheckbox ModeOKLCH props config
    ]

-- | Render a single mode checkbox
renderModeCheckbox :: forall msg. ColorMode -> ColorPickerProps msg -> ResolvedConfig -> E.Element msg
renderModeCheckbox mode props config =
  let
    isChecked = elem mode props.enabledModes
    checkboxAttrs = case props.onModeToggle of
      Nothing ->
        [ E.style "pointer-events" "none"
        , E.style "opacity" "0.5"
        ]
      Just handler ->
        [ E.onClick (handler mode (not isChecked))
        , E.style "cursor" "pointer"
        ]
  in
    E.label_
      ( [ E.style "display" "flex"
        , E.style "align-items" "center"
        , E.style "gap" "8px"
        , E.style "cursor" "pointer"
        ] <> checkboxAttrs
      )
      [ renderCheckboxVisual isChecked config
      , E.span_
          [ E.style "font-size" config.labelFontSizeVal
          , E.style "font-weight" config.labelFontWeightVal
          , E.style "color" (Color.toLegacyCss config.labelCol)
          ]
          [ E.text (modeName mode) ]
      ]

-- | Render checkbox visual
renderCheckboxVisual :: forall msg. Boolean -> ResolvedConfig -> E.Element msg
renderCheckboxVisual isChecked config =
  let
    bgColor = if isChecked then config.primaryCol else config.bgColor
    borderCol = if isChecked then config.primaryCol else config.borderCol
  in
    E.div_
      [ E.style "width" "18px"
      , E.style "height" "18px"
      , E.style "border-radius" "4px"
      , E.style "border-style" "solid"
      , E.style "border-width" "2px"
      , E.style "border-color" (Color.toLegacyCss borderCol)
      , E.style "background-color" (Color.toLegacyCss bgColor)
      , E.style "display" "flex"
      , E.style "align-items" "center"
      , E.style "justify-content" "center"
      ]
      [ if isChecked then renderCheckmark else E.empty ]

-- | Render checkmark SVG
renderCheckmark :: forall msg. E.Element msg
renderCheckmark =
  E.svg_
    [ E.attr "width" "12"
    , E.attr "height" "12"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "white"
    , E.attr "stroke-width" "3"
    , E.attr "stroke-linecap" "round"
    , E.attr "stroke-linejoin" "round"
    ]
    [ E.svgElement "polyline"
        [ E.attr "points" "20 6 9 17 4 12" ]
        []
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // color // sliders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render color sliders for all enabled modes
renderColorSliders :: forall msg. ColorPickerProps msg -> ResolvedConfig -> E.Element msg
renderColorSliders props config =
  E.div_
    [ E.style "display" "flex"
    , E.style "flex-direction" "column"
    , E.style "gap" config.gapVal
    ]
    [ if elem ModeHSL props.enabledModes
        then renderHSLSliders props config
        else E.empty
    , if elem ModeRGB props.enabledModes
        then renderRGBSliders props config
        else E.empty
    , if elem ModeHWB props.enabledModes
        then renderHWBSliders props config
        else E.empty
    , if elem ModeOKLAB props.enabledModes
        then renderOKLABSliders props config
        else E.empty
    , if elem ModeOKLCH props.enabledModes
        then renderOKLCHSliders props config
        else E.empty
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // hsl // sliders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render HSL sliders
renderHSLSliders :: forall msg. ColorPickerProps msg -> ResolvedConfig -> E.Element msg
renderHSLSliders props config =
  let
    hslColor = Conv.rgbToHsl props.color
    hslRec = HSL.hslToRecord hslColor
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "8px"
      ]
      [ renderSectionHeader "HSL" config
      , case props.onChange of
          Nothing ->
            E.div_
              [ E.style "display" "flex"
              , E.style "flex-direction" "column"
              , E.style "gap" "8px"
              ]
              [ renderSliderReadonly "Hue" 0 359 hslRec.h config
              , renderSliderReadonly "Saturation" 0 100 hslRec.s config
              , renderSliderReadonly "Lightness" 0 100 hslRec.l config
              ]
          Just handler ->
            E.div_
              [ E.style "display" "flex"
              , E.style "flex-direction" "column"
              , E.style "gap" "8px"
              ]
              [ renderSlider "Hue" 0 359 hslRec.h
                  (\v -> handler (Conv.hslToRgb (HSL.hsl v hslRec.s hslRec.l))) config
              , renderSlider "Saturation" 0 100 hslRec.s
                  (\v -> handler (Conv.hslToRgb (HSL.hsl hslRec.h v hslRec.l))) config
              , renderSlider "Lightness" 0 100 hslRec.l
                  (\v -> handler (Conv.hslToRgb (HSL.hsl hslRec.h hslRec.s v))) config
              ]
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // rgb // sliders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render RGB sliders
renderRGBSliders :: forall msg. ColorPickerProps msg -> ResolvedConfig -> E.Element msg
renderRGBSliders props config =
  let
    rgbRec = Color.rgbToRecord props.color
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "8px"
      ]
      [ renderSectionHeader "RGB" config
      , case props.onChange of
          Nothing ->
            E.div_
              [ E.style "display" "flex"
              , E.style "flex-direction" "column"
              , E.style "gap" "8px"
              ]
              [ renderSliderReadonly "Red" 0 255 rgbRec.r config
              , renderSliderReadonly "Green" 0 255 rgbRec.g config
              , renderSliderReadonly "Blue" 0 255 rgbRec.b config
              ]
          Just handler ->
            E.div_
              [ E.style "display" "flex"
              , E.style "flex-direction" "column"
              , E.style "gap" "8px"
              ]
              [ renderSlider "Red" 0 255 rgbRec.r
                  (\v -> handler (Color.rgb v rgbRec.g rgbRec.b)) config
              , renderSlider "Green" 0 255 rgbRec.g
                  (\v -> handler (Color.rgb rgbRec.r v rgbRec.b)) config
              , renderSlider "Blue" 0 255 rgbRec.b
                  (\v -> handler (Color.rgb rgbRec.r rgbRec.g v)) config
              ]
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // hwb // sliders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render HWB sliders
renderHWBSliders :: forall msg. ColorPickerProps msg -> ResolvedConfig -> E.Element msg
renderHWBSliders props config =
  let
    hwbColor = Conv.rgbToHwb props.color
    hwbRec = HWB.hwbToRecord hwbColor
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "8px"
      ]
      [ renderSectionHeader "HWB" config
      , case props.onChange of
          Nothing ->
            E.div_
              [ E.style "display" "flex"
              , E.style "flex-direction" "column"
              , E.style "gap" "8px"
              ]
              [ renderSliderReadonly "Hue" 0 359 hwbRec.h config
              , renderSliderReadonly "Whiteness" 0 100 hwbRec.w config
              , renderSliderReadonly "Blackness" 0 100 hwbRec.b config
              ]
          Just handler ->
            E.div_
              [ E.style "display" "flex"
              , E.style "flex-direction" "column"
              , E.style "gap" "8px"
              ]
              [ renderSlider "Hue" 0 359 hwbRec.h
                  (\v -> handler (Conv.hwbToRgb (HWB.hwb v hwbRec.w hwbRec.b))) config
              , renderSlider "Whiteness" 0 100 hwbRec.w
                  (\v -> handler (Conv.hwbToRgb (HWB.hwb hwbRec.h v hwbRec.b))) config
              , renderSlider "Blackness" 0 100 hwbRec.b
                  (\v -> handler (Conv.hwbToRgb (HWB.hwb hwbRec.h hwbRec.w v))) config
              ]
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // oklab // sliders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render OKLAB sliders
renderOKLABSliders :: forall msg. ColorPickerProps msg -> ResolvedConfig -> E.Element msg
renderOKLABSliders props config =
  let
    oklabColor = Conv.rgbToOklab props.color
    oklabRec = OKLAB.oklabToRecord oklabColor
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "8px"
      ]
      [ renderSectionHeader "OKLAB" config
      , case props.onChange of
          Nothing ->
            E.div_
              [ E.style "display" "flex"
              , E.style "flex-direction" "column"
              , E.style "gap" "8px"
              ]
              [ renderSliderFloatReadonly "L" 0.0 1.0 oklabRec.l config
              , renderSliderFloatReadonly "a" (-0.4) 0.4 oklabRec.a config
              , renderSliderFloatReadonly "b" (-0.4) 0.4 oklabRec.b config
              ]
          Just handler ->
            E.div_
              [ E.style "display" "flex"
              , E.style "flex-direction" "column"
              , E.style "gap" "8px"
              ]
              [ renderSliderFloat "L" 0.0 1.0 0.01 oklabRec.l
                  (\v -> handler (Conv.oklabToRgb (OKLAB.oklab v oklabRec.a oklabRec.b))) config
              , renderSliderFloat "a" (-0.4) 0.4 0.01 oklabRec.a
                  (\v -> handler (Conv.oklabToRgb (OKLAB.oklab oklabRec.l v oklabRec.b))) config
              , renderSliderFloat "b" (-0.4) 0.4 0.01 oklabRec.b
                  (\v -> handler (Conv.oklabToRgb (OKLAB.oklab oklabRec.l oklabRec.a v))) config
              ]
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // oklch // sliders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render OKLCH sliders
renderOKLCHSliders :: forall msg. ColorPickerProps msg -> ResolvedConfig -> E.Element msg
renderOKLCHSliders props config =
  let
    oklchColor = Conv.rgbToOklch props.color
    oklchRec = OKLCH.oklchToRecord oklchColor
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "8px"
      ]
      [ renderSectionHeader "OKLCH" config
      , case props.onChange of
          Nothing ->
            E.div_
              [ E.style "display" "flex"
              , E.style "flex-direction" "column"
              , E.style "gap" "8px"
              ]
              [ renderSliderFloatReadonly "L" 0.0 1.0 oklchRec.l config
              , renderSliderFloatReadonly "C" 0.0 0.4 oklchRec.c config
              , renderSliderReadonly "H" 0 359 oklchRec.h config
              ]
          Just handler ->
            E.div_
              [ E.style "display" "flex"
              , E.style "flex-direction" "column"
              , E.style "gap" "8px"
              ]
              [ renderSliderFloat "L" 0.0 1.0 0.01 oklchRec.l
                  (\v -> handler (Conv.oklchToRgb (OKLCH.oklch v oklchRec.c oklchRec.h))) config
              , renderSliderFloat "C" 0.0 0.4 0.01 oklchRec.c
                  (\v -> handler (Conv.oklchToRgb (OKLCH.oklch oklchRec.l v oklchRec.h))) config
              , renderSlider "H" 0 359 oklchRec.h
                  (\v -> handler (Conv.oklchToRgb (OKLCH.oklch oklchRec.l oklchRec.c v))) config
              ]
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Calculate percentage position for slider track fill (Int values)
toPercent :: Int -> Int -> Int -> String
toPercent minV maxV val =
  let
    range = Int.toNumber (maxV - minV)
    offset = Int.toNumber (val - minV)
    pct = (offset / range) * 100.0
  in
    show pct <> "%"

-- | Calculate percentage position for slider track fill (Number values)
toPercentFloat :: Number -> Number -> Number -> String
toPercentFloat minV maxV val =
  let
    range = maxV - minV
    offset = val - minV
    pct = (offset / range) * 100.0
  in
    show pct <> "%"

-- | Render section header
renderSectionHeader :: forall msg. String -> ResolvedConfig -> E.Element msg
renderSectionHeader label config =
  E.h3_
    [ E.style "margin" "0"
    , E.style "font-size" config.headerFontSizeVal
    , E.style "font-weight" config.headerFontWeightVal
    , E.style "color" (Color.toLegacyCss config.labelCol)
    , E.style "opacity" "0.6"
    ]
    [ E.text label ]

-- | Render an interactive slider (Int values)
renderSlider :: forall msg. String -> Int -> Int -> Int -> (Int -> msg) -> ResolvedConfig -> E.Element msg
renderSlider label minVal maxVal currentVal handler config =
  let
    -- Calculate fill percentage for track visualization
    percent = toPercent minVal maxVal currentVal
    trackGradient = "linear-gradient(to right, " 
      <> Color.toLegacyCss config.primaryCol <> " " <> percent <> ", "
      <> Color.toLegacyCss config.trackColor <> " " <> percent <> ")"
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "4px"
      ]
      [ E.label_
          [ E.style "font-size" config.labelFontSizeVal
          , E.style "font-weight" config.labelFontWeightVal
          , E.style "color" (Color.toLegacyCss config.labelCol)
          ]
          [ E.text (label <> ": " <> show currentVal) ]
      , E.input_
          [ E.type_ "range"
          , E.attr "min" (show minVal)
          , E.attr "max" (show maxVal)
          , E.value (show currentVal)
          , E.onChange (\v -> handler (parseIntWithDefault currentVal v))
          , E.style "width" "100%"
          , E.style "height" "8px"
          , E.style "border-radius" "4px"
          , E.style "background" trackGradient
          , E.style "accent-color" (Color.toLegacyCss config.primaryCol)
          , E.style "cursor" "pointer"
          ]
      ]

-- | Render a readonly slider (Int values)
renderSliderReadonly :: forall msg. String -> Int -> Int -> Int -> ResolvedConfig -> E.Element msg
renderSliderReadonly label minVal maxVal currentVal config =
  let
    percent = toPercent minVal maxVal currentVal
    trackGradient = "linear-gradient(to right, " 
      <> Color.toLegacyCss config.primaryCol <> " " <> percent <> ", "
      <> Color.toLegacyCss config.trackColor <> " " <> percent <> ")"
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "4px"
      ]
      [ E.label_
          [ E.style "font-size" config.labelFontSizeVal
          , E.style "font-weight" config.labelFontWeightVal
          , E.style "color" (Color.toLegacyCss config.labelCol)
          ]
          [ E.text (label <> ": " <> show currentVal) ]
      , E.input_
          [ E.type_ "range"
          , E.attr "min" (show minVal)
          , E.attr "max" (show maxVal)
          , E.value (show currentVal)
          , E.disabled true
          , E.style "width" "100%"
          , E.style "height" "8px"
          , E.style "border-radius" "4px"
          , E.style "background" trackGradient
          , E.style "accent-color" (Color.toLegacyCss config.primaryCol)
          , E.style "opacity" "0.5"
          , E.style "cursor" "not-allowed"
          ]
      ]

-- | Render an interactive slider (Number values)
renderSliderFloat :: forall msg. String -> Number -> Number -> Number -> Number -> (Number -> msg) -> ResolvedConfig -> E.Element msg
renderSliderFloat label minVal maxVal stepVal currentVal handler config =
  let
    displayVal = toStringWith (fixed 3) currentVal
    percent = toPercentFloat minVal maxVal currentVal
    trackGradient = "linear-gradient(to right, " 
      <> Color.toLegacyCss config.primaryCol <> " " <> percent <> ", "
      <> Color.toLegacyCss config.trackColor <> " " <> percent <> ")"
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "4px"
      ]
      [ E.label_
          [ E.style "font-size" config.labelFontSizeVal
          , E.style "font-weight" config.labelFontWeightVal
          , E.style "color" (Color.toLegacyCss config.labelCol)
          ]
          [ E.text (label <> ": " <> displayVal) ]
      , E.input_
          [ E.type_ "range"
          , E.attr "min" (show minVal)
          , E.attr "max" (show maxVal)
          , E.attr "step" (show stepVal)
          , E.value (show currentVal)
          , E.onChange (\v -> handler (parseNumberWithDefault currentVal v))
          , E.style "width" "100%"
          , E.style "height" "8px"
          , E.style "border-radius" "4px"
          , E.style "background" trackGradient
          , E.style "accent-color" (Color.toLegacyCss config.primaryCol)
          , E.style "cursor" "pointer"
          ]
      ]

-- | Render a readonly slider (Number values)
renderSliderFloatReadonly :: forall msg. String -> Number -> Number -> Number -> ResolvedConfig -> E.Element msg
renderSliderFloatReadonly label minVal maxVal currentVal config =
  let
    displayVal = toStringWith (fixed 3) currentVal
    percent = toPercentFloat minVal maxVal currentVal
    trackGradient = "linear-gradient(to right, " 
      <> Color.toLegacyCss config.primaryCol <> " " <> percent <> ", "
      <> Color.toLegacyCss config.trackColor <> " " <> percent <> ")"
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "4px"
      ]
      [ E.label_
          [ E.style "font-size" config.labelFontSizeVal
          , E.style "font-weight" config.labelFontWeightVal
          , E.style "color" (Color.toLegacyCss config.labelCol)
          ]
          [ E.text (label <> ": " <> displayVal) ]
      , E.input_
          [ E.type_ "range"
          , E.attr "min" (show minVal)
          , E.attr "max" (show maxVal)
          , E.value (show currentVal)
          , E.disabled true
          , E.style "width" "100%"
          , E.style "height" "8px"
          , E.style "border-radius" "4px"
          , E.style "background" trackGradient
          , E.style "accent-color" (Color.toLegacyCss config.primaryCol)
          , E.style "opacity" "0.5"
          , E.style "cursor" "not-allowed"
          ]
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // parsing
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Parse Int with default fallback
-- |
-- | Range inputs always produce valid number strings, but we handle
-- | the failure case gracefully by returning the default.
parseIntWithDefault :: Int -> String -> Int
parseIntWithDefault def str = case Int.fromString str of
  Just n -> n
  Nothing -> case Number.fromString str of
    Just num -> round num
    Nothing -> def

-- | Parse Number with default fallback
-- |
-- | Range inputs always produce valid number strings, but we handle
-- | the failure case gracefully by returning the default.
parseNumberWithDefault :: Number -> String -> Number
parseNumberWithDefault def str = case Number.fromString str of
  Just n -> n
  Nothing -> def
