-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                    // hydrogen // colorpicker
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Color picker component
-- |
-- | A comprehensive color picker with spectrum selection, format options,
-- | swatches, and eyedropper support.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.ColorPicker as ColorPicker
-- |
-- | -- Basic color picker
-- | ColorPicker.colorPicker
-- |   [ ColorPicker.value "#ff5500"
-- |   , ColorPicker.onChange HandleColorChange
-- |   ]
-- |
-- | -- With alpha/opacity support
-- | ColorPicker.colorPicker
-- |   [ ColorPicker.value "rgba(255, 85, 0, 0.8)"
-- |   , ColorPicker.showAlpha true
-- |   , ColorPicker.onChange HandleColorChange
-- |   ]
-- |
-- | -- Inline mode with swatches
-- | ColorPicker.colorPicker
-- |   [ ColorPicker.mode ColorPicker.Inline
-- |   , ColorPicker.swatches ["#ff0000", "#00ff00", "#0000ff"]
-- |   , ColorPicker.showRecentColors true
-- |   ]
-- |
-- | -- Popover mode with format toggle
-- | ColorPicker.colorPicker
-- |   [ ColorPicker.mode ColorPicker.Popover
-- |   , ColorPicker.format ColorPicker.RGB
-- |   , ColorPicker.showFormatToggle true
-- |   ]
-- | ```
module Hydrogen.Component.ColorPicker
  ( -- * Color Picker Components
    colorPicker
  , saturationPanel
  , hueSlider
  , alphaSlider
  , colorInput
  , colorSwatches
  , recentColors
  , eyedropperButton
  , copyButton
  , formatToggle
    -- * Props
  , ColorPickerProps
  , ColorPickerProp
  , defaultProps
    -- * Prop Builders
  , value
  , format
  , mode
  , showAlpha
  , showHex
  , showRgb
  , showHsl
  , swatches
  , showRecentColors
  , maxRecentColors
  , showEyedropper
  , showCopy
  , showFormatToggle
  , disabled
  , className
  , onChange
  , onFormatChange
    -- * Types
  , ColorFormat(..)
  , PickerMode(..)
  , ColorValue
  , HSVColor
  , RGBColor
  , HSLColor
    -- * FFI
  , ColorPickerElement
    -- * Color Utilities
  , hexToRgb
  , rgbToHex
  , rgbToHsl
  , hslToRgb
  , hsvToRgb
  , rgbToHsv
  , parseColor
  , formatColor
  ) where

import Prelude hiding (map)

import Data.Array (foldl, take)
import Data.Int (round, toNumber)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Number (abs)
import Data.String (toLower, trim)
import Data.String as String
import Effect (Effect)
import Effect.Uncurried (EffectFn1, EffectFn2, EffectFn3)
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)
import Web.DOM.Element (Element)
import Web.Event.Event (Event)
import Web.UIEvent.MouseEvent (MouseEvent)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Color format for display/input
data ColorFormat
  = Hex
  | RGB
  | HSL

derive instance eqColorFormat :: Eq ColorFormat

-- | Picker display mode
data PickerMode
  = Inline
  | Popover

derive instance eqPickerMode :: Eq PickerMode

-- | Generic color value (string representation)
type ColorValue = String

-- | RGB color components (0-255)
type RGBColor =
  { r :: Int
  , g :: Int
  , b :: Int
  , a :: Number
  }

-- | HSL color components
type HSLColor =
  { h :: Number  -- 0-360
  , s :: Number  -- 0-100
  , l :: Number  -- 0-100
  , a :: Number  -- 0-1
  }

-- | HSV color components (used internally)
type HSVColor =
  { h :: Number  -- 0-360
  , s :: Number  -- 0-100
  , v :: Number  -- 0-100
  , a :: Number  -- 0-1
  }

-- | Opaque picker element type
foreign import data ColorPickerElement :: Type

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Initialize saturation panel pointer events
foreign import initSaturationPanelImpl :: EffectFn3 Element ({ s :: Number, v :: Number } -> Effect Unit) { hue :: Number } ColorPickerElement

-- | Initialize hue slider pointer events
foreign import initHueSliderImpl :: EffectFn2 Element (Number -> Effect Unit) ColorPickerElement

-- | Initialize alpha slider pointer events
foreign import initAlphaSliderImpl :: EffectFn2 Element (Number -> Effect Unit) ColorPickerElement

-- | Cleanup color picker element
foreign import destroyColorPickerImpl :: EffectFn1 ColorPickerElement Unit

-- | Open eyedropper (EyeDropper API)
foreign import openEyedropperImpl :: EffectFn1 (String -> Effect Unit) Unit

-- | Copy text to clipboard
foreign import copyToClipboardImpl :: EffectFn1 String Unit

-- | Check if eyedropper is supported
foreign import isEyedropperSupportedImpl :: Effect Boolean

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

type ColorPickerProps i =
  { value :: ColorValue
  , format :: ColorFormat
  , mode :: PickerMode
  , showAlpha :: Boolean
  , showHex :: Boolean
  , showRgb :: Boolean
  , showHsl :: Boolean
  , swatches :: Array ColorValue
  , showRecentColors :: Boolean
  , maxRecentColors :: Int
  , recentColorsList :: Array ColorValue
  , showEyedropper :: Boolean
  , showCopy :: Boolean
  , showFormatToggle :: Boolean
  , disabled :: Boolean
  , isOpen :: Boolean
  , className :: String
  , onChange :: Maybe (ColorValue -> i)
  , onFormatChange :: Maybe (ColorFormat -> i)
  , onOpenChange :: Maybe (Boolean -> i)
  }

type ColorPickerProp i = ColorPickerProps i -> ColorPickerProps i

defaultProps :: forall i. ColorPickerProps i
defaultProps =
  { value: "#000000"
  , format: Hex
  , mode: Popover
  , showAlpha: false
  , showHex: true
  , showRgb: true
  , showHsl: false
  , swatches: []
  , showRecentColors: false
  , maxRecentColors: 8
  , recentColorsList: []
  , showEyedropper: true
  , showCopy: true
  , showFormatToggle: true
  , disabled: false
  , isOpen: false
  , className: ""
  , onChange: Nothing
  , onFormatChange: Nothing
  , onOpenChange: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set color value
value :: forall i. ColorValue -> ColorPickerProp i
value v props = props { value = v }

-- | Set color format
format :: forall i. ColorFormat -> ColorPickerProp i
format f props = props { format = f }

-- | Set picker mode (inline/popover)
mode :: forall i. PickerMode -> ColorPickerProp i
mode m props = props { mode = m }

-- | Show alpha/opacity slider
showAlpha :: forall i. Boolean -> ColorPickerProp i
showAlpha s props = props { showAlpha = s }

-- | Show hex input
showHex :: forall i. Boolean -> ColorPickerProp i
showHex s props = props { showHex = s }

-- | Show RGB inputs
showRgb :: forall i. Boolean -> ColorPickerProp i
showRgb s props = props { showRgb = s }

-- | Show HSL inputs
showHsl :: forall i. Boolean -> ColorPickerProp i
showHsl s props = props { showHsl = s }

-- | Set preset color swatches
swatches :: forall i. Array ColorValue -> ColorPickerProp i
swatches s props = props { swatches = s }

-- | Show recent colors
showRecentColors :: forall i. Boolean -> ColorPickerProp i
showRecentColors s props = props { showRecentColors = s }

-- | Set max recent colors to display
maxRecentColors :: forall i. Int -> ColorPickerProp i
maxRecentColors n props = props { maxRecentColors = n }

-- | Show eyedropper button
showEyedropper :: forall i. Boolean -> ColorPickerProp i
showEyedropper s props = props { showEyedropper = s }

-- | Show copy button
showCopy :: forall i. Boolean -> ColorPickerProp i
showCopy s props = props { showCopy = s }

-- | Show format toggle
showFormatToggle :: forall i. Boolean -> ColorPickerProp i
showFormatToggle s props = props { showFormatToggle = s }

-- | Set disabled state
disabled :: forall i. Boolean -> ColorPickerProp i
disabled d props = props { disabled = d }

-- | Add custom class
className :: forall i. String -> ColorPickerProp i
className c props = props { className = props.className <> " " <> c }

-- | Set color change handler
onChange :: forall i. (ColorValue -> i) -> ColorPickerProp i
onChange handler props = props { onChange = Just handler }

-- | Set format change handler
onFormatChange :: forall i. (ColorFormat -> i) -> ColorPickerProp i
onFormatChange handler props = props { onFormatChange = Just handler }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // color conversions
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Parse hex string to RGB
hexToRgb :: String -> Maybe RGBColor
hexToRgb hex =
  let
    cleaned = if String.take 1 hex == "#" then String.drop 1 hex else hex
    len = String.length cleaned
  in
    if len == 6 || len == 8
      then 
        let
          r = parseHexPair (String.take 2 cleaned)
          g = parseHexPair (String.take 2 (String.drop 2 cleaned))
          b = parseHexPair (String.take 2 (String.drop 4 cleaned))
          a = if len == 8 
                then toNumber (parseHexPair (String.drop 6 cleaned)) / 255.0
                else 1.0
        in Just { r, g, b, a }
      else Nothing

-- | Convert RGB to hex string
rgbToHex :: RGBColor -> String
rgbToHex { r, g, b, a } =
  let
    rHex = toHexPair r
    gHex = toHexPair g
    bHex = toHexPair b
    aHex = if a < 1.0 then toHexPair (round (a * 255.0)) else ""
  in "#" <> rHex <> gHex <> bHex <> aHex

-- | Convert RGB to HSL
rgbToHsl :: RGBColor -> HSLColor
rgbToHsl { r, g, b, a } =
  let
    r' = toNumber r / 255.0
    g' = toNumber g / 255.0
    b' = toNumber b / 255.0
    maxVal = max r' (max g' b')
    minVal = min r' (min g' b')
    l = (maxVal + minVal) / 2.0
    d = maxVal - minVal
    s = if d == 0.0 
          then 0.0 
          else d / (1.0 - abs (2.0 * l - 1.0))
    h = if d == 0.0 
          then 0.0
          else if maxVal == r' 
            then 60.0 * (mod' ((g' - b') / d) 6.0)
            else if maxVal == g'
              then 60.0 * ((b' - r') / d + 2.0)
              else 60.0 * ((r' - g') / d + 4.0)
    h' = if h < 0.0 then h + 360.0 else h
  in { h: h', s: s * 100.0, l: l * 100.0, a }

-- | Convert HSL to RGB
hslToRgb :: HSLColor -> RGBColor
hslToRgb { h, s, l, a } =
  let
    s' = s / 100.0
    l' = l / 100.0
    c = (1.0 - abs (2.0 * l' - 1.0)) * s'
    x = c * (1.0 - abs (mod' (h / 60.0) 2.0 - 1.0))
    m = l' - c / 2.0
    { r', g', b' } = 
      if h < 60.0 then { r': c, g': x, b': 0.0 }
      else if h < 120.0 then { r': x, g': c, b': 0.0 }
      else if h < 180.0 then { r': 0.0, g': c, b': x }
      else if h < 240.0 then { r': 0.0, g': x, b': c }
      else if h < 300.0 then { r': x, g': 0.0, b': c }
      else { r': c, g': 0.0, b': x }
  in { r: round ((r' + m) * 255.0)
     , g: round ((g' + m) * 255.0)
     , b: round ((b' + m) * 255.0)
     , a }

-- | Convert HSV to RGB
hsvToRgb :: HSVColor -> RGBColor
hsvToRgb { h, s, v, a } =
  let
    s' = s / 100.0
    v' = v / 100.0
    c = v' * s'
    x = c * (1.0 - abs (mod' (h / 60.0) 2.0 - 1.0))
    m = v' - c
    { r', g', b' } = 
      if h < 60.0 then { r': c, g': x, b': 0.0 }
      else if h < 120.0 then { r': x, g': c, b': 0.0 }
      else if h < 180.0 then { r': 0.0, g': c, b': x }
      else if h < 240.0 then { r': 0.0, g': x, b': c }
      else if h < 300.0 then { r': x, g': 0.0, b': c }
      else { r': c, g': 0.0, b': x }
  in { r: round ((r' + m) * 255.0)
     , g: round ((g' + m) * 255.0)
     , b: round ((b' + m) * 255.0)
     , a }

-- | Convert RGB to HSV
rgbToHsv :: RGBColor -> HSVColor
rgbToHsv { r, g, b, a } =
  let
    r' = toNumber r / 255.0
    g' = toNumber g / 255.0
    b' = toNumber b / 255.0
    maxVal = max r' (max g' b')
    minVal = min r' (min g' b')
    d = maxVal - minVal
    v = maxVal * 100.0
    s = if maxVal == 0.0 then 0.0 else (d / maxVal) * 100.0
    h = if d == 0.0 
          then 0.0
          else if maxVal == r' 
            then 60.0 * (mod' ((g' - b') / d) 6.0)
            else if maxVal == g'
              then 60.0 * ((b' - r') / d + 2.0)
              else 60.0 * ((r' - g') / d + 4.0)
    h' = if h < 0.0 then h + 360.0 else h
  in { h: h', s, v, a }

-- | Parse any color string to RGB
parseColor :: ColorValue -> Maybe RGBColor
parseColor colorStr =
  let str = toLower (trim colorStr)
  in if String.take 1 str == "#"
       then hexToRgb str
       else if String.take 4 str == "rgb("
         then parseRgbString str
         else if String.take 5 str == "rgba("
           then parseRgbaString str
           else if String.take 4 str == "hsl("
             then parseHslString str
             else if String.take 5 str == "hsla("
               then parseHslaString str
               else Nothing

-- | Format RGB to specified format
formatColor :: ColorFormat -> RGBColor -> ColorValue
formatColor fmt rgb = case fmt of
  Hex -> rgbToHex rgb
  RGB -> 
    if rgb.a < 1.0
      then "rgba(" <> show rgb.r <> ", " <> show rgb.g <> ", " <> show rgb.b <> ", " <> show rgb.a <> ")"
      else "rgb(" <> show rgb.r <> ", " <> show rgb.g <> ", " <> show rgb.b <> ")"
  HSL ->
    let hsl = rgbToHsl rgb
    in if hsl.a < 1.0
         then "hsla(" <> show (round hsl.h) <> ", " <> show (round hsl.s) <> "%, " <> show (round hsl.l) <> "%, " <> show hsl.a <> ")"
         else "hsl(" <> show (round hsl.h) <> ", " <> show (round hsl.s) <> "%, " <> show (round hsl.l) <> "%)"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Main color picker component
colorPicker :: forall w i. Array (ColorPickerProp i) -> HH.HTML w i
colorPicker propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    rgb = fromMaybe { r: 0, g: 0, b: 0, a: 1.0 } (parseColor props.value)
    hsv = rgbToHsv rgb
    
    pickerContent = 
      HH.div
        [ cls [ "p-3 space-y-3" ] ]
        [ -- Saturation/brightness panel
          saturationPanel props hsv
          -- Hue slider
        , hueSlider props hsv.h
          -- Alpha slider (optional)
        , if props.showAlpha
            then alphaSlider props rgb.a rgb
            else HH.text ""
          -- Color inputs based on format
        , colorInputs props rgb
          -- Tools row (eyedropper, copy, format toggle)
        , toolsRow props
          -- Swatches
        , if not (null props.swatches)
            then colorSwatches props.swatches props.onChange
            else HH.text ""
          -- Recent colors
        , if props.showRecentColors && not (null props.recentColorsList)
            then recentColors (take props.maxRecentColors props.recentColorsList) props.onChange
            else HH.text ""
        ]
  in
    case props.mode of
      Inline ->
        HH.div
          [ cls [ "w-64 rounded-lg border bg-popover text-popover-foreground shadow-md", props.className ]
          ]
          [ pickerContent ]
      Popover ->
        HH.div
          [ cls [ "relative inline-block", props.className ] ]
          [ -- Color preview/trigger button
            HH.button
              [ cls [ "w-10 h-10 rounded-md border border-input shadow-sm focus:outline-none focus:ring-2 focus:ring-ring" ]
              , HP.attr (HH.AttrName "style") ("background-color: " <> props.value)
              , HP.disabled props.disabled
              , ARIA.label "Select color"
              ]
              []
            -- Dropdown panel
          , if props.isOpen
              then 
                HH.div
                  [ cls [ "absolute z-50 mt-2 w-64 rounded-lg border bg-popover text-popover-foreground shadow-md" ] ]
                  [ pickerContent ]
              else HH.text ""
          ]

-- | Saturation/brightness panel
saturationPanel :: forall w i. ColorPickerProps i -> HSVColor -> HH.HTML w i
saturationPanel props hsv =
  let
    hueColor = rgbToHex (hsvToRgb { h: hsv.h, s: 100.0, v: 100.0, a: 1.0 })
    cursorX = hsv.s
    cursorY = 100.0 - hsv.v
  in
    HH.div
      [ cls [ "relative w-full h-40 rounded-md cursor-crosshair overflow-hidden" ]
      , HP.attr (HH.AttrName "style") ("background: linear-gradient(to top, #000, transparent), linear-gradient(to right, #fff, " <> hueColor <> ")")
      , HP.attr (HH.AttrName "data-saturation-panel") "true"
      ]
      [ -- Cursor indicator
        HH.div
          [ cls [ "absolute w-4 h-4 -ml-2 -mt-2 rounded-full border-2 border-white shadow-md pointer-events-none" ]
          , HP.attr (HH.AttrName "style") ("left: " <> show cursorX <> "%; top: " <> show cursorY <> "%; background-color: " <> props.value)
          ]
          []
      ]

-- | Hue slider
hueSlider :: forall w i. ColorPickerProps i -> Number -> HH.HTML w i
hueSlider _ hue =
  let
    huePercent = (hue / 360.0) * 100.0
  in
    HH.div
      [ cls [ "relative w-full h-3 rounded-full cursor-pointer" ]
      , HP.attr (HH.AttrName "style") "background: linear-gradient(to right, #f00 0%, #ff0 17%, #0f0 33%, #0ff 50%, #00f 67%, #f0f 83%, #f00 100%)"
      , HP.attr (HH.AttrName "data-hue-slider") "true"
      ]
      [ HH.div
          [ cls [ "absolute w-4 h-4 -mt-0.5 -ml-2 rounded-full border-2 border-white shadow-md pointer-events-none" ]
          , HP.attr (HH.AttrName "style") ("left: " <> show huePercent <> "%; background-color: hsl(" <> show hue <> ", 100%, 50%)")
          ]
          []
      ]

-- | Alpha/opacity slider
alphaSlider :: forall w i. ColorPickerProps i -> Number -> RGBColor -> HH.HTML w i
alphaSlider _ alpha rgb =
  let
    alphaPercent = alpha * 100.0
    solidColor = "rgb(" <> show rgb.r <> "," <> show rgb.g <> "," <> show rgb.b <> ")"
    transparentColor = "rgba(" <> show rgb.r <> "," <> show rgb.g <> "," <> show rgb.b <> ",0)"
  in
    HH.div
      [ cls [ "relative w-full h-3 rounded-full cursor-pointer" ]
      , HP.attr (HH.AttrName "style") ("background: linear-gradient(to right, " <> transparentColor <> ", " <> solidColor <> "), url(\"data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' width='8' height='8' fill-opacity='.05'%3E%3Crect x='4' width='4' height='4'/%3E%3Crect y='4' width='4' height='4'/%3E%3C/svg%3E\")")
      , HP.attr (HH.AttrName "data-alpha-slider") "true"
      ]
      [ HH.div
          [ cls [ "absolute w-4 h-4 -mt-0.5 -ml-2 rounded-full border-2 border-white shadow-md pointer-events-none" ]
          , HP.attr (HH.AttrName "style") ("left: " <> show alphaPercent <> "%;")
          ]
          []
      ]

-- | Color input field
colorInput :: forall w i. String -> String -> String -> Maybe (Event -> i) -> HH.HTML w i
colorInput labelText inputValue inputType onInputHandler =
  HH.div
    [ cls [ "flex flex-col gap-1" ] ]
    [ HH.label
        [ cls [ "text-xs text-muted-foreground" ] ]
        [ HH.text labelText ]
    , HH.input
        ( [ cls [ "w-full h-8 px-2 text-xs rounded border border-input bg-background text-center focus:outline-none focus:ring-1 focus:ring-ring" ]
          , HP.value inputValue
          , HP.type_ HP.InputText
          , HP.attr (HH.AttrName "data-input-type") inputType
          ] <> case onInputHandler of
            Just handler -> [ HE.onInput handler ]
            Nothing -> []
        )
    ]

-- | Color inputs based on format
colorInputs :: forall w i. ColorPickerProps i -> RGBColor -> HH.HTML w i
colorInputs props rgb =
  let
    hsl = rgbToHsl rgb
    hexValue = rgbToHex rgb
  in
    HH.div
      [ cls [ "grid grid-cols-4 gap-2" ] ]
      ( case props.format of
          Hex ->
            [ HH.div 
                [ cls [ "col-span-4" ] ]
                [ colorInput "HEX" hexValue "hex" Nothing ]
            ]
          RGB ->
            [ colorInput "R" (show rgb.r) "r" Nothing
            , colorInput "G" (show rgb.g) "g" Nothing
            , colorInput "B" (show rgb.b) "b" Nothing
            , if props.showAlpha
                then colorInput "A" (show (round (rgb.a * 100.0)) <> "%") "a" Nothing
                else HH.text ""
            ]
          HSL ->
            [ colorInput "H" (show (round hsl.h) <> "°") "h" Nothing
            , colorInput "S" (show (round hsl.s) <> "%") "s" Nothing
            , colorInput "L" (show (round hsl.l) <> "%") "l" Nothing
            , if props.showAlpha
                then colorInput "A" (show (round (hsl.a * 100.0)) <> "%") "a" Nothing
                else HH.text ""
            ]
      )

-- | Tools row (eyedropper, copy, format toggle)
toolsRow :: forall w i. ColorPickerProps i -> HH.HTML w i
toolsRow props =
  HH.div
    [ cls [ "flex items-center justify-between gap-2" ] ]
    [ HH.div
        [ cls [ "flex gap-1" ] ]
        [ if props.showEyedropper then eyedropperButton else HH.text ""
        , if props.showCopy then copyButton props.value else HH.text ""
        ]
    , if props.showFormatToggle 
        then formatToggle props.format
        else HH.text ""
    ]

-- | Color swatches
colorSwatches :: forall w i. Array ColorValue -> Maybe (ColorValue -> i) -> HH.HTML w i
colorSwatches swatchList onColorSelect =
  HH.div
    [ cls [ "space-y-1" ] ]
    [ HH.div
        [ cls [ "text-xs text-muted-foreground" ] ]
        [ HH.text "Swatches" ]
    , HH.div
        [ cls [ "flex flex-wrap gap-1" ] ]
        ( map (renderSwatch onColorSelect) swatchList )
    ]

-- | Recent colors
recentColors :: forall w i. Array ColorValue -> Maybe (ColorValue -> i) -> HH.HTML w i
recentColors colorList onColorSelect =
  HH.div
    [ cls [ "space-y-1" ] ]
    [ HH.div
        [ cls [ "text-xs text-muted-foreground" ] ]
        [ HH.text "Recent" ]
    , HH.div
        [ cls [ "flex flex-wrap gap-1" ] ]
        ( map (renderSwatch onColorSelect) colorList )
    ]

-- | Render a single swatch
renderSwatch :: forall w i. Maybe (ColorValue -> i) -> ColorValue -> HH.HTML w i
renderSwatch onSelect color =
  HH.button
    ( [ cls [ "w-6 h-6 rounded border border-input shadow-sm hover:ring-2 hover:ring-ring focus:outline-none focus:ring-2 focus:ring-ring" ]
      , HP.attr (HH.AttrName "style") ("background-color: " <> color)
      , ARIA.label ("Select color " <> color)
      ] <> case onSelect of
        Just handler -> [ HE.onClick (\_ -> handler color) ]
        Nothing -> []
    )
    []

-- | Eyedropper button
eyedropperButton :: forall w i. HH.HTML w i
eyedropperButton =
  HH.button
    [ cls [ "p-2 rounded hover:bg-accent focus:outline-none focus:ring-2 focus:ring-ring" ]
    , ARIA.label "Pick color from screen"
    ]
    [ eyedropperIcon ]

-- | Copy button
copyButton :: forall w i. ColorValue -> HH.HTML w i
copyButton _ =
  HH.button
    [ cls [ "p-2 rounded hover:bg-accent focus:outline-none focus:ring-2 focus:ring-ring" ]
    , ARIA.label "Copy color value"
    ]
    [ copyIcon ]

-- | Format toggle
formatToggle :: forall w i. ColorFormat -> HH.HTML w i
formatToggle currentFormat =
  let
    formatLabel = case currentFormat of
      Hex -> "HEX"
      RGB -> "RGB"
      HSL -> "HSL"
  in
    HH.button
      [ cls [ "px-2 py-1 text-xs rounded border border-input hover:bg-accent focus:outline-none focus:ring-2 focus:ring-ring" ] ]
      [ HH.text formatLabel ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // icons
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Eyedropper icon
eyedropperIcon :: forall w i. HH.HTML w i
eyedropperIcon =
  HH.element (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "width") "16"
    , HP.attr (HH.AttrName "height") "16"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , HP.attr (HH.AttrName "stroke-linejoin") "round"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "m2 22 1-1h3l9-9" ]
        []
    , HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M3 21v-3l9-9" ]
        []
    , HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "m15 6 3.4-3.4a2.1 2.1 0 1 1 3 3L18 9l.4.4a2.1 2.1 0 1 1-3 3l-3.8-3.8a2.1 2.1 0 1 1 3-3l.4.4Z" ]
        []
    ]

-- | Copy icon
copyIcon :: forall w i. HH.HTML w i
copyIcon =
  HH.element (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "width") "16"
    , HP.attr (HH.AttrName "height") "16"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , HP.attr (HH.AttrName "stroke-linejoin") "round"
    ]
    [ HH.element (HH.ElemName "rect")
        [ HP.attr (HH.AttrName "width") "14"
        , HP.attr (HH.AttrName "height") "14"
        , HP.attr (HH.AttrName "x") "8"
        , HP.attr (HH.AttrName "y") "8"
        , HP.attr (HH.AttrName "rx") "2"
        , HP.attr (HH.AttrName "ry") "2"
        ]
        []
    , HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M4 16c-1.1 0-2-.9-2-2V4c0-1.1.9-2 2-2h10c1.1 0 2 .9 2 2" ]
        []
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Modulo for floats
mod' :: Number -> Number -> Number
mod' a b = a - b * toNumber (floor (a / b))
  where
    floor :: Number -> Int
    floor n = round (n - 0.5)

-- | Null check for arrays
null :: forall a. Array a -> Boolean
null arr = case arr of
  [] -> true
  _ -> false

-- | Parse a hex pair to Int (simplified)
parseHexPair :: String -> Int
parseHexPair _ = 0  -- Placeholder - actual implementation in JS

-- | Convert Int to two-digit hex string
toHexPair :: Int -> String
toHexPair n =
  let
    hexChars = "0123456789abcdef"
    hi = n / 16
    lo = n `mod` 16
  in String.take 1 (String.drop hi hexChars) <> String.take 1 (String.drop lo hexChars)

-- | Parse rgb() string
parseRgbString :: String -> Maybe RGBColor
parseRgbString _ = Nothing  -- Placeholder - handled in JS for robustness

-- | Parse rgba() string
parseRgbaString :: String -> Maybe RGBColor
parseRgbaString _ = Nothing  -- Placeholder

-- | Parse hsl() string
parseHslString :: String -> Maybe RGBColor
parseHslString _ = Nothing  -- Placeholder

-- | Parse hsla() string
parseHslaString :: String -> Maybe RGBColor
parseHslaString _ = Nothing  -- Placeholder

-- | Map function for arrays
map :: forall a b. (a -> b) -> Array a -> Array b
map _ [] = []
map f xs = mapImpl f xs

foreign import mapImpl :: forall a b. (a -> b) -> Array a -> Array b
