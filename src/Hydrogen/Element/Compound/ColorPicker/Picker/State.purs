-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // colorpicker // picker // state
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | State management for the ColorPicker component.
-- |
-- | This module contains:
-- | - `PickerState`: The complete internal state
-- | - `update`: Pure state machine transition function
-- | - Helper functions for state manipulation

module Hydrogen.Element.Compound.ColorPicker.Picker.State
  ( -- * State
    PickerState
  , initialPickerState
  
  -- * Update
  , update
  
  -- * Helpers
  , extractHueFromRGBA
  , rgbaToHsl
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( not
  , (-)
  , (<=)
  , (==)
  )

import Data.Array (foldl, length, drop, snoc)

import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Color.HSL as HSL
import Hydrogen.Schema.Color.Hue as Hue
import Hydrogen.Schema.Color.Saturation as Sat
import Hydrogen.Schema.Color.Lightness as Light
import Hydrogen.Schema.Color.Opacity as Opacity
import Hydrogen.Schema.Color.Conversion as Convert

import Hydrogen.Element.Compound.ColorPicker.Picker.Types 
  ( PickerTab(TabWheel)
  , PickerMsg(SetColor, SetHue, SetSaturation, SetLightness, SetOpacity, SetTab, SetCursor, ToggleMagnifier, SelectSwatch, SelectHarmony, CopyValue, ActivateEyedropper)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Picker internal state
-- |
-- | Tracks all mutable aspects of the color picker:
-- | - Current and original colors (for comparison/reset)
-- | - Active interface tab
-- | - Cursor position (for magnifier feature)
-- | - Recent color history
-- | - Magnifier activation state
type PickerState =
  { currentColor :: RGB.RGBA
  , originalColor :: RGB.RGBA
  , activeTab :: PickerTab
  , cursorX :: Number
  , cursorY :: Number
  , recentColors :: Array RGB.RGBA
  , magnifierActive :: Boolean
  }

-- | Initial picker state
-- |
-- | Creates a fresh state with the given color as both current and original.
-- | Recent colors history starts empty.
initialPickerState :: RGB.RGBA -> PickerState
initialPickerState color =
  { currentColor: color
  , originalColor: color
  , activeTab: TabWheel
  , cursorX: 0.0
  , cursorY: 0.0
  , recentColors: []
  , magnifierActive: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // update
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pure state update function
-- |
-- | Takes a message and current state, returns the new state.
-- | This implements the complete state machine for the color picker.
-- |
-- | ## Design
-- |
-- | Each message maps to a single, deterministic state transformation.
-- | Side effects (like clipboard copy or eyedropper) are signaled via
-- | messages but handled by the parent component.
update :: PickerMsg -> PickerState -> PickerState
update msg state = case msg of
  SetColor rgba ->
    state 
      { currentColor = rgba
      , recentColors = addToRecent rgba state.recentColors
      }
  
  SetHue newHue ->
    let
      -- Get current HSL, replace hue, convert back to RGBA
      currentHsl = rgbaToHsl state.currentColor
      currentAlpha = Opacity.unwrap (RGB.alpha state.currentColor)
      newHsl = HSL.hsl 
        (Hue.unwrap newHue) 
        (Sat.unwrap (HSL.saturation currentHsl)) 
        (Light.unwrap (HSL.lightness currentHsl))
      newRgb = Convert.hslToRgb newHsl
      rec = RGB.rgbToRecord newRgb
      newRgba = RGB.rgba rec.r rec.g rec.b currentAlpha
    in
      state { currentColor = newRgba }
  
  SetSaturation newSat ->
    let
      currentHsl = rgbaToHsl state.currentColor
      currentAlpha = Opacity.unwrap (RGB.alpha state.currentColor)
      newHsl = HSL.hsl 
        (Hue.unwrap (HSL.hue currentHsl)) 
        (Sat.unwrap newSat) 
        (Light.unwrap (HSL.lightness currentHsl))
      newRgb = Convert.hslToRgb newHsl
      rec = RGB.rgbToRecord newRgb
      newRgba = RGB.rgba rec.r rec.g rec.b currentAlpha
    in
      state { currentColor = newRgba }
  
  SetLightness newLight ->
    let
      currentHsl = rgbaToHsl state.currentColor
      currentAlpha = Opacity.unwrap (RGB.alpha state.currentColor)
      newHsl = HSL.hsl 
        (Hue.unwrap (HSL.hue currentHsl)) 
        (Sat.unwrap (HSL.saturation currentHsl)) 
        (Light.unwrap newLight)
      newRgb = Convert.hslToRgb newHsl
      rec = RGB.rgbToRecord newRgb
      newRgba = RGB.rgba rec.r rec.g rec.b currentAlpha
    in
      state { currentColor = newRgba }
  
  SetOpacity newOpacity ->
    let
      rgb = RGB.fromRGBA state.currentColor
      rec = RGB.rgbToRecord rgb
      newRgba = RGB.rgba rec.r rec.g rec.b (Opacity.unwrap newOpacity)
    in
      state { currentColor = newRgba }
  
  SetTab tab ->
    state { activeTab = tab }
  
  SetCursor x y ->
    state { cursorX = x, cursorY = y, magnifierActive = true }
  
  ToggleMagnifier ->
    state { magnifierActive = not state.magnifierActive }
  
  SelectSwatch rgba ->
    state 
      { currentColor = rgba
      , recentColors = addToRecent rgba state.recentColors
      }
  
  SelectHarmony hsl ->
    let
      newRgb = Convert.hslToRgb hsl
      rec = RGB.rgbToRecord newRgb
      currentAlpha = Opacity.unwrap (RGB.alpha state.currentColor)
      newRgba = RGB.rgba rec.r rec.g rec.b currentAlpha
    in
      state 
        { currentColor = newRgba
        , recentColors = addToRecent newRgba state.recentColors
        }
  
  CopyValue _value ->
    -- Copy is a side effect handled by the parent; state unchanged
    state
  
  ActivateEyedropper ->
    -- Eyedropper activation is handled by parent; state unchanged
    state

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract hue from RGBA color by converting through HSL
extractHueFromRGBA :: RGB.RGBA -> Hue.Hue
extractHueFromRGBA rgba =
  let
    rgb = RGB.fromRGBA rgba
    hsl = Convert.rgbToHsl rgb
  in
    HSL.hue hsl

-- | Convert RGBA to HSL for manipulation
rgbaToHsl :: RGB.RGBA -> HSL.HSL
rgbaToHsl rgba = Convert.rgbToHsl (RGB.fromRGBA rgba)

-- | Add color to recent list, keeping max 16 entries
-- |
-- | Deduplicates by removing existing entries before adding.
addToRecent :: RGB.RGBA -> Array RGB.RGBA -> Array RGB.RGBA
addToRecent color recents =
  let
    -- Remove if already present to avoid duplicates
    filtered = filterNot (\c -> c == color) recents
    -- Add to end, take last 16
    added = snoc filtered color
  in
    takeLast 16 added

-- | Filter out elements matching predicate
filterNot :: forall a. (a -> Boolean) -> Array a -> Array a
filterNot pred = foldl (\acc x -> if pred x then acc else snoc acc x) []

-- | Take last n elements from array
takeLast :: forall a. Int -> Array a -> Array a
takeLast n arr = 
  let len = length arr
  in if len <= n then arr else drop (len - n) arr
