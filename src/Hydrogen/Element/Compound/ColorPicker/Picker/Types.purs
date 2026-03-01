-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // colorpicker // picker // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core types for the ColorPicker component.
-- |
-- | This module contains the foundational types used throughout the picker:
-- | - `PickerTab`: The available interface tabs
-- | - `PickerMsg`: Messages the picker can produce/respond to

module Hydrogen.Element.Compound.ColorPicker.Picker.Types
  ( -- * Tabs
    PickerTab(TabWheel, TabSliders, TabSwatches, TabHarmony)
  
  -- * Messages
  , PickerMsg(SetColor, SetHue, SetSaturation, SetLightness, SetOpacity, SetTab, SetCursor, ToggleMagnifier, SelectSwatch, SelectHarmony, CopyValue, ActivateEyedropper)
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  )

import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Color.HSL as HSL
import Hydrogen.Schema.Color.Hue as Hue
import Hydrogen.Schema.Color.Saturation as Sat
import Hydrogen.Schema.Color.Lightness as Light
import Hydrogen.Schema.Color.Opacity as Opacity

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // tabs
-- ═════════════════════════════════════════════════════════════════════════════

-- | Picker interface tabs
-- |
-- | The color picker supports multiple interaction modes:
-- | - **Wheel**: Hue wheel with saturation/brightness panel
-- | - **Sliders**: Individual H/S/L sliders
-- | - **Swatches**: Preset color palettes
-- | - **Harmony**: Color harmony calculations
data PickerTab
  = TabWheel      -- ^ Wheel + panel mode
  | TabSliders    -- ^ HSL/RGB sliders mode
  | TabSwatches   -- ^ Preset palettes mode
  | TabHarmony    -- ^ Color harmonies mode

derive instance eqPickerTab :: Eq PickerTab

instance showPickerTab :: Show PickerTab where
  show TabWheel = "Wheel"
  show TabSliders = "Sliders"
  show TabSwatches = "Swatches"
  show TabHarmony = "Harmony"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // messages
-- ═════════════════════════════════════════════════════════════════════════════

-- | Messages the picker can produce
-- |
-- | These messages form the complete vocabulary of picker interactions:
-- | - Color component changes (hue, saturation, lightness, opacity)
-- | - Tab navigation
-- | - Magnifier control
-- | - Swatch and harmony selection
-- | - Copy operations
-- | - Eyedropper activation
data PickerMsg
  = SetColor RGB.RGBA              -- ^ Set the complete color
  | SetHue Hue.Hue                 -- ^ Adjust hue component
  | SetSaturation Sat.Saturation   -- ^ Adjust saturation component
  | SetLightness Light.Lightness   -- ^ Adjust lightness component
  | SetOpacity Opacity.Opacity     -- ^ Adjust opacity component
  | SetTab PickerTab               -- ^ Switch active tab
  | SetCursor Number Number        -- ^ Update cursor position (for magnifier)
  | ToggleMagnifier                -- ^ Toggle magnifier visibility
  | SelectSwatch RGB.RGBA          -- ^ Select a preset swatch color
  | SelectHarmony HSL.HSL          -- ^ Select a harmony-derived color
  | CopyValue String               -- ^ Copy a formatted value to clipboard
  | ActivateEyedropper             -- ^ Activate screen color picker

derive instance eqPickerMsg :: Eq PickerMsg
