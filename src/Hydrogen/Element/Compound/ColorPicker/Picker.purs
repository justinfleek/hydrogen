-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // element // colorpicker // picker
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ColorPicker — The ULTIMATE color picker orchestrator.
-- |
-- | ## Design Philosophy
-- |
-- | This is the main color picker component that composes all sub-components
-- | into a unified, professional-grade color selection interface.
-- |
-- | ## Features
-- |
-- | - **Wheel mode**: Hue wheel with saturation/brightness panel
-- | - **Slider mode**: Individual H/S/L or R/G/B sliders
-- | - **Magnifier**: Pixel-level precision with zoom loupe
-- | - **All formats**: HEX, RGB, HSL, HSV displayed simultaneously
-- | - **Swatches**: Preset palettes and recent colors
-- | - **Harmony**: Complementary, analogous, triadic palettes
-- | - **Contrast**: WCAG accessibility checker
-- | - **Alpha**: Full opacity control
-- | - **Eyedropper**: Screen color picking (requires FFI)
-- |
-- | ## State Management
-- |
-- | The picker maintains internal state for:
-- | - Current color (RGBA)
-- | - Original color (for comparison)
-- | - Active tab/mode
-- | - Cursor position (for magnifier)
-- | - Recent colors history
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from:
-- | - `Picker.Types`: Tabs and Messages
-- | - `Picker.State`: State and update function
-- | - `Picker.Props`: Configuration properties
-- | - `Picker.Sliders`: HSL slider rendering
-- | - `Picker.Render`: Main component and section renders

module Hydrogen.Element.Compound.ColorPicker.Picker
  ( -- * Types
    module Types
  
  -- * State  
  , module State
  
  -- * Props
  , module Props
  
  -- * Render
  , module Render
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

-- Types: Tabs and Messages
import Hydrogen.Element.Compound.ColorPicker.Picker.Types 
  ( PickerTab(TabWheel, TabSliders, TabSwatches, TabHarmony)
  , PickerMsg(SetColor, SetHue, SetSaturation, SetLightness, SetOpacity, SetTab, SetCursor, ToggleMagnifier, SelectSwatch, SelectHarmony, CopyValue, ActivateEyedropper)
  ) as Types

-- State: State type, initial state, update function, helpers
import Hydrogen.Element.Compound.ColorPicker.Picker.State 
  ( PickerState
  , initialPickerState
  , update
  , extractHueFromRGBA
  , rgbaToHsl
  ) as State

-- Props: Configuration type, defaults, builders
import Hydrogen.Element.Compound.ColorPicker.Picker.Props 
  ( PickerProps
  , PickerProp
  , defaultPickerProps
  , initialColor
  , showWheel
  , showSliders
  , showMagnifier
  , showPreview
  , showSwatches
  , showHarmony
  , showContrast
  , showAlpha
  , showEyedropper
  , showInputs
  , pickerWidth
  , onChange
  , onMsg
  ) as Props

-- Render: Main component
import Hydrogen.Element.Compound.ColorPicker.Picker.Render (colorPicker) as Render
