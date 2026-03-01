-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // colorpicker // picker // props
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Configuration properties for the ColorPicker component.
-- |
-- | This module contains:
-- | - `PickerProps`: The complete configuration type
-- | - `defaultPickerProps`: Sensible defaults (full-featured picker)
-- | - Property builder functions for fluent configuration

module Hydrogen.Element.Compound.ColorPicker.Picker.Props
  ( -- * Props
    PickerProps
  , PickerProp
  , defaultPickerProps
  
  -- * Prop Builders
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
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Data.Maybe (Maybe(Nothing, Just))

import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Dimension.Device as Device

import Hydrogen.Element.Compound.ColorPicker.Picker.Types (PickerMsg)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Picker properties
-- |
-- | Controls all aspects of picker behavior and appearance:
-- | - **Initial value**: Starting color
-- | - **Feature toggles**: Enable/disable individual features
-- | - **Dimensions**: Picker width
-- | - **Callbacks**: Event handlers for color changes and messages
type PickerProps msg =
  { -- Initial value
    initialColor :: RGB.RGBA
  
  -- Feature toggles
  , showWheel :: Boolean
  , showSliders :: Boolean
  , showMagnifier :: Boolean
  , showPreview :: Boolean
  , showSwatches :: Boolean
  , showHarmony :: Boolean
  , showContrast :: Boolean
  , showAlpha :: Boolean
  , showEyedropper :: Boolean
  , showInputs :: Boolean
  
  -- Dimensions
  , pickerWidth :: Device.Pixel
  
  -- Callbacks
  , onChange :: Maybe (RGB.RGBA -> msg)  -- ^ Called when color changes
  , onMsg :: Maybe (PickerMsg -> msg)    -- ^ Maps internal messages to parent type
  }

-- | Property modifier type
-- |
-- | Allows fluent builder-style configuration:
-- | ```purescript
-- | colorPicker state
-- |   [ showAlpha true
-- |   , showEyedropper false
-- |   , pickerWidth (Device.px 400.0)
-- |   ]
-- | ```
type PickerProp msg = PickerProps msg -> PickerProps msg

-- | Default properties (full-featured picker)
-- |
-- | All features enabled, 320px width, red initial color.
-- | Override specific properties as needed.
defaultPickerProps :: forall msg. PickerProps msg
defaultPickerProps =
  { initialColor: RGB.rgba 255 0 0 100
  , showWheel: true
  , showSliders: true
  , showMagnifier: true
  , showPreview: true
  , showSwatches: true
  , showHarmony: true
  , showContrast: true
  , showAlpha: true
  , showEyedropper: true
  , showInputs: true
  , pickerWidth: Device.px 320.0
  , onChange: Nothing
  , onMsg: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set initial color value
initialColor :: forall msg. RGB.RGBA -> PickerProp msg
initialColor c props = props { initialColor = c }

-- | Toggle wheel mode visibility
showWheel :: forall msg. Boolean -> PickerProp msg
showWheel b props = props { showWheel = b }

-- | Toggle sliders mode visibility
showSliders :: forall msg. Boolean -> PickerProp msg
showSliders b props = props { showSliders = b }

-- | Toggle magnifier feature
showMagnifier :: forall msg. Boolean -> PickerProp msg
showMagnifier b props = props { showMagnifier = b }

-- | Toggle preview section visibility
showPreview :: forall msg. Boolean -> PickerProp msg
showPreview b props = props { showPreview = b }

-- | Toggle swatches mode visibility
showSwatches :: forall msg. Boolean -> PickerProp msg
showSwatches b props = props { showSwatches = b }

-- | Toggle harmony mode visibility
showHarmony :: forall msg. Boolean -> PickerProp msg
showHarmony b props = props { showHarmony = b }

-- | Toggle contrast checker visibility
showContrast :: forall msg. Boolean -> PickerProp msg
showContrast b props = props { showContrast = b }

-- | Toggle alpha slider visibility
showAlpha :: forall msg. Boolean -> PickerProp msg
showAlpha b props = props { showAlpha = b }

-- | Toggle eyedropper button visibility
showEyedropper :: forall msg. Boolean -> PickerProp msg
showEyedropper b props = props { showEyedropper = b }

-- | Toggle input fields visibility
showInputs :: forall msg. Boolean -> PickerProp msg
showInputs b props = props { showInputs = b }

-- | Set picker width
pickerWidth :: forall msg. Device.Pixel -> PickerProp msg
pickerWidth w props = props { pickerWidth = w }

-- | Set color change callback
-- |
-- | Called when the user commits a color change.
onChange :: forall msg. (RGB.RGBA -> msg) -> PickerProp msg
onChange handler props = props { onChange = Just handler }

-- | Set internal message handler
-- |
-- | This maps PickerMsg to the parent's message type, enabling full interactivity.
-- | Without this, the picker renders but produces no messages.
-- |
-- | ## Example
-- |
-- | ```purescript
-- | data MyMsg = PickerMsg PickerMsg | ...
-- |
-- | colorPicker state [ onMsg PickerMsg ]
-- | ```
onMsg :: forall msg. (PickerMsg -> msg) -> PickerProp msg
onMsg handler props = props { onMsg = Just handler }
