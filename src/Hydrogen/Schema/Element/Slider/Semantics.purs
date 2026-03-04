-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // schema // element // slider // semantics
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | SliderSemantics — Purpose, identity, and accessibility atoms.
-- |
-- | ## Verified Atoms (re-exported from Schema pillars)
-- |
-- | - UUID5 (Attestation.UUID5) — Deterministic identity
-- |
-- | ## Slider Semantics Model
-- |
-- | A slider control has:
-- | - Purpose: What it controls (volume, hue, brightness, etc.)
-- | - ARIA role: "slider" for single-thumb, "range" for dual-thumb (future)
-- | - Value: Current value with min/max bounds and optional units
-- | - Label: Accessible name for screen readers
-- |
-- | ## Accessibility (WCAG 2.1)
-- |
-- | - role="slider" indicates range input control
-- | - aria-valuenow indicates current value
-- | - aria-valuemin indicates minimum value
-- | - aria-valuemax indicates maximum value
-- | - aria-valuetext provides human-readable value (e.g., "50%", "180°")
-- | - aria-label/aria-labelledby provides accessible name
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Attestation.UUID5 (UUID5, nsSlider)

module Hydrogen.Schema.Element.Slider.Semantics
  ( -- * Slider Purpose
    SliderPurpose
      ( PurposeHue
      , PurposeSaturation
      , PurposeLightness
      , PurposeVolume
      , PurposeOpacity
      , PurposeTemperature
      , PurposeZoom
      , PurposeProgress
      , PurposeBalance
      , PurposeBrightness
      , PurposeContrast
      , PurposeSpeed
      , PurposeCustom
      )
  , purposeToString
  , purposeDefaultLabel
  , purposeDefaultUnit
  
  -- * Slider Value Range
  , SliderRange
  , defaultRange
  , percentRange
  , degreeRange
  , volumeRange
  , kelvinRange
  , zoomRange
  
  -- * Slider Semantics Record
  , SliderSemantics
  , defaultSemantics
  , hueSemantics
  , saturationSemantics
  , lightnessSemantics
  , volumeSemantics
  , opacitySemantics
  , temperatureSemantics
  , zoomSemantics
  
  -- * Semantics Accessors
  , getPurpose
  , getLabel
  , getDescription
  , getAriaRole
  , getAriaValueText
  , getRange
  , isDisabled
  
  -- * Semantics Modifiers
  , setPurpose
  , setLabel
  , setDescription
  , setDisabled
  , setRange
  , setUnit
  , setAriaDescribedBy
  
  -- * UUID5 Identity
  , sliderId
  , sliderIdString
  
  -- * Re-exports
  , module Hydrogen.Schema.Attestation.UUID5
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Prim (Boolean, Number, String)

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Attestation.UUID5
  ( UUID5
  , uuid5
  , toString
  , nsSlider
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // slider purpose
-- ═════════════════════════════════════════════════════════════════════════════

-- | Slider purpose — what kind of value does this slider control?
-- |
-- | Purpose determines:
-- | - Default labeling
-- | - Unit suffix (%, °, dB, etc.)
-- | - Value range and wrapping behavior
data SliderPurpose
  = PurposeHue           -- ^ Hue angle (0-360°, wraps)
  | PurposeSaturation    -- ^ Saturation percentage (0-100%)
  | PurposeLightness     -- ^ Lightness percentage (0-100%)
  | PurposeVolume        -- ^ Audio volume (0-100%)
  | PurposeOpacity       -- ^ Opacity/alpha (0-100%)
  | PurposeTemperature   -- ^ Color temperature (Kelvin)
  | PurposeZoom          -- ^ Zoom level (percentage)
  | PurposeProgress      -- ^ Generic progress (0-100%)
  | PurposeBalance       -- ^ Audio balance (L-R, -100 to +100)
  | PurposeBrightness    -- ^ Display brightness (0-100%)
  | PurposeContrast      -- ^ Display contrast (0-100%)
  | PurposeSpeed         -- ^ Playback speed (0.25x - 2x)
  | PurposeCustom String -- ^ Custom purpose with description

derive instance eqSliderPurpose :: Eq SliderPurpose
derive instance ordSliderPurpose :: Ord SliderPurpose

instance showSliderPurpose :: Show SliderPurpose where
  show PurposeHue = "hue"
  show PurposeSaturation = "saturation"
  show PurposeLightness = "lightness"
  show PurposeVolume = "volume"
  show PurposeOpacity = "opacity"
  show PurposeTemperature = "temperature"
  show PurposeZoom = "zoom"
  show PurposeProgress = "progress"
  show PurposeBalance = "balance"
  show PurposeBrightness = "brightness"
  show PurposeContrast = "contrast"
  show PurposeSpeed = "speed"
  show (PurposeCustom s) = "custom:" <> s

-- | Convert purpose to string for data attributes.
purposeToString :: SliderPurpose -> String
purposeToString = show

-- | Get default label for a purpose.
-- |
-- | These are fallback labels — specific sliders should override.
purposeDefaultLabel :: SliderPurpose -> String
purposeDefaultLabel = case _ of
  PurposeHue -> "Hue"
  PurposeSaturation -> "Saturation"
  PurposeLightness -> "Lightness"
  PurposeVolume -> "Volume"
  PurposeOpacity -> "Opacity"
  PurposeTemperature -> "Temperature"
  PurposeZoom -> "Zoom"
  PurposeProgress -> "Progress"
  PurposeBalance -> "Balance"
  PurposeBrightness -> "Brightness"
  PurposeContrast -> "Contrast"
  PurposeSpeed -> "Speed"
  PurposeCustom s -> s

-- | Get default unit suffix for a purpose.
-- |
-- | Used in aria-valuetext for screen readers.
purposeDefaultUnit :: SliderPurpose -> String
purposeDefaultUnit = case _ of
  PurposeHue -> "°"
  PurposeSaturation -> "%"
  PurposeLightness -> "%"
  PurposeVolume -> "%"
  PurposeOpacity -> "%"
  PurposeTemperature -> "K"
  PurposeZoom -> "%"
  PurposeProgress -> "%"
  PurposeBalance -> ""
  PurposeBrightness -> "%"
  PurposeContrast -> "%"
  PurposeSpeed -> "x"
  PurposeCustom _ -> ""

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // slider range
-- ═════════════════════════════════════════════════════════════════════════════

-- | Slider value range — min, max, and step for ARIA.
-- |
-- | ## Fields
-- |
-- | - min: Minimum value (aria-valuemin)
-- | - max: Maximum value (aria-valuemax)
-- | - step: Step increment (for keyboard navigation)
-- | - unit: Unit suffix for aria-valuetext (e.g., "%", "°", "K")
type SliderRange =
  { min :: Number
  , max :: Number
  , step :: Number
  , unit :: String
  }

-- | Default range (0-100, step 1, no unit).
defaultRange :: SliderRange
defaultRange =
  { min: 0.0
  , max: 100.0
  , step: 1.0
  , unit: ""
  }

-- | Percentage range (0-100%).
percentRange :: SliderRange
percentRange =
  { min: 0.0
  , max: 100.0
  , step: 1.0
  , unit: "%"
  }

-- | Degree range (0-360°, for hue).
degreeRange :: SliderRange
degreeRange =
  { min: 0.0
  , max: 360.0
  , step: 1.0
  , unit: "°"
  }

-- | Volume range (0-100%).
volumeRange :: SliderRange
volumeRange =
  { min: 0.0
  , max: 100.0
  , step: 1.0
  , unit: "%"
  }

-- | Kelvin range (1000-40000K, step 100).
kelvinRange :: SliderRange
kelvinRange =
  { min: 1000.0
  , max: 40000.0
  , step: 100.0
  , unit: "K"
  }

-- | Zoom range (10-400%, step 10).
zoomRange :: SliderRange
zoomRange =
  { min: 10.0
  , max: 400.0
  , step: 10.0
  , unit: "%"
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // slider semantics
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete slider semantics — purpose, identity, and accessibility.
-- |
-- | ## ARIA Attributes
-- |
-- | - role="slider" (always, for single-thumb sliders)
-- | - aria-valuenow (current value)
-- | - aria-valuemin (minimum)
-- | - aria-valuemax (maximum)
-- | - aria-valuetext (human-readable, e.g., "50%")
-- | - aria-label (or aria-labelledby)
-- | - aria-describedby (optional)
-- |
-- | ## UUID5 Identity
-- |
-- | Slider identity is derived from:
-- | - uniqueKey
-- | - purpose
-- | - label
-- |
-- | Same inputs = same UUID5. Always. Everywhere.
type SliderSemantics =
  { -- Purpose and identity
    purpose :: SliderPurpose          -- ^ What kind of slider
  , uniqueKey :: String               -- ^ Unique identifier for UUID5
    -- Labels
  , label :: String                   -- ^ Visible or ARIA label
  , labelledBy :: Maybe String        -- ^ ID of labelling element
  , description :: Maybe String       -- ^ Extended description
  , describedBy :: Maybe String       -- ^ ID of describing element
    -- Value range
  , range :: SliderRange              -- ^ Min, max, step, unit
    -- State
  , disabled :: Boolean               -- ^ Is slider disabled
  }

-- | Default slider semantics.
-- |
-- | Progress purpose, 0-100 range, "Value" label.
defaultSemantics :: String -> SliderSemantics
defaultSemantics key =
  { purpose: PurposeProgress
  , uniqueKey: key
  , label: "Value"
  , labelledBy: Nothing
  , description: Nothing
  , describedBy: Nothing
  , range: percentRange
  , disabled: false
  }

-- | Hue slider semantics.
hueSemantics :: String -> SliderSemantics
hueSemantics key =
  { purpose: PurposeHue
  , uniqueKey: key
  , label: "Hue"
  , labelledBy: Nothing
  , description: Just "Select color hue (0-360 degrees)"
  , describedBy: Nothing
  , range: degreeRange
  , disabled: false
  }

-- | Saturation slider semantics.
saturationSemantics :: String -> SliderSemantics
saturationSemantics key =
  { purpose: PurposeSaturation
  , uniqueKey: key
  , label: "Saturation"
  , labelledBy: Nothing
  , description: Just "Adjust color saturation"
  , describedBy: Nothing
  , range: percentRange
  , disabled: false
  }

-- | Lightness slider semantics.
lightnessSemantics :: String -> SliderSemantics
lightnessSemantics key =
  { purpose: PurposeLightness
  , uniqueKey: key
  , label: "Lightness"
  , labelledBy: Nothing
  , description: Just "Adjust color lightness"
  , describedBy: Nothing
  , range: percentRange
  , disabled: false
  }

-- | Volume slider semantics.
volumeSemantics :: String -> SliderSemantics
volumeSemantics key =
  { purpose: PurposeVolume
  , uniqueKey: key
  , label: "Volume"
  , labelledBy: Nothing
  , description: Nothing
  , describedBy: Nothing
  , range: volumeRange
  , disabled: false
  }

-- | Opacity slider semantics.
opacitySemantics :: String -> SliderSemantics
opacitySemantics key =
  { purpose: PurposeOpacity
  , uniqueKey: key
  , label: "Opacity"
  , labelledBy: Nothing
  , description: Just "Adjust transparency"
  , describedBy: Nothing
  , range: percentRange
  , disabled: false
  }

-- | Temperature slider semantics.
temperatureSemantics :: String -> SliderSemantics
temperatureSemantics key =
  { purpose: PurposeTemperature
  , uniqueKey: key
  , label: "Color Temperature"
  , labelledBy: Nothing
  , description: Just "Adjust color temperature from warm to cool"
  , describedBy: Nothing
  , range: kelvinRange
  , disabled: false
  }

-- | Zoom slider semantics.
zoomSemantics :: String -> SliderSemantics
zoomSemantics key =
  { purpose: PurposeZoom
  , uniqueKey: key
  , label: "Zoom"
  , labelledBy: Nothing
  , description: Nothing
  , describedBy: Nothing
  , range: zoomRange
  , disabled: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get purpose.
getPurpose :: SliderSemantics -> SliderPurpose
getPurpose s = s.purpose

-- | Get label.
getLabel :: SliderSemantics -> String
getLabel s = s.label

-- | Get description.
getDescription :: SliderSemantics -> Maybe String
getDescription s = s.description

-- | Get ARIA role (always "slider" for single-thumb sliders).
getAriaRole :: SliderSemantics -> String
getAriaRole _ = "slider"

-- | Get ARIA valuetext for a given numeric value.
-- |
-- | Combines the value with the unit suffix.
-- | Example: getAriaValueText 180.0 hueSemantics = "180°"
getAriaValueText :: Number -> SliderSemantics -> String
getAriaValueText value sem = show value <> sem.range.unit

-- | Get value range.
getRange :: SliderSemantics -> SliderRange
getRange s = s.range

-- | Is slider disabled?
isDisabled :: SliderSemantics -> Boolean
isDisabled s = s.disabled

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set purpose.
setPurpose :: SliderPurpose -> SliderSemantics -> SliderSemantics
setPurpose p s = s { purpose = p }

-- | Set label.
setLabel :: String -> SliderSemantics -> SliderSemantics
setLabel l s = s { label = l }

-- | Set description.
setDescription :: String -> SliderSemantics -> SliderSemantics
setDescription d s = s { description = Just d }

-- | Set disabled state.
setDisabled :: Boolean -> SliderSemantics -> SliderSemantics
setDisabled d s = s { disabled = d }

-- | Set value range.
setRange :: SliderRange -> SliderSemantics -> SliderSemantics
setRange r s = s { range = r }

-- | Set unit suffix.
setUnit :: String -> SliderSemantics -> SliderSemantics
setUnit u s = s { range = s.range { unit = u } }

-- | Set aria-describedby ID.
setAriaDescribedBy :: String -> SliderSemantics -> SliderSemantics
setAriaDescribedBy id s = s { describedBy = Just id }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // uuid5 identity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate deterministic UUID5 for a slider.
-- |
-- | Identity is derived from:
-- | - uniqueKey
-- | - purpose
-- | - label
-- |
-- | Same inputs = same UUID5. Always. Everywhere.
sliderId :: SliderSemantics -> UUID5
sliderId sem =
  let
    canonical = sem.uniqueKey <> "|" <> show sem.purpose <> "|" <> sem.label
  in
    uuid5 nsSlider canonical

-- | Get slider UUID5 as string (36 chars with dashes).
sliderIdString :: SliderSemantics -> String
sliderIdString sem = toString (sliderId sem)
