-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // schema // element // knob // semantics
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | KnobSemantics — Purpose, identity, and accessibility atoms.
-- |
-- | ## Design Philosophy
-- |
-- | Semantics describe WHAT the knob means, not how it looks or behaves.
-- | This includes:
-- | - Purpose (volume, pan, frequency, rotation, medical rate)
-- | - ARIA attributes for accessibility
-- | - Value formatters for display
-- | - UUID5 deterministic identity
-- |
-- | ## Domain-Specific Semantics
-- |
-- | Different domains have very different semantic requirements:
-- |
-- | **Medical**:
-- | - aria-valuetext MUST include units: "120 milliliters per hour"
-- | - Critical values trigger aria-live announcements
-- | - Purpose is life-critical (IV drip rate, medication dose)
-- |
-- | **DAW**:
-- | - Logarithmic scaling for frequency (20Hz-20kHz over 270 degrees)
-- | - Bipolar center semantics (pan: L64-Center-R64)
-- | - dB display with proper formatting (+3.2dB, -inf)
-- |
-- | **Game**:
-- | - Simple percentage or level display
-- | - May omit ARIA for fullscreen game context
-- |
-- | ## Value Formatters
-- |
-- | Formatters convert raw values to human-readable strings:
-- | - Volume: "80%", "-12.5 dB"
-- | - Pan: "L 32", "Center", "R 64"
-- | - Frequency: "1.2 kHz", "440 Hz"
-- | - Rate: "2.0x", "0.5x"
-- | - Medical: "120 mL/hr"
-- |
-- | ## Verified Atoms (re-exported from Schema pillars)
-- |
-- | - UUID5 (Attestation.UUID5) — Deterministic identity
-- | - Range (Dimension.Range) — Value bounds
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Attestation.UUID5 (UUID5, nsKnob)
-- | - Hydrogen.Schema.Dimension.Range (value bounds)

module Hydrogen.Schema.Element.Knob.Semantics
  ( -- * Knob Purpose
    KnobPurpose
      ( PurposeVolume
      , PurposePan
      , PurposeFrequency
      , PurposeResonance
      , PurposeAttack
      , PurposeDecay
      , PurposeRelease
      , PurposeRate
      , PurposeRotation
      , PurposeHue
      , PurposeMedicalRate
      , PurposeMedicalDose
      , PurposeCustom
      )
  , purposeToString
  , purposeDefaultLabel
  , purposeDefaultUnit
  , purposeIsLogarithmic
  , purposeIsBipolar
  
  -- * Scale Type
  , ScaleType
      ( ScaleLinear
      , ScaleLogarithmic
      , ScaleExponential
      )
  
  -- * Value Range
  , KnobRange
  , defaultRange
  , volumeRange
  , panRange
  , frequencyRange
  , attackRange
  , rateRange
  , rotationRange
  , medicalRateRange
  
  -- * Value Formatter
  , ValueFormatter
  , formatPercent
  , formatDecibels
  , formatPan
  , formatFrequency
  , formatRate
  , formatMedicalRate
  , formatDegrees
  , formatCustom
  
  -- * Knob Semantics Record
  , KnobSemantics
  , defaultSemantics
  , volumeSemantics
  , panSemantics
  , frequencySemantics
  , rateSemantics
  , rotationSemantics
  , medicalSemantics
  
  -- * Semantics Accessors
  , getPurpose
  , getLabel
  , getDescription
  , getAriaRole
  , getAriaValueText
  , getRange
  , getScaleType
  , isDisabled
  , isLogarithmic
  
  -- * Semantics Modifiers
  , setPurpose
  , setLabel
  , setDescription
  , setDisabled
  , setRange
  , setScaleType
  , setFormatter
  , setAriaDescribedBy
  
  -- * UUID5 Identity
  , knobId
  , knobIdString
  
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
  , negate
  , (/)
  , (-)
  , (*)
  , (+)
  , (<>)
  , (==)
  , (&&)
  , (||)
  , (>)
  , (<)
  , (>=)
  , (<=)
  )

import Prim (Boolean, Int, Number, String)

import Data.Maybe (Maybe(Just, Nothing))

import Data.Number (abs, log) as Number

import Hydrogen.Schema.Attestation.UUID5
  ( UUID5
  , uuid5
  , toString
  , nsKnob
  )

import Hydrogen.Schema.Bounded as Bounded

import Data.Int (floor, toNumber) as Int

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // knob purpose
-- ═════════════════════════════════════════════════════════════════════════════

-- | Knob purpose — what kind of parameter does this knob control?
-- |
-- | Purpose determines:
-- | - Default labeling and units
-- | - Value scaling (linear, log, exponential)
-- | - Bipolar vs unipolar semantics
-- | - ARIA value text formatting
data KnobPurpose
  = PurposeVolume         -- ^ Audio volume (0-100% or dB)
  | PurposePan            -- ^ Stereo pan (L64 to R64, center = 0)
  | PurposeFrequency      -- ^ Frequency (20Hz-20kHz, logarithmic)
  | PurposeResonance      -- ^ Filter resonance/Q (0-100%)
  | PurposeAttack         -- ^ Envelope attack (0-10000ms, logarithmic)
  | PurposeDecay          -- ^ Envelope decay (0-10000ms, logarithmic)
  | PurposeRelease        -- ^ Envelope release (0-10000ms, logarithmic)
  | PurposeRate           -- ^ Playback rate (0.25x-4.0x)
  | PurposeRotation       -- ^ Generic rotation (0-360 degrees)
  | PurposeHue            -- ^ Color hue (0-360 degrees, wraps)
  | PurposeMedicalRate    -- ^ IV drip rate (mL/hr)
  | PurposeMedicalDose    -- ^ Medication dose (mg, mcg)
  | PurposeCustom String  -- ^ Custom purpose with description

derive instance eqKnobPurpose :: Eq KnobPurpose
derive instance ordKnobPurpose :: Ord KnobPurpose

instance showKnobPurpose :: Show KnobPurpose where
  show PurposeVolume = "volume"
  show PurposePan = "pan"
  show PurposeFrequency = "frequency"
  show PurposeResonance = "resonance"
  show PurposeAttack = "attack"
  show PurposeDecay = "decay"
  show PurposeRelease = "release"
  show PurposeRate = "rate"
  show PurposeRotation = "rotation"
  show PurposeHue = "hue"
  show PurposeMedicalRate = "medical-rate"
  show PurposeMedicalDose = "medical-dose"
  show (PurposeCustom s) = "custom:" <> s

-- | Convert purpose to string for data attributes.
purposeToString :: KnobPurpose -> String
purposeToString = show

-- | Get default label for a purpose.
purposeDefaultLabel :: KnobPurpose -> String
purposeDefaultLabel = case _ of
  PurposeVolume -> "Volume"
  PurposePan -> "Pan"
  PurposeFrequency -> "Frequency"
  PurposeResonance -> "Resonance"
  PurposeAttack -> "Attack"
  PurposeDecay -> "Decay"
  PurposeRelease -> "Release"
  PurposeRate -> "Rate"
  PurposeRotation -> "Rotation"
  PurposeHue -> "Hue"
  PurposeMedicalRate -> "Flow Rate"
  PurposeMedicalDose -> "Dose"
  PurposeCustom s -> s

-- | Get default unit suffix for a purpose.
purposeDefaultUnit :: KnobPurpose -> String
purposeDefaultUnit = case _ of
  PurposeVolume -> "%"
  PurposePan -> ""           -- Pan has complex formatting (L/R)
  PurposeFrequency -> "Hz"
  PurposeResonance -> "%"
  PurposeAttack -> "ms"
  PurposeDecay -> "ms"
  PurposeRelease -> "ms"
  PurposeRate -> "x"
  PurposeRotation -> "°"
  PurposeHue -> "°"
  PurposeMedicalRate -> "mL/hr"
  PurposeMedicalDose -> "mg"
  PurposeCustom _ -> ""

-- | Does this purpose use logarithmic scaling?
purposeIsLogarithmic :: KnobPurpose -> Boolean
purposeIsLogarithmic = case _ of
  PurposeFrequency -> true
  PurposeAttack -> true
  PurposeDecay -> true
  PurposeRelease -> true
  PurposeRate -> true
  _ -> false

-- | Is this purpose bipolar (center = 0)?
purposeIsBipolar :: KnobPurpose -> Boolean
purposeIsBipolar = case _ of
  PurposePan -> true
  _ -> false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // scale type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scale type for value mapping.
-- |
-- | - Linear: Even distribution across arc
-- | - Logarithmic: More resolution at low end (frequency, time)
-- | - Exponential: More resolution at high end
data ScaleType
  = ScaleLinear       -- ^ Even distribution
  | ScaleLogarithmic  -- ^ Log scale (more low-end resolution)
  | ScaleExponential  -- ^ Exponential scale (more high-end resolution)

derive instance eqScaleType :: Eq ScaleType
derive instance ordScaleType :: Ord ScaleType

instance showScaleType :: Show ScaleType where
  show ScaleLinear = "linear"
  show ScaleLogarithmic = "logarithmic"
  show ScaleExponential = "exponential"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // value range
-- ═════════════════════════════════════════════════════════════════════════════

-- | Knob value range — min, max, step, and display info.
-- |
-- | ## Fields
-- |
-- | - min: Minimum value (aria-valuemin)
-- | - max: Maximum value (aria-valuemax)
-- | - step: Step increment (for discrete stepping)
-- | - defaultValue: Value for reset
-- | - unit: Unit suffix for display
type KnobRange =
  { min :: Number
  , max :: Number
  , step :: Number
  , defaultValue :: Number
  , unit :: String
  }

-- | Default range (0-100, step 1).
defaultRange :: KnobRange
defaultRange =
  { min: 0.0
  , max: 100.0
  , step: 1.0
  , defaultValue: 50.0
  , unit: ""
  }

-- | Volume range (0-100%, default 80%).
volumeRange :: KnobRange
volumeRange =
  { min: 0.0
  , max: 100.0
  , step: 1.0
  , defaultValue: 80.0
  , unit: "%"
  }

-- | Pan range (-100 to +100, center = 0).
panRange :: KnobRange
panRange =
  { min: -100.0
  , max: 100.0
  , step: 1.0
  , defaultValue: 0.0
  , unit: ""
  }

-- | Frequency range (20-20000 Hz, logarithmic).
frequencyRange :: KnobRange
frequencyRange =
  { min: 20.0
  , max: 20000.0
  , step: 1.0
  , defaultValue: 1000.0
  , unit: "Hz"
  }

-- | Attack/Decay/Release range (0-10000 ms).
attackRange :: KnobRange
attackRange =
  { min: 0.0
  , max: 10000.0
  , step: 1.0
  , defaultValue: 10.0
  , unit: "ms"
  }

-- | Playback rate range (0.25-4.0x).
rateRange :: KnobRange
rateRange =
  { min: 0.25
  , max: 4.0
  , step: 0.01
  , defaultValue: 1.0
  , unit: "x"
  }

-- | Rotation range (0-360 degrees).
rotationRange :: KnobRange
rotationRange =
  { min: 0.0
  , max: 360.0
  , step: 1.0
  , defaultValue: 0.0
  , unit: "°"
  }

-- | Medical rate range (0-999 mL/hr).
medicalRateRange :: KnobRange
medicalRateRange =
  { min: 0.0
  , max: 999.0
  , step: 1.0
  , defaultValue: 0.0
  , unit: "mL/hr"
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // value formatter
-- ═════════════════════════════════════════════════════════════════════════════

-- | Value formatter function type.
-- |
-- | Takes a raw numeric value and returns a human-readable string
-- | suitable for display and aria-valuetext.
type ValueFormatter = Number -> String

-- | Format as percentage (e.g., "80%").
formatPercent :: ValueFormatter
formatPercent v = show (Bounded.clampInt 0 100 (roundToInt v)) <> "%"

-- | Format as decibels (e.g., "+3.2 dB", "-inf").
formatDecibels :: ValueFormatter
formatDecibels v
  | v <= 0.0 = "-∞ dB"
  | true = 
      let db = 20.0 * (Number.log v / Number.log 10.0)
          rounded = roundToDecimal 1 db
          sign = if rounded > 0.0 then "+" else ""
      in sign <> show rounded <> " dB"

-- | Format as pan position (e.g., "L 32", "Center", "R 64").
formatPan :: ValueFormatter
formatPan v
  | v < -1.0 = "L " <> show (roundToInt (Number.abs v))
  | v > 1.0 = "R " <> show (roundToInt v)
  | true = "Center"

-- | Format as frequency (e.g., "440 Hz", "1.2 kHz").
formatFrequency :: ValueFormatter
formatFrequency v
  | v >= 1000.0 = show (roundToDecimal 1 (v / 1000.0)) <> " kHz"
  | true = show (roundToInt v) <> " Hz"

-- | Format as rate multiplier (e.g., "2.0x", "0.5x").
formatRate :: ValueFormatter
formatRate v = show (roundToDecimal 2 v) <> "x"

-- | Format as medical rate (e.g., "120 mL/hr").
formatMedicalRate :: ValueFormatter
formatMedicalRate v = show (roundToInt v) <> " mL/hr"

-- | Format as degrees (e.g., "180°").
formatDegrees :: ValueFormatter
formatDegrees v = show (roundToInt v) <> "°"

-- | Custom formatter with unit suffix.
formatCustom :: String -> ValueFormatter
formatCustom unit v = show (roundToDecimal 1 v) <> unit

-- | Round to integer (using standard rounding: 0.5 rounds up).
roundToInt :: Number -> Int
roundToInt n = Int.floor (n + 0.5)

-- | Round to decimal places.
roundToDecimal :: Int -> Number -> Number
roundToDecimal places n = 
  let factor = pow10 places
  in Int.toNumber (roundToInt (n * factor)) / factor
  where
    pow10 :: Int -> Number
    pow10 0 = 1.0
    pow10 1 = 10.0
    pow10 2 = 100.0
    pow10 3 = 1000.0
    pow10 _ = 1000.0  -- Cap at 3 decimal places

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // knob semantics
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete knob semantics — purpose, identity, and accessibility.
-- |
-- | ## ARIA Attributes
-- |
-- | - role="slider" (standard for rotary controls)
-- | - aria-valuenow (current value)
-- | - aria-valuemin (minimum)
-- | - aria-valuemax (maximum)
-- | - aria-valuetext (human-readable, e.g., "Left 32")
-- | - aria-label (or aria-labelledby)
-- | - aria-describedby (optional)
-- |
-- | ## UUID5 Identity
-- |
-- | Knob identity is derived from:
-- | - uniqueKey
-- | - purpose
-- | - label
-- |
-- | Same inputs = same UUID5. Always. Everywhere.
type KnobSemantics =
  { -- Purpose and identity
    purpose :: KnobPurpose          -- ^ What kind of knob
  , uniqueKey :: String             -- ^ Unique identifier for UUID5
    -- Labels
  , label :: String                 -- ^ Visible or ARIA label
  , labelledBy :: Maybe String      -- ^ ID of labelling element
  , description :: Maybe String     -- ^ Extended description
  , describedBy :: Maybe String     -- ^ ID of describing element
    -- Value range and scaling
  , range :: KnobRange              -- ^ Min, max, step, default
  , scaleType :: ScaleType          -- ^ Linear, log, or exponential
    -- Formatting
  , formatter :: ValueFormatter     -- ^ How to format value for display
    -- State
  , disabled :: Boolean             -- ^ Is knob disabled
  }

-- | Default knob semantics.
defaultSemantics :: String -> KnobSemantics
defaultSemantics key =
  { purpose: PurposeCustom "Value"
  , uniqueKey: key
  , label: "Value"
  , labelledBy: Nothing
  , description: Nothing
  , describedBy: Nothing
  , range: defaultRange
  , scaleType: ScaleLinear
  , formatter: formatPercent
  , disabled: false
  }

-- | Volume knob semantics.
volumeSemantics :: String -> KnobSemantics
volumeSemantics key =
  { purpose: PurposeVolume
  , uniqueKey: key
  , label: "Volume"
  , labelledBy: Nothing
  , description: Just "Adjust audio volume"
  , describedBy: Nothing
  , range: volumeRange
  , scaleType: ScaleLinear
  , formatter: formatPercent
  , disabled: false
  }

-- | Pan knob semantics.
panSemantics :: String -> KnobSemantics
panSemantics key =
  { purpose: PurposePan
  , uniqueKey: key
  , label: "Pan"
  , labelledBy: Nothing
  , description: Just "Adjust stereo position"
  , describedBy: Nothing
  , range: panRange
  , scaleType: ScaleLinear
  , formatter: formatPan
  , disabled: false
  }

-- | Frequency knob semantics.
frequencySemantics :: String -> KnobSemantics
frequencySemantics key =
  { purpose: PurposeFrequency
  , uniqueKey: key
  , label: "Frequency"
  , labelledBy: Nothing
  , description: Just "Adjust frequency (20 Hz - 20 kHz)"
  , describedBy: Nothing
  , range: frequencyRange
  , scaleType: ScaleLogarithmic
  , formatter: formatFrequency
  , disabled: false
  }

-- | Playback rate semantics.
rateSemantics :: String -> KnobSemantics
rateSemantics key =
  { purpose: PurposeRate
  , uniqueKey: key
  , label: "Rate"
  , labelledBy: Nothing
  , description: Just "Adjust playback speed"
  , describedBy: Nothing
  , range: rateRange
  , scaleType: ScaleLogarithmic
  , formatter: formatRate
  , disabled: false
  }

-- | Rotation knob semantics.
rotationSemantics :: String -> KnobSemantics
rotationSemantics key =
  { purpose: PurposeRotation
  , uniqueKey: key
  , label: "Rotation"
  , labelledBy: Nothing
  , description: Nothing
  , describedBy: Nothing
  , range: rotationRange
  , scaleType: ScaleLinear
  , formatter: formatDegrees
  , disabled: false
  }

-- | Medical rate semantics.
medicalSemantics :: String -> KnobSemantics
medicalSemantics key =
  { purpose: PurposeMedicalRate
  , uniqueKey: key
  , label: "Flow Rate"
  , labelledBy: Nothing
  , description: Just "IV infusion rate in milliliters per hour"
  , describedBy: Nothing
  , range: medicalRateRange
  , scaleType: ScaleLinear
  , formatter: formatMedicalRate
  , disabled: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get purpose.
getPurpose :: KnobSemantics -> KnobPurpose
getPurpose s = s.purpose

-- | Get label.
getLabel :: KnobSemantics -> String
getLabel s = s.label

-- | Get description.
getDescription :: KnobSemantics -> Maybe String
getDescription s = s.description

-- | Get ARIA role (always "slider" for rotary controls).
getAriaRole :: KnobSemantics -> String
getAriaRole _ = "slider"

-- | Get ARIA valuetext for a given numeric value.
-- |
-- | Uses the formatter to create human-readable text.
getAriaValueText :: Number -> KnobSemantics -> String
getAriaValueText value sem = sem.formatter value

-- | Get value range.
getRange :: KnobSemantics -> KnobRange
getRange s = s.range

-- | Get scale type.
getScaleType :: KnobSemantics -> ScaleType
getScaleType s = s.scaleType

-- | Is knob disabled?
isDisabled :: KnobSemantics -> Boolean
isDisabled s = s.disabled

-- | Is this knob using logarithmic scaling?
isLogarithmic :: KnobSemantics -> Boolean
isLogarithmic s = s.scaleType == ScaleLogarithmic

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set purpose.
setPurpose :: KnobPurpose -> KnobSemantics -> KnobSemantics
setPurpose p s = s { purpose = p }

-- | Set label.
setLabel :: String -> KnobSemantics -> KnobSemantics
setLabel l s = s { label = l }

-- | Set description.
setDescription :: String -> KnobSemantics -> KnobSemantics
setDescription d s = s { description = Just d }

-- | Set disabled state.
setDisabled :: Boolean -> KnobSemantics -> KnobSemantics
setDisabled d s = s { disabled = d }

-- | Set value range.
setRange :: KnobRange -> KnobSemantics -> KnobSemantics
setRange r s = s { range = r }

-- | Set scale type.
setScaleType :: ScaleType -> KnobSemantics -> KnobSemantics
setScaleType t s = s { scaleType = t }

-- | Set value formatter.
setFormatter :: ValueFormatter -> KnobSemantics -> KnobSemantics
setFormatter f s = s { formatter = f }

-- | Set aria-describedby ID.
setAriaDescribedBy :: String -> KnobSemantics -> KnobSemantics
setAriaDescribedBy id s = s { describedBy = Just id }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // uuid5 identity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate deterministic UUID5 for a knob.
-- |
-- | Identity is derived from:
-- | - uniqueKey
-- | - purpose
-- | - label
-- |
-- | Same inputs = same UUID5. Always. Everywhere.
knobId :: KnobSemantics -> UUID5
knobId sem =
  let
    canonical = sem.uniqueKey <> "|" <> show sem.purpose <> "|" <> sem.label
  in
    uuid5 nsKnob canonical

-- | Get knob UUID5 as string (36 chars with dashes).
knobIdString :: KnobSemantics -> String
knobIdString sem = toString (knobId sem)
