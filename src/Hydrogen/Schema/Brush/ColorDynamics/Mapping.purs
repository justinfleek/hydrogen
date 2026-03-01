-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                  // hydrogen // schema // brush // colordynamics // mapping
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | FG/BG Position Mapping — Configuration for input-to-position modulation.
-- |
-- | ## Design Philosophy
-- |
-- | FGBGMapping defines how input signals (pressure, tilt, velocity) control
-- | the interpolation position between foreground and background colors.
-- | This enables expressive color behavior where light pressure produces
-- | one color and heavy pressure produces another, with smooth transitions.
-- |
-- | ## The Mapping Pattern
-- |
-- | Following the established pattern from Pressure, Tilt, Velocity, and
-- | Texture mappings, FGBGMapping provides:
-- |
-- | - `control`: What input type controls position (or Off)
-- | - `positionAtMinInput`: FG/BG position when input is at minimum
-- | - `positionAtMaxInput`: FG/BG position when input is at maximum
-- | - `curve`: Transfer function for non-linear mapping
-- |
-- | ## The Gap This Fills
-- |
-- | Previously, ColorDynamicsConfig had `fgbgControl :: ColorControl` which
-- | specified WHAT controls the FG/BG position, but assumed a fixed 0→1 range.
-- | This made it impossible to express:
-- |
-- | - "Light pressure = 20% toward BG, heavy pressure = 80% toward BG"
-- | - "Inverted control: light = BG, heavy = FG"
-- | - "Narrow range: pressure only varies between 30% and 70%"
-- |
-- | With FGBGMapping, these behaviors are explicit and composable.
-- |
-- | ## Input Sources
-- |
-- | - **Pressure**: Light touch = min position, heavy press = max position
-- | - **Tilt**: Perpendicular pen = min, tilted = max
-- | - **Velocity**: Slow strokes = min, fast strokes = max
-- | - **StrokeDistance**: Start of stroke = min, end = max
-- | - **StrokeTime**: Fresh stroke = min, duration = max
-- | - **Random**: Per-dab random position within range
-- | - **Off**: Constant position (uses static value)
-- |
-- | ## Dependencies
-- |
-- | - Prelude
-- | - ColorDynamics.Types (ColorControl)

module Hydrogen.Schema.Brush.ColorDynamics.Mapping
  ( -- * FGBGCurve ADT
    FGBGCurve
      ( FGBGLinear
      , FGBGSoft
      , FGBGFirm
      , FGBGSCurve
      , FGBGLogarithmic
      , FGBGExponential
      )
  , allFGBGCurves
  , fgbgCurveDescription
  , fgbgCurveFormula
  , fgbgCurveMaxSensitivity
  , fgbgCurveToId
  , fgbgCurveDebugInfo
  
  -- * FGBGMapping Record
  , FGBGMapping
  , defaultFGBGMapping
  , fgbgMappingDebugInfo
  
  -- * Presets
  , noFGBGMapping
  , pressureFGBGMapping
  , tiltFGBGMapping
  , velocityFGBGMapping
  , distanceFGBGMapping
  , randomFGBGMapping
  , invertedPressureMapping
  , subtlePressureMapping
  , dramaticPressureMapping
  
  -- * Queries
  , isFGBGMappingEnabled
  , getPositionRange
  , isInvertedMapping
  , fgbgMappingComplexity
  
  -- * Debug Utilities
  , showWithFGBGMapping
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
  , (+)
  , (-)
  , (*)
  , (<)
  , (==)
  , not
  , negate
  )

import Hydrogen.Schema.Brush.ColorDynamics.Types
  ( ColorControl
      ( ControlOff
      , ControlPressure
      , ControlTilt
      , ControlVelocity
      , ControlStrokeDistance
      , ControlStrokeTime
      , ControlRandom
      )
  , colorControlToId
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // fgbg curve
-- ═════════════════════════════════════════════════════════════════════════════

-- | Transfer function for FG/BG position mapping.
-- |
-- | Controls how input values (0-1) map to position values (0-1).
-- | Same curve vocabulary as PressureCurve, VelocityCurve, TextureDepthCurve.
-- |
-- | - **Linear**: Direct 1:1 mapping, f(t) = t
-- | - **Soft**: Sensitive to light input, f(t) = sqrt(t)
-- | - **Firm**: Requires more input, f(t) = t²
-- | - **SCurve**: Smooth middle region, f(t) = 3t² - 2t³
-- | - **Logarithmic**: Quick ramp then plateau, f(t) = log(1+9t)/log(10)
-- | - **Exponential**: Slow start rapid finish, f(t) = (e^t-1)/(e-1)
data FGBGCurve
  = FGBGLinear       -- ^ Direct 1:1 mapping: f(t) = t
  | FGBGSoft         -- ^ Light input sensitive: f(t) = sqrt(t)
  | FGBGFirm         -- ^ Requires input: f(t) = t²
  | FGBGSCurve       -- ^ Smooth S-curve: f(t) = 3t² - 2t³
  | FGBGLogarithmic  -- ^ Quick ramp, plateau: f(t) = log(1+9t)/log(10)
  | FGBGExponential  -- ^ Slow start, fast end: f(t) = (e^t-1)/(e-1)

derive instance eqFGBGCurve :: Eq FGBGCurve
derive instance ordFGBGCurve :: Ord FGBGCurve

instance showFGBGCurve :: Show FGBGCurve where
  show FGBGLinear = "(FGBGCurve Linear)"
  show FGBGSoft = "(FGBGCurve Soft)"
  show FGBGFirm = "(FGBGCurve Firm)"
  show FGBGSCurve = "(FGBGCurve SCurve)"
  show FGBGLogarithmic = "(FGBGCurve Logarithmic)"
  show FGBGExponential = "(FGBGCurve Exponential)"

-- | All available FG/BG curve types.
allFGBGCurves :: Array FGBGCurve
allFGBGCurves =
  [ FGBGLinear
  , FGBGSoft
  , FGBGFirm
  , FGBGSCurve
  , FGBGLogarithmic
  , FGBGExponential
  ]

-- | Human-readable description of each FG/BG curve.
fgbgCurveDescription :: FGBGCurve -> String
fgbgCurveDescription FGBGLinear = "Linear 1:1 response, direct input mapping"
fgbgCurveDescription FGBGSoft = "Soft response, sensitive to light input"
fgbgCurveDescription FGBGFirm = "Firm response, requires stronger input"
fgbgCurveDescription FGBGSCurve = "S-curve response, smooth middle region"
fgbgCurveDescription FGBGLogarithmic = "Logarithmic response, quick ramp then plateau"
fgbgCurveDescription FGBGExponential = "Exponential response, slow start then rapid finish"

-- | Mathematical formula for each FG/BG curve.
fgbgCurveFormula :: FGBGCurve -> String
fgbgCurveFormula FGBGLinear = "f(t) = t"
fgbgCurveFormula FGBGSoft = "f(t) = sqrt(t)"
fgbgCurveFormula FGBGFirm = "f(t) = t^2"
fgbgCurveFormula FGBGSCurve = "f(t) = 3t^2 - 2t^3"
fgbgCurveFormula FGBGLogarithmic = "f(t) = log(1+9t)/log(10)"
fgbgCurveFormula FGBGExponential = "f(t) = (e^t - 1)/(e - 1)"

-- | Maximum sensitivity (derivative bound) for each FG/BG curve.
-- |
-- | Bounds how rapidly the output changes with input.
-- | Important for smooth color transitions.
-- |
-- | | Curve       | Derivative           | Max on [0,1] or [ε,1] |
-- | |-------------|----------------------|------------------------|
-- | | Linear      | 1                    | 1.0                    |
-- | | Soft        | 1/(2√t)             | 8.0 (at t = 1/256)     |
-- | | Firm        | 2t                   | 2.0                    |
-- | | SCurve      | 6t - 6t²            | 1.5 (at t = 0.5)       |
-- | | Logarithmic | 9/((1+9t)·ln(10))   | 3.91 (at t = 0)        |
-- | | Exponential | e^t/(e-1)           | 1.58 (at t = 1)        |
fgbgCurveMaxSensitivity :: FGBGCurve -> Number
fgbgCurveMaxSensitivity FGBGLinear = 1.0
fgbgCurveMaxSensitivity FGBGSoft = 8.0
fgbgCurveMaxSensitivity FGBGFirm = 2.0
fgbgCurveMaxSensitivity FGBGSCurve = 1.5
fgbgCurveMaxSensitivity FGBGLogarithmic = 3.91
fgbgCurveMaxSensitivity FGBGExponential = 1.58

-- | Convert curve to string ID for serialization.
fgbgCurveToId :: FGBGCurve -> String
fgbgCurveToId FGBGLinear = "linear"
fgbgCurveToId FGBGSoft = "soft"
fgbgCurveToId FGBGFirm = "firm"
fgbgCurveToId FGBGSCurve = "s-curve"
fgbgCurveToId FGBGLogarithmic = "logarithmic"
fgbgCurveToId FGBGExponential = "exponential"

-- | Debug info string for FG/BG curve.
fgbgCurveDebugInfo :: FGBGCurve -> String
fgbgCurveDebugInfo curve =
  show curve <> " formula:" <> fgbgCurveFormula curve
    <> " maxSensitivity:" <> show (fgbgCurveMaxSensitivity curve)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // fgbg mapping
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for how input signals modulate FG/BG position.
-- |
-- | ## Field Descriptions
-- |
-- | - `control`: What input type controls position (Pressure, Tilt, etc.)
-- | - `positionAtMinInput`: FG/BG position when input is at minimum (0.0-1.0)
-- | - `positionAtMaxInput`: FG/BG position when input is at maximum (0.0-1.0)
-- | - `curve`: Transfer function for non-linear response
-- |
-- | ## Position Semantics
-- |
-- | - 0.0 = pure foreground color
-- | - 1.0 = pure background color
-- | - 0.5 = equal mix of foreground and background
-- |
-- | ## Mapping Semantics
-- |
-- | When `control = ControlPressure`:
-- | - Input pressure 0.0 → position = positionAtMinInput
-- | - Input pressure 1.0 → position = positionAtMaxInput
-- | - Values between interpolated through curve
-- |
-- | When `control = ControlOff`:
-- | - The mapping is ignored
-- | - Position uses static fgbgControl behavior from ColorDynamicsConfig
type FGBGMapping =
  { control :: ColorControl              -- What controls position
  , positionAtMinInput :: Number         -- Position at minimum input (0.0-1.0)
  , positionAtMaxInput :: Number         -- Position at maximum input (0.0-1.0)
  , curve :: FGBGCurve                   -- Transfer function
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // default
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default FG/BG mapping: no dynamic control.
-- |
-- | Position is constant, determined by static configuration.
-- | Min/max values are sensible defaults for when mapping is enabled.
defaultFGBGMapping :: FGBGMapping
defaultFGBGMapping =
  { control: ControlOff                  -- No dynamic control
  , positionAtMinInput: 0.0              -- Foreground at min input
  , positionAtMaxInput: 1.0              -- Background at max input
  , curve: FGBGLinear                    -- Direct mapping
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | No FG/BG mapping (static position).
-- |
-- | Position is constant throughout the stroke.
-- | Used for: solid color brushes, no variation needed.
noFGBGMapping :: FGBGMapping
noFGBGMapping = defaultFGBGMapping

-- | Pressure-controlled position with full range.
-- |
-- | Light pressure = foreground, heavy pressure = background.
-- | Most common configuration for two-tone brushes.
-- | Used for: calligraphy, expressive brushwork, shading.
pressureFGBGMapping :: FGBGMapping
pressureFGBGMapping =
  { control: ControlPressure
  , positionAtMinInput: 0.0              -- Foreground at light touch
  , positionAtMaxInput: 1.0              -- Background at heavy press
  , curve: FGBGSoft                      -- Sensitive to light pressure
  }

-- | Tilt-controlled position for angle-based color.
-- |
-- | Perpendicular pen = foreground, tilted = background.
-- | Useful for creating shading effects where angle affects color.
-- | Used for: pencil shading with color, angle-based variation.
tiltFGBGMapping :: FGBGMapping
tiltFGBGMapping =
  { control: ControlTilt
  , positionAtMinInput: 0.0              -- Foreground when perpendicular
  , positionAtMaxInput: 1.0              -- Background when tilted
  , curve: FGBGLinear                    -- Direct altitude mapping
  }

-- | Velocity-controlled position for speed-based color.
-- |
-- | Slow strokes = foreground, fast strokes = background.
-- | Creates dynamic variation based on drawing speed.
-- | Used for: expressive speed-based coloring, action painting.
velocityFGBGMapping :: FGBGMapping
velocityFGBGMapping =
  { control: ControlVelocity
  , positionAtMinInput: 0.0              -- Foreground when slow
  , positionAtMaxInput: 1.0              -- Background when fast
  , curve: FGBGSCurve                    -- Smooth transition
  }

-- | Distance-controlled position for gradient strokes.
-- |
-- | Start of stroke = foreground, end of stroke = background.
-- | Creates linear color gradients along the stroke path.
-- | Used for: gradient strokes, fade effects, rainbow lines.
distanceFGBGMapping :: FGBGMapping
distanceFGBGMapping =
  { control: ControlStrokeDistance
  , positionAtMinInput: 0.0              -- Foreground at start
  , positionAtMaxInput: 1.0              -- Background at end
  , curve: FGBGLinear                    -- Linear gradient
  }

-- | Random position for chaotic color variation.
-- |
-- | Each dab gets random position within full range.
-- | Creates unpredictable, varied color throughout stroke.
-- | Used for: impressionist effects, chaotic coloring, texture.
randomFGBGMapping :: FGBGMapping
randomFGBGMapping =
  { control: ControlRandom
  , positionAtMinInput: 0.0              -- Minimum random position
  , positionAtMaxInput: 1.0              -- Maximum random position
  , curve: FGBGLinear                    -- Direct (random already varied)
  }

-- | Inverted pressure mapping.
-- |
-- | Light pressure = background, heavy pressure = foreground.
-- | Opposite of standard pressure mapping for special effects.
-- | Used for: inverted two-tone, special calligraphy effects.
invertedPressureMapping :: FGBGMapping
invertedPressureMapping =
  { control: ControlPressure
  , positionAtMinInput: 1.0              -- Background at light touch
  , positionAtMaxInput: 0.0              -- Foreground at heavy press
  , curve: FGBGSoft                      -- Sensitive to light pressure
  }

-- | Subtle pressure mapping with narrow range.
-- |
-- | Pressure varies position only between 20% and 80%.
-- | Creates subtle color variation, never pure FG or BG.
-- | Used for: subtle two-tone, controlled variation.
subtlePressureMapping :: FGBGMapping
subtlePressureMapping =
  { control: ControlPressure
  , positionAtMinInput: 0.2              -- 20% toward BG at light touch
  , positionAtMaxInput: 0.8              -- 80% toward BG at heavy press
  , curve: FGBGSCurve                    -- Smooth middle range
  }

-- | Dramatic pressure mapping with firm curve.
-- |
-- | Full range but requires firm pressure to reach background.
-- | Creates dramatic contrast between light and heavy strokes.
-- | Used for: dramatic two-tone, expressive contrast.
dramaticPressureMapping :: FGBGMapping
dramaticPressureMapping =
  { control: ControlPressure
  , positionAtMinInput: 0.0              -- Pure FG at light touch
  , positionAtMaxInput: 1.0              -- Pure BG at heavy press
  , curve: FGBGFirm                      -- Requires firm pressure
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if FG/BG mapping is enabled (not Off).
isFGBGMappingEnabled :: FGBGMapping -> Boolean
isFGBGMappingEnabled m = not (m.control == ControlOff)

-- | Get the position range (max - min).
-- | Useful for understanding the dynamic range of the mapping.
-- | Returns absolute value of difference.
getPositionRange :: FGBGMapping -> Number
getPositionRange m =
  let diff = m.positionAtMaxInput - m.positionAtMinInput
  in if diff < 0.0 then diff * (-1.0) else diff

-- | Check if mapping is inverted (max < min).
-- | Inverted mappings reverse the natural direction of the control.
isInvertedMapping :: FGBGMapping -> Boolean
isInvertedMapping m = m.positionAtMaxInput < m.positionAtMinInput

-- | Calculate mapping complexity score (0-100).
-- | Higher values indicate more complex/expensive computation.
fgbgMappingComplexity :: FGBGMapping -> Number
fgbgMappingComplexity m =
  controlScore + rangeScore + curveScore
  where
    -- Base score for control type
    controlScore :: Number
    controlScore = case m.control of
      ControlOff -> 0.0
      ControlPressure -> 10.0
      ControlTilt -> 15.0              -- Tilt requires more processing
      ControlVelocity -> 20.0          -- Velocity requires smoothing
      ControlStrokeDistance -> 15.0    -- Distance requires accumulation
      ControlStrokeTime -> 10.0        -- Time is straightforward
      ControlRandom -> 5.0             -- Random is cheap
      _ -> 10.0                        -- Default for other controls
    
    -- Score for dynamic range
    rangeScore :: Number
    rangeScore = getPositionRange m * 20.0
    
    -- Score for curve complexity
    curveScore :: Number
    curveScore = case m.curve of
      FGBGLinear -> 0.0
      FGBGSoft -> 5.0
      FGBGFirm -> 5.0
      FGBGSCurve -> 10.0
      FGBGLogarithmic -> 8.0
      FGBGExponential -> 8.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // debug utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate debug info string for FGBGMapping.
-- |
-- | Produces a parseable, unambiguous representation.
-- | Format: "(FGBGMapping { control: pressure, range: 0.0→1.0, curve: soft })"
fgbgMappingDebugInfo :: FGBGMapping -> String
fgbgMappingDebugInfo m =
  "(FGBGMapping { " <>
  "control: " <> colorControlToId m.control <> ", " <>
  "range: " <> show m.positionAtMinInput <> "→" <> show m.positionAtMaxInput <> ", " <>
  "curve: " <> fgbgCurveToId m.curve <>
  showInverted m <>
  " })"
  where
    showInverted :: FGBGMapping -> String
    showInverted mapping =
      if isInvertedMapping mapping
        then " (inverted)"
        else ""

-- | Combine a label with its FG/BG mapping debug info.
-- |
-- | Useful for logging preset configurations with identifying names.
showWithFGBGMapping :: String -> FGBGMapping -> String
showWithFGBGMapping label mapping =
  label <> ": " <> fgbgMappingDebugInfo mapping
