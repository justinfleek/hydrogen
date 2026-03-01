-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // brush // pressure // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pressure Types — Transfer curves and simulation for pressure input.
-- |
-- | ## Design Philosophy
-- |
-- | Pressure is a physical phenomenon with unique properties:
-- | - **Haptic feedback** — force feedback to the user
-- | - **Physical simulation** — resistance curves, spring models
-- | - **Hardware integration** — pressure levels, force sensors
-- | - **Robotics** — force-controlled manipulation
-- |
-- | PressureCurve is semantically distinct from ResponseCurve (Dynamics.Types).
-- | While both describe transfer functions [0,1] → [0,1], PressureCurve is
-- | specific to the pressure domain and may be extended with haptic parameters.
-- |
-- | PressureSimulation provides pressure-like input for devices without native
-- | pressure support (mouse, trackpad, touch without force sensing).
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)

module Hydrogen.Schema.Brush.Pressure.Types
  ( -- * Pressure Curve
    PressureCurve
      ( Linear
      , Soft
      , Firm
      , SCurve
      , Logarithmic
      , Exponential
      )
  , allPressureCurves
  , pressureCurveDescription
  , pressureCurveFormula
  , pressureCurveMaxSensitivity
  , pressureCurveDebugInfo
  
  -- * Pressure Simulation
  , PressureSimulation(..)
  , allPressureSimulations
  , pressureSimulationDescription
  , pressureSimulationQuality
  , pressureSimulationDebugInfo
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

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // pressure curve
-- ═════════════════════════════════════════════════════════════════════════════

-- | Transfer function mapping raw pressure to effective pressure.
-- |
-- | Each curve defines how stylus force translates to brush parameter changes.
-- | Input is normalized pressure (0-1), output is effective pressure (0-1).
-- |
-- | ## Physical Context
-- |
-- | Unlike velocity or tilt, pressure involves force — a physical quantity
-- | that can be measured, simulated, and fed back to the user via haptics.
-- | PressureCurve shapes the *feel* of pressure response:
-- |
-- | - **Linear**: Direct force sensing, technical applications
-- | - **Soft**: Light touch sensitive, natural media simulation
-- | - **Firm**: Requires deliberate force, bold/confident strokes
-- | - **SCurve**: Smooth transition, comfortable for long sessions
-- | - **Logarithmic**: Quick response, then plateaus (calligraphy)
-- | - **Exponential**: Builds momentum, requires commitment
-- |
-- | ## Future Extensions
-- |
-- | This type may be extended to include haptic feedback parameters:
-- | - Force feedback resistance curves
-- | - Spring tension simulation
-- | - Click/detent positions
data PressureCurve
  = Linear       -- ^ Direct 1:1 mapping: f(p) = p
  | Soft         -- ^ Light touch sensitive: f(p) = sqrt(p)
  | Firm         -- ^ Requires force: f(p) = p²
  | SCurve       -- ^ Smooth transition: f(p) = 3p² - 2p³
  | Logarithmic  -- ^ Quick ramp, plateau: f(p) = log(1 + 9p) / log(10)
  | Exponential  -- ^ Slow start, fast end: f(p) = (e^p - 1) / (e - 1)

derive instance eqPressureCurve :: Eq PressureCurve
derive instance ordPressureCurve :: Ord PressureCurve

instance showPressureCurve :: Show PressureCurve where
  show Linear = "(PressureCurve Linear)"
  show Soft = "(PressureCurve Soft)"
  show Firm = "(PressureCurve Firm)"
  show SCurve = "(PressureCurve SCurve)"
  show Logarithmic = "(PressureCurve Logarithmic)"
  show Exponential = "(PressureCurve Exponential)"

-- | All available pressure curve types.
allPressureCurves :: Array PressureCurve
allPressureCurves = [ Linear, Soft, Firm, SCurve, Logarithmic, Exponential ]

-- | Human-readable description of each pressure curve.
pressureCurveDescription :: PressureCurve -> String
pressureCurveDescription Linear = "Linear 1:1 response, direct force mapping"
pressureCurveDescription Soft = "Soft response, light touch sensitive (sqrt curve)"
pressureCurveDescription Firm = "Firm response, requires pressure (quadratic curve)"
pressureCurveDescription SCurve = "S-curve response, smooth acceleration/deceleration"
pressureCurveDescription Logarithmic = "Logarithmic response, quick ramp then plateau"
pressureCurveDescription Exponential = "Exponential response, slow start then rapid finish"

-- | Mathematical formula for each pressure curve.
pressureCurveFormula :: PressureCurve -> String
pressureCurveFormula Linear = "f(p) = p"
pressureCurveFormula Soft = "f(p) = sqrt(p)"
pressureCurveFormula Firm = "f(p) = p^2"
pressureCurveFormula SCurve = "f(p) = 3p^2 - 2p^3"
pressureCurveFormula Logarithmic = "f(p) = log(1+9p)/log(10)"
pressureCurveFormula Exponential = "f(p) = (e^p - 1)/(e - 1)"

-- | Maximum sensitivity (derivative bound) for each pressure curve.
-- |
-- | This bounds error amplification through the curve. Critical for:
-- | - Haptic feedback stability (prevents oscillation)
-- | - Consistent feel across pressure levels
-- | - Predictable behavior at edges
-- |
-- | | Curve       | Derivative           | Max on [0,1] or [ε,1] |
-- | |-------------|----------------------|------------------------|
-- | | Linear      | 1                    | 1.0                    |
-- | | Soft        | 1/(2√p)             | 8.0 (at p = 1/256)     |
-- | | Firm        | 2p                   | 2.0                    |
-- | | SCurve      | 6p - 6p²            | 1.5 (at p = 0.5)       |
-- | | Logarithmic | 9/((1+9p)·ln(10))   | 3.91 (at p = 0)        |
-- | | Exponential | e^p/(e-1)           | 1.58 (at p = 1)        |
pressureCurveMaxSensitivity :: PressureCurve -> Number
pressureCurveMaxSensitivity Linear = 1.0
pressureCurveMaxSensitivity Soft = 8.0
pressureCurveMaxSensitivity Firm = 2.0
pressureCurveMaxSensitivity SCurve = 1.5
pressureCurveMaxSensitivity Logarithmic = 3.91
pressureCurveMaxSensitivity Exponential = 1.58

-- | Debug info string for pressure curve.
pressureCurveDebugInfo :: PressureCurve -> String
pressureCurveDebugInfo curve =
  show curve <> " formula:" <> pressureCurveFormula curve
    <> " maxSensitivity:" <> show (pressureCurveMaxSensitivity curve)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // pressure simulation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Method for simulating pressure on non-pressure devices.
-- | Used when native pressure is unavailable.
data PressureSimulation
  = SimulateVelocity   -- ^ Faster = more pressure
  | SimulateDistance   -- ^ Longer stroke = building pressure
  | SimulateTime       -- ^ Longer hold = more pressure
  | SimulateForceTouch -- ^ Use Force Touch / 3D Touch (macOS/iOS)
  | SimulateFixed      -- ^ Constant pressure value (fallback)

derive instance eqPressureSimulation :: Eq PressureSimulation
derive instance ordPressureSimulation :: Ord PressureSimulation

instance showPressureSimulation :: Show PressureSimulation where
  show SimulateVelocity = "(PressureSimulation Velocity)"
  show SimulateDistance = "(PressureSimulation Distance)"
  show SimulateTime = "(PressureSimulation Time)"
  show SimulateForceTouch = "(PressureSimulation ForceTouch)"
  show SimulateFixed = "(PressureSimulation Fixed)"

-- | All available pressure simulation methods.
allPressureSimulations :: Array PressureSimulation
allPressureSimulations =
  [ SimulateVelocity
  , SimulateDistance
  , SimulateTime
  , SimulateForceTouch
  , SimulateFixed
  ]

-- | Human-readable description of each simulation method.
pressureSimulationDescription :: PressureSimulation -> String
pressureSimulationDescription SimulateVelocity = "Movement speed maps to pressure"
pressureSimulationDescription SimulateDistance = "Stroke length builds pressure"
pressureSimulationDescription SimulateTime = "Hold duration increases pressure"
pressureSimulationDescription SimulateForceTouch = "Use trackpad/screen force sensing"
pressureSimulationDescription SimulateFixed = "Constant pressure value, no variation"

-- | Quality rating for each simulation method (1-5).
pressureSimulationQuality :: PressureSimulation -> Int
pressureSimulationQuality SimulateVelocity = 3
pressureSimulationQuality SimulateDistance = 2
pressureSimulationQuality SimulateTime = 3
pressureSimulationQuality SimulateForceTouch = 4
pressureSimulationQuality SimulateFixed = 1

-- | Debug info string for pressure simulation.
pressureSimulationDebugInfo :: PressureSimulation -> String
pressureSimulationDebugInfo sim =
  show sim <> " quality:" <> show (pressureSimulationQuality sim)
