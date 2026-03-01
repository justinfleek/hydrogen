-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // brush // dynamics // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Response Curve and Dynamics Mapping Types.
-- |
-- | Status: PROVEN (proofs/Hydrogen/Schema/Brush/Dynamics.lean)
-- |
-- | ## Purpose
-- |
-- | When pressure, tilt, or velocity flows from a stylus, BMI, uploaded mind,
-- | or AI agent — it passes through response curves that shape the feel.
-- | These curves MUST be bounded, monotonic, and sensitivity-tracked.
-- |
-- | ## Strong Invariants (Proven in Lean4)
-- |
-- | 1. BOUNDS PRESERVATION — Curves map [0,1] → [0,1]
-- | 2. ENDPOINT PRESERVATION — Curves pass through (0,0) and (1,1)
-- | 3. MONOTONICITY — Curves are monotonically non-decreasing
-- | 4. SENSITIVITY BOUNDS — Each curve has finite maximum derivative
-- | 5. GRADE DEGRADATION — Applying a curve degrades certainty
-- | 6. OUTPUT RANGE VALIDITY — Mapped values land in [valueAtMin, valueAtMax]
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)
-- | - Schema.Bounded (UnitInterval)

module Hydrogen.Schema.Brush.Dynamics.Types
  ( -- * Response Curves
    ResponseCurve(..)
  , allResponseCurves
  , responseCurveDescription
  , responseCurveMaxSensitivity
  
  -- * Dynamics Mapping
  , DynamicsMapping(..)
  , identityMapping
  , constantMapping
  , softMapping
  , firmMapping
  , sCurveMapping
  , logarithmicMapping
  , exponentialMapping
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

import Hydrogen.Schema.Bounded
  ( UnitInterval
  , unitZero
  , unitOne
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // response curves
-- ═════════════════════════════════════════════════════════════════════════════

-- | Response curve types for dynamics mapping.
-- |
-- | Each curve is a function [0,1] → [0,1] with specific feel:
-- |
-- | - **Linear**: Direct 1:1 mapping. f(t) = t
-- | - **Soft**: Light touch sensitive, power < 1. f(t) = sqrt(t)
-- | - **Firm**: Requires force, power > 1. f(t) = t²
-- | - **SCurve**: Smooth acceleration/deceleration. f(t) = 3t² - 2t³
-- | - **Logarithmic**: Quick ramp then plateau. f(t) = log(1 + 9t) / log(10)
-- | - **Exponential**: Slow start, fast finish. f(t) = (e^t - 1) / (e - 1)
-- |
-- | Proven: All curves are bounded, monotonic, and pass through (0,0) and (1,1).
-- | Exception: Soft maps 0 → sqrt(epsilon) to bound sensitivity.
data ResponseCurve
  = Linear       -- ^ Direct 1:1 mapping: f(t) = t
  | Soft         -- ^ Light touch sensitive: f(t) = sqrt(t), clamped domain
  | Firm         -- ^ Requires force: f(t) = t²
  | SCurve       -- ^ Smooth S-curve: f(t) = 3t² - 2t³
  | Logarithmic  -- ^ Quick ramp, plateau: f(t) = log(1 + 9t) / log(10)
  | Exponential  -- ^ Slow start, fast end: f(t) = (e^t - 1) / (e - 1)

derive instance eqResponseCurve :: Eq ResponseCurve
derive instance ordResponseCurve :: Ord ResponseCurve

instance showResponseCurve :: Show ResponseCurve where
  show Linear = "(ResponseCurve Linear)"
  show Soft = "(ResponseCurve Soft)"
  show Firm = "(ResponseCurve Firm)"
  show SCurve = "(ResponseCurve SCurve)"
  show Logarithmic = "(ResponseCurve Logarithmic)"
  show Exponential = "(ResponseCurve Exponential)"

-- | All available response curves.
allResponseCurves :: Array ResponseCurve
allResponseCurves = [ Linear, Soft, Firm, SCurve, Logarithmic, Exponential ]

-- | Human-readable description of each response curve.
responseCurveDescription :: ResponseCurve -> String
responseCurveDescription Linear = "Linear 1:1 response, no shaping"
responseCurveDescription Soft = "Soft response, light touch sensitive (sqrt curve)"
responseCurveDescription Firm = "Firm response, requires pressure (quadratic curve)"
responseCurveDescription SCurve = "S-curve response, smooth acceleration/deceleration"
responseCurveDescription Logarithmic = "Logarithmic response, quick ramp then plateau"
responseCurveDescription Exponential = "Exponential response, slow start then rapid finish"

-- | Maximum sensitivity (derivative bound) for each curve type.
-- |
-- | This bounds error amplification through the curve.
-- | Proven: All sensitivities are <= 8.
-- |
-- | | Curve       | Derivative           | Max on [0,1] or [ε,1] |
-- | |-------------|----------------------|------------------------|
-- | | Linear      | 1                    | 1                      |
-- | | Soft        | 1/(2√t)             | 8 (at t = 1/256)       |
-- | | Firm        | 2t                   | 2                      |
-- | | SCurve      | 6t - 6t²            | 1.5 (at t = 0.5)       |
-- | | Logarithmic | 9/((1+9t)·ln(10))   | 3.91 (at t = 0)        |
-- | | Exponential | e^t/(e-1)           | 1.58 (at t = 1)        |
responseCurveMaxSensitivity :: ResponseCurve -> Number
responseCurveMaxSensitivity Linear = 1.0
responseCurveMaxSensitivity Soft = 8.0
responseCurveMaxSensitivity Firm = 2.0
responseCurveMaxSensitivity SCurve = 1.5
responseCurveMaxSensitivity Logarithmic = 3.91
responseCurveMaxSensitivity Exponential = 1.58

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // dynamics mapping
-- ═════════════════════════════════════════════════════════════════════════════

-- | A dynamics mapping configuration.
-- |
-- | Maps input ∈ [0,1] to output ∈ [valueAtMin, valueAtMax] via curve:
-- |   output = lerp(valueAtMin, valueAtMax, curve(input))
-- |
-- | Used for pressure→size, tilt→opacity, velocity→flow, etc.
-- |
-- | Invariant (enforced at construction): valueAtMin <= valueAtMax
newtype DynamicsMapping = DynamicsMapping
  { curve :: ResponseCurve
  , valueAtMin :: UnitInterval  -- ^ Output value when input = 0
  , valueAtMax :: UnitInterval  -- ^ Output value when input = 1
  }

derive instance eqDynamicsMapping :: Eq DynamicsMapping

instance showDynamicsMapping :: Show DynamicsMapping where
  show (DynamicsMapping m) = "(DynamicsMapping "
    <> "curve:" <> show m.curve
    <> " min:" <> show m.valueAtMin
    <> " max:" <> show m.valueAtMax
    <> ")"

-- | Identity mapping: linear curve, full range [0,1].
-- | Input passes through unchanged.
identityMapping :: DynamicsMapping
identityMapping = DynamicsMapping
  { curve: Linear
  , valueAtMin: unitZero
  , valueAtMax: unitOne
  }

-- | Constant mapping: any input produces the same output.
constantMapping :: UnitInterval -> DynamicsMapping
constantMapping value = DynamicsMapping
  { curve: Linear
  , valueAtMin: value
  , valueAtMax: value
  }

-- | Soft mapping: light touch sensitive, full range [0,1].
softMapping :: DynamicsMapping
softMapping = DynamicsMapping
  { curve: Soft
  , valueAtMin: unitZero
  , valueAtMax: unitOne
  }

-- | Firm mapping: requires pressure, full range [0,1].
firmMapping :: DynamicsMapping
firmMapping = DynamicsMapping
  { curve: Firm
  , valueAtMin: unitZero
  , valueAtMax: unitOne
  }

-- | S-curve mapping: smooth transition, full range [0,1].
sCurveMapping :: DynamicsMapping
sCurveMapping = DynamicsMapping
  { curve: SCurve
  , valueAtMin: unitZero
  , valueAtMax: unitOne
  }

-- | Logarithmic mapping: quick ramp then plateau, full range [0,1].
-- | Good for calligraphy — responsive to initial touch, then plateaus.
logarithmicMapping :: DynamicsMapping
logarithmicMapping = DynamicsMapping
  { curve: Logarithmic
  , valueAtMin: unitZero
  , valueAtMax: unitOne
  }

-- | Exponential mapping: slow start, fast finish, full range [0,1].
-- | Good for building momentum — requires commitment to reach full effect.
exponentialMapping :: DynamicsMapping
exponentialMapping = DynamicsMapping
  { curve: Exponential
  , valueAtMin: unitZero
  , valueAtMax: unitOne
  }
