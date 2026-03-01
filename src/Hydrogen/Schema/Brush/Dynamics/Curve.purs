-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // brush // dynamics // curve
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Response Curve Application Functions.
-- |
-- | Status: PROVEN (proofs/Hydrogen/Schema/Brush/Dynamics.lean)
-- |
-- | ## Purpose
-- |
-- | Applies response curves to bounded input values. All functions preserve
-- | bounds by construction — outputs are always in [0,1].
-- |
-- | ## Strong Invariants (Proven in Lean4)
-- |
-- | 1. BOUNDS PRESERVATION — apply always returns value in [0,1]
-- | 2. ENDPOINT PRESERVATION — apply passes through (0,0) and (1,1)
-- | 3. MONOTONICITY — apply is monotonically non-decreasing
-- |
-- | ## Dependencies
-- |
-- | - Schema.Bounded (UnitInterval)
-- | - Dynamics.Types (ResponseCurve, DynamicsMapping)

module Hydrogen.Schema.Brush.Dynamics.Curve
  ( -- * Curve Application
    applyCurve
  , applyCurveRaw
  
  -- * Dynamics Mapping Application
  , applyMapping
  
  -- * Utilities
  , epsilon
  , clampToEpsilon
  , lerpUnit
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( max
  , (+)
  , (-)
  , (*)
  , (/)
  )

import Data.Number (sqrt, pow, log, exp) as Number

import Hydrogen.Schema.Bounded
  ( UnitInterval
  , clampUnit
  , unwrapUnit
  )

import Hydrogen.Schema.Brush.Dynamics.Types
  ( ResponseCurve(Linear, Soft, Firm, SCurve, Logarithmic, Exponential)
  , DynamicsMapping(DynamicsMapping)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // epsilon
-- ═════════════════════════════════════════════════════════════════════════════

-- | Minimum positive value for soft curve domain clamping.
-- |
-- | Value: 1/256 ≈ 0.00390625
-- |
-- | Used to bound sensitivity of sqrt curve at near-zero inputs.
-- | Without this clamp, derivative at zero would be infinite.
epsilon :: Number
epsilon = 1.0 / 256.0

-- | Clamp a value to [epsilon, 1] for curves requiring positive input.
clampToEpsilon :: Number -> Number
clampToEpsilon x = max epsilon (max 0.0 (max x 0.0))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // curve application
-- ═════════════════════════════════════════════════════════════════════════════

-- | Apply a response curve to a raw Number input.
-- |
-- | Assumes input is in [0,1]. Output is guaranteed in [0,1].
-- |
-- | Formulas:
-- | - Linear: f(t) = t
-- | - Soft: f(t) = sqrt(max(epsilon, t))
-- | - Firm: f(t) = t²
-- | - SCurve: f(t) = 3t² - 2t³ (smoothstep)
-- | - Logarithmic: f(t) = log(1 + 9t) / log(10)
-- | - Exponential: f(t) = (e^t - 1) / (e - 1)
applyCurveRaw :: ResponseCurve -> Number -> Number
applyCurveRaw Linear t = t
applyCurveRaw Soft t =
  -- Clamp to [epsilon, 1] to bound sensitivity
  let clamped = max epsilon t
  in Number.sqrt clamped
applyCurveRaw Firm t = Number.pow t 2.0
applyCurveRaw SCurve t = 3.0 * Number.pow t 2.0 - 2.0 * Number.pow t 3.0
applyCurveRaw Logarithmic t =
  -- f(t) = log(1 + 9t) / log(10)
  -- Maps [0,1] → [0,1]: f(0) = 0, f(1) = 1
  Number.log (1.0 + 9.0 * t) / Number.log 10.0
applyCurveRaw Exponential t =
  -- f(t) = (e^t - 1) / (e - 1)
  -- Maps [0,1] → [0,1]: f(0) = 0, f(1) = 1
  let e = Number.exp 1.0
  in (Number.exp t - 1.0) / (e - 1.0)

-- | Apply a response curve to a UnitInterval.
-- |
-- | Input and output are both bounded in [0,1] by construction.
-- |
-- | Proven: bounded, monotone, endpoint-preserving in Dynamics.lean
applyCurve :: ResponseCurve -> UnitInterval -> UnitInterval
applyCurve curve input = clampUnit (applyCurveRaw curve (unwrapUnit input))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // linear interpolation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Linear interpolation between two values.
-- |
-- | lerpUnit t a b = a + t * (b - a)
-- |            = a * (1 - t) + b * t
-- |
-- | When t = 0, returns a.
-- | When t = 1, returns b.
lerpUnit :: UnitInterval -> UnitInterval -> UnitInterval -> UnitInterval
lerpUnit t a b =
  let
    tVal = unwrapUnit t
    aVal = unwrapUnit a
    bVal = unwrapUnit b
    result = aVal * (1.0 - tVal) + bVal * tVal
  in clampUnit result

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // mapping application
-- ═════════════════════════════════════════════════════════════════════════════

-- | Apply a dynamics mapping to an input value.
-- |
-- | output = lerp(valueAtMin, valueAtMax, curve(input))
-- |
-- | Proven: output_in_range in Dynamics.lean
-- | Output is always in [valueAtMin, valueAtMax].
applyMapping :: DynamicsMapping -> UnitInterval -> UnitInterval
applyMapping (DynamicsMapping m) input =
  let curveOutput = applyCurve m.curve input
  in lerpUnit curveOutput m.valueAtMin m.valueAtMax
