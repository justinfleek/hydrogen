-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // brush // dynamics
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Brush Dynamics — Response curves and dynamics mappings.
-- |
-- | Status: PROVEN (proofs/Hydrogen/Schema/Brush/Dynamics.lean)
-- |
-- | ## Design Philosophy
-- |
-- | Dynamics control how input values (pressure, tilt, velocity) map to
-- | output parameters (size, opacity, flow). Response curves shape the
-- | feel — soft curves make light touches sensitive, firm curves require
-- | pressure.
-- |
-- | All curves are BOUNDED by construction: inputs in [0,1] produce
-- | outputs in [0,1]. This is proven in Lean4 and critical for safety
-- | when the input might come from a BMI user or uploaded mind.
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
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from submodules:
-- |
-- | - **Types**: ResponseCurve ADT and DynamicsMapping record
-- | - **Curve**: Curve application functions
-- |
-- | ## Dependencies
-- |
-- | - Dynamics.Types
-- | - Dynamics.Curve

module Hydrogen.Schema.Brush.Dynamics
  ( module Types
  , module Curve
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Brush.Dynamics.Types
  ( DynamicsMapping(DynamicsMapping)
  , ResponseCurve(Linear, Soft, Firm, SCurve, Logarithmic, Exponential)
  , allResponseCurves
  , constantMapping
  , exponentialMapping
  , firmMapping
  , identityMapping
  , logarithmicMapping
  , responseCurveDescription
  , responseCurveMaxSensitivity
  , sCurveMapping
  , softMapping
  ) as Types

import Hydrogen.Schema.Brush.Dynamics.Curve
  ( applyCurve
  , applyCurveRaw
  , applyMapping
  , clampToEpsilon
  , epsilon
  , lerpUnit
  ) as Curve
