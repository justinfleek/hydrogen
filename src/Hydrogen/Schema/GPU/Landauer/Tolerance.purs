-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // schema // gpu // landauer // tolerance
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Distortion tolerance and dual sensitivity for precision selection.
-- |
-- | From the Landauer paper, Definition 2 requires dual criteria:
-- | - Forward tolerance (ε_fwd): How much output distortion is acceptable?
-- | - Backward tolerance (ε_bwd): How much gradient distortion is acceptable?
-- |
-- | This module implements the sensitivity analysis and operational precision
-- | calculations that satisfy both forward and backward requirements.

module Hydrogen.Schema.GPU.Landauer.Tolerance
  ( -- * Distortion Tolerance (Definition 2)
    DistortionTolerance
  , distortionTolerance
  , symmetricTolerance
  , toleranceForward
  , toleranceBackward
  
  -- * Dual Sensitivity (Forward/Backward Entropy Flows)
  , forwardSensitivity
  , backwardSensitivity
  , satisfiesForwardTolerance
  , satisfiesBackwardTolerance
  , satisfiesDualTolerance
  
  -- * Operational Precision (Definitions 1 & 2)
  , operationalPrecision
  , effectivePrecision
  , effectivePrecisionSymmetric
  ) where

import Prelude
  ( ($)
  , (-)
  , (>)
  , (<=)
  , (&&)
  )

import Hydrogen.Schema.Bounded as Bounded

import Hydrogen.Schema.GPU.Landauer.Internal
  ( Entropy(Entropy)
  , NaturalPrecision(NaturalPrecision)
  )

import Hydrogen.Schema.GPU.Landauer.Types
  ( intToNumber
  , ceilInt
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // distortion tolerance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Distortion tolerance for precision selection.
-- |
-- | From the paper, Definition 2 requires dual criteria:
-- | - Forward tolerance (ε_fwd): How much output distortion is acceptable?
-- | - Backward tolerance (ε_bwd): How much gradient distortion is acceptable?
-- |
-- | Both are measured in bits of acceptable information loss.
type DistortionTolerance =
  { forward :: Number   -- ε_fwd: Forward (Shannon) tolerance
  , backward :: Number  -- ε_bwd: Backward (Gibbs) tolerance
  }

-- | Create a distortion tolerance (clamped to [0, 64])
distortionTolerance :: Number -> Number -> DistortionTolerance
distortionTolerance fwd bwd =
  { forward: Bounded.clampNumber 0.0 64.0 fwd
  , backward: Bounded.clampNumber 0.0 64.0 bwd
  }

-- | Symmetric tolerance (same for forward and backward)
symmetricTolerance :: Number -> DistortionTolerance
symmetricTolerance eps = distortionTolerance eps eps

-- | Get forward tolerance
toleranceForward :: DistortionTolerance -> Number
toleranceForward t = t.forward

-- | Get backward tolerance
toleranceBackward :: DistortionTolerance -> Number
toleranceBackward t = t.backward

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // dual sensitivity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Forward sensitivity (Shannon entropy flow).
-- |
-- | Measures how much quantization affects forward pass outputs.
-- | Δ→(b) = max(0, H_source - b)
-- |
-- | This is the expected distortion when quantizing to b bits.
forwardSensitivity :: Entropy -> NaturalPrecision -> Number
forwardSensitivity (Entropy sourceH) (NaturalPrecision targetBits) =
  let diff = sourceH - intToNumber targetBits
  in if diff > 0.0 then diff else 0.0

-- | Backward sensitivity (Gibbs entropy flow).
-- |
-- | Measures how much quantization affects gradient computation.
-- | Δ←(b) = max(0, H_gradient - b)
-- |
-- | Gradients often need different precision than activations.
backwardSensitivity :: Entropy -> NaturalPrecision -> Number
backwardSensitivity (Entropy gradH) (NaturalPrecision targetBits) =
  let diff = gradH - intToNumber targetBits
  in if diff > 0.0 then diff else 0.0

-- | Check if a precision satisfies forward tolerance.
-- |
-- | Returns true if Δ→(b) ≤ ε_fwd
satisfiesForwardTolerance :: Entropy -> NaturalPrecision -> DistortionTolerance -> Boolean
satisfiesForwardTolerance h b tol =
  forwardSensitivity h b <= tol.forward

-- | Check if a precision satisfies backward tolerance.
-- |
-- | Returns true if Δ←(b) ≤ ε_bwd
satisfiesBackwardTolerance :: Entropy -> NaturalPrecision -> DistortionTolerance -> Boolean
satisfiesBackwardTolerance h b tol =
  backwardSensitivity h b <= tol.backward

-- | Check if a precision satisfies both tolerances.
-- |
-- | This is the dual criteria from Definition 2.
satisfiesDualTolerance :: Entropy -> Entropy -> NaturalPrecision -> DistortionTolerance -> Boolean
satisfiesDualTolerance forwardH backwardH b tol =
  satisfiesForwardTolerance forwardH b tol && satisfiesBackwardTolerance backwardH b tol

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // operational precision
-- ═════════════════════════════════════════════════════════════════════════════

-- | Operational natural precision (Definition 1 from paper).
-- |
-- | b*_v(ε) = min{ b ∈ ℕ : E[D(φ_v(x), φ_v(Q_b(x)))] ≤ ε }
-- |
-- | Given entropy and tolerance, find minimum bits where distortion ≤ tolerance.
-- | This is the ceiling of (entropy - tolerance), clamped to [1, 64].
operationalPrecision :: Entropy -> Number -> NaturalPrecision
operationalPrecision (Entropy h) tolerance =
  let
    effectiveH = h - tolerance
    bits = if effectiveH <= 0.0 then 1 else ceilInt effectiveH
  in
    NaturalPrecision (Bounded.clampInt 1 64 bits)

-- | Effective precision under dual criteria (Definition 2 from paper).
-- |
-- | b*_v = min{ b : Δ→_v(b) ≤ ε_fwd AND Δ←_v(b) ≤ ε_bwd }
-- |
-- | This finds the minimum precision that satisfies BOTH forward and backward
-- | tolerance requirements. The effective precision is:
-- |
-- |   b* = max(⌈H_fwd - ε_fwd⌉, ⌈H_bwd - ε_bwd⌉)
effectivePrecision :: Entropy -> Entropy -> DistortionTolerance -> NaturalPrecision
effectivePrecision (Entropy forwardH) (Entropy backwardH) tol =
  let
    fwdBits = forwardH - tol.forward
    bwdBits = backwardH - tol.backward
    maxBits = if fwdBits > bwdBits then fwdBits else bwdBits
    bits = if maxBits <= 0.0 then 1 else ceilInt maxBits
  in
    NaturalPrecision (Bounded.clampInt 1 64 bits)

-- | Effective precision with same entropy for both flows.
-- |
-- | Simplified version when forward and backward entropy are equal.
effectivePrecisionSymmetric :: Entropy -> DistortionTolerance -> NaturalPrecision
effectivePrecisionSymmetric h tol = effectivePrecision h h tol
