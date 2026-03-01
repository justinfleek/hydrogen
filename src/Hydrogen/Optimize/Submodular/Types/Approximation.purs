-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // submodular // approximation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Approximation Ratio Types for Submodular Maximization.
-- |
-- | An α-approximation algorithm guarantees: ALG ≥ α · OPT
-- |
-- | ## Standard Ratios
-- |
-- | - Monotone + cardinality: (1 - 1/e) ≈ 0.632
-- | - Non-monotone + cardinality: 1/2
-- | - Monotone + matroid: (1 - 1/e) ≈ 0.632
-- | - Non-monotone + matroid: (e-1)/(2e-1) ≈ 0.401
-- |
-- | ## Phantom Types
-- |
-- | Approximation ratios are encoded as phantom types to track guarantees
-- | statically through the type system.
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Show)

module Hydrogen.Optimize.Submodular.Types.Approximation
  ( ApproxRatio
      ( ExactRatio
      , MonotoneMatroidRatio
      , NonMonotoneMatroidRatio
      , HalfRatio
      , CustomRatio
      )
  , AlphaRegret(AlphaRegret)
  , MonotoneOPT
  , NonMonotoneOPT
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  , (==)
  , (&&)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                       // approximation ratios (phantom types)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Approximation ratio α for submodular maximization.
-- |
-- | An α-approximation algorithm guarantees:
-- |   ALG ≥ α · OPT
-- |
-- | Encoded as a phantom type to track approximation guarantees statically.
-- |
-- | Standard ratios:
-- | - Monotone + cardinality: (1 - 1/e) ≈ 0.632
-- | - Non-monotone + cardinality: 1/2
-- | - Monotone + matroid: (1 - 1/e) ≈ 0.632
-- | - Non-monotone + matroid: (e-1)/(2e-1) ≈ 0.401
data ApproxRatio
  = ExactRatio              -- ^ α = 1 (optimal)
  | MonotoneMatroidRatio    -- ^ α = 1 - 1/e ≈ 0.632
  | NonMonotoneMatroidRatio -- ^ α = (e-1)/(2e-1) ≈ 0.401
  | HalfRatio               -- ^ α = 1/2
  | CustomRatio Number      -- ^ α = custom value in (0, 1]

-- | Type-level encoding of (1 - 1/e) optimal for monotone.
data MonotoneOPT

-- | Type-level encoding of 1/2 optimal for non-monotone.
data NonMonotoneOPT

-- | α-regret in online learning context.
-- |
-- | For online submodular maximization, we measure α-regret:
-- |   R_α(T) = α · Σ f_t(S_t*) - Σ f_t(S_t)
-- |
-- | Where S_t* = argmax_{S ∈ I} f_t(S) is the offline optimum for round t.
-- |
-- | Harvey/Liaw/Soma achieve O(√(kT ln(n/k))) first-order α-regret.
newtype AlphaRegret :: ApproxRatio -> Type
newtype AlphaRegret (α :: ApproxRatio) = AlphaRegret
  { cumulative :: Number           -- ^ Cumulative regret so far
  , bound :: Number                -- ^ Theoretical upper bound
  , alpha :: Number                -- ^ The approximation ratio value
  }

instance eqAlphaRegret :: Eq (AlphaRegret α) where
  eq (AlphaRegret a) (AlphaRegret b) = 
    a.cumulative == b.cumulative && a.bound == b.bound && a.alpha == b.alpha

instance showAlphaRegret :: Show (AlphaRegret α) where
  show (AlphaRegret r) = "R_" <> show r.alpha <> "=" <> show r.cumulative
