-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // submodular // classification
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Submodular Function Classification Types.
-- |
-- | Monotonicity and curvature classification for submodular functions.
-- | These properties determine achievable approximation ratios.
-- |
-- | ## Monotonicity
-- |
-- | - **Monotone**: f(A) ≤ f(B) whenever A ⊆ B (adding elements never decreases value)
-- | - **NonMonotone**: f(A) can exceed f(B) even when A ⊆ B
-- |
-- | ## Curvature
-- |
-- | Curvature κ ∈ [0, 1] measures how far from modular (additive) f is:
-- | - κ = 0: f is modular (linear)
-- | - κ = 1: f has maximum submodularity
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)

module Hydrogen.Optimize.Submodular.Types.Classification
  ( Monotonicity
      ( Monotone
      , NonMonotone
      )
  , Curvature
      ( CurvatureUnknown
      , CurvatureBounded
      , CurvatureExact
      )
  , CurvatureWitness(CurvatureWitness)
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
--                                         // submodular function classification
-- ═════════════════════════════════════════════════════════════════════════════

-- | Monotonicity classification of a submodular function.
-- |
-- | **Monotone**: f(A) ≤ f(B) whenever A ⊆ B
-- |   - Adding elements never decreases value
-- |   - Achievable approximation ratio: (1 - 1/e) ≈ 0.632
-- |
-- | **NonMonotone**: f(A) can be > f(B) even when A ⊆ B
-- |   - Adding elements may decrease value
-- |   - Achievable approximation ratio: 1/2
data Monotonicity
  = Monotone
  | NonMonotone

derive instance eqMonotonicity :: Eq Monotonicity
derive instance ordMonotonicity :: Ord Monotonicity

instance showMonotonicity :: Show Monotonicity where
  show Monotone = "Monotone"
  show NonMonotone = "NonMonotone"

-- | Curvature of a submodular function.
-- |
-- | Curvature κ ∈ [0, 1] measures how far from modular (additive) f is:
-- |
-- | κ = 1 - min_{e ∈ V, S ⊆ V\{e}} [f(S ∪ {e}) - f(S)] / [f({e}) - f(∅)]
-- |
-- | - κ = 0: f is modular (linear)
-- | - κ = 1: f has maximum submodularity
-- |
-- | Tighter curvature bounds enable better approximation ratios:
-- | - General submodular: (1 - 1/e) ≈ 0.632
-- | - Curvature κ: (1 - e^{-κ})/κ (approaches 1 as κ → 0)
data Curvature
  = CurvatureUnknown              -- ^ κ = 1 assumed (worst case)
  | CurvatureBounded Number       -- ^ κ ≤ bound, where bound ∈ [0, 1]
  | CurvatureExact Number         -- ^ κ = exact, where exact ∈ [0, 1]

derive instance eqCurvature :: Eq Curvature

instance showCurvature :: Show Curvature where
  show CurvatureUnknown = "κ≤1"
  show (CurvatureBounded k) = "κ≤" <> show k
  show (CurvatureExact k) = "κ=" <> show k

-- | A witness that a function has specific curvature.
-- |
-- | The witness encodes a proof (or certificate) that the function
-- | satisfies the curvature bound. This enables the type system to
-- | track curvature through compositions.
newtype CurvatureWitness (κ :: Curvature) = CurvatureWitness
  { bound :: Number                -- ^ The curvature bound value
  , certified :: Boolean           -- ^ Whether bound has been verified
  }
