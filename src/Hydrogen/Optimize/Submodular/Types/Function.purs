-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // submodular // function
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core Submodular Function Types.
-- |
-- | A submodular function f : 2^V → ℝ₊ satisfies diminishing returns:
-- | for all A ⊆ B and e ∉ B, f(A ∪ {e}) - f(A) ≥ f(B ∪ {e}) - f(B)
-- |
-- | ## Oracle Model
-- |
-- | We assume value oracle access: given S ⊆ V, return f(S).
-- | Marginal gain oracle: given e and S, return f(S ∪ {e}) - f(S).
-- |
-- | ## Phantom Types
-- |
-- | The SubmodularFn type encodes static guarantees via phantom types:
-- | - `v`: Ground set type
-- | - `m`: Monotonicity (Monotone or NonMonotone)
-- | - `κ`: Curvature bound
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show, Semigroup, Monoid)
-- | - Hydrogen.Optimize.Submodular.Types.GroundSet
-- | - Hydrogen.Optimize.Submodular.Types.Classification

module Hydrogen.Optimize.Submodular.Types.Function
  ( SubmodularFn
  , SubmodularOracle(SubmodularOracle)
  , MarginalGain(MarginalGain)
  , SetValue(SetValue)
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , class Semigroup
  , class Monoid
  , show
  , (<>)
  , (+)
  )

import Data.Maybe (Maybe)

import Hydrogen.Optimize.Submodular.Types.GroundSet
  ( Element
  , ElementSet
  , GroundSet
  )

import Hydrogen.Optimize.Submodular.Types.Classification
  ( Monotonicity
  , Curvature
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                              // core submodular function type
-- ═════════════════════════════════════════════════════════════════════════════

-- | A value returned by evaluating f(S).
-- |
-- | Values are non-negative reals. We use Number but enforce non-negativity.
newtype SetValue = SetValue Number

derive instance eqSetValue :: Eq SetValue
derive instance ordSetValue :: Ord SetValue

instance showSetValue :: Show SetValue where
  show (SetValue v) = show v

instance semigroupSetValue :: Semigroup SetValue where
  append (SetValue a) (SetValue b) = SetValue (a + b)

instance monoidSetValue :: Monoid SetValue where
  mempty = SetValue 0.0

-- | Marginal gain from adding element e to set S.
-- |
-- | Δf(e | S) = f(S ∪ {e}) - f(S)
-- |
-- | For submodular functions, marginal gains are non-increasing as S grows.
newtype MarginalGain = MarginalGain Number

derive instance eqMarginalGain :: Eq MarginalGain
derive instance ordMarginalGain :: Ord MarginalGain

instance showMarginalGain :: Show MarginalGain where
  show (MarginalGain g) = "Δ" <> show g

instance semigroupMarginalGain :: Semigroup MarginalGain where
  append (MarginalGain a) (MarginalGain b) = MarginalGain (a + b)

instance monoidMarginalGain :: Monoid MarginalGain where
  mempty = MarginalGain 0.0

-- | A submodular function f : 2^V → ℝ₊.
-- |
-- | Phantom types encode static guarantees:
-- | - `v`: Ground set type
-- | - `m`: Monotonicity (Monotone or NonMonotone)
-- | - `κ`: Curvature bound
-- |
-- | The oracle provides access to f(S) and marginal gains.
type SubmodularFn :: Type -> Monotonicity -> Curvature -> Type
type SubmodularFn v (m :: Monotonicity) (κ :: Curvature) = SubmodularOracle v

-- | Oracle interface for evaluating a submodular function.
-- |
-- | Separates the "what" (SubmodularFn type) from the "how" (oracle impl).
-- |
-- | ## Oracle Model
-- |
-- | We assume value oracle access: given S ⊆ V, return f(S).
-- | Marginal gain oracle: given e and S, return f(S ∪ {e}) - f(S).
-- |
-- | In practice, marginal gains may be computed more efficiently than
-- | full set evaluation (e.g., for graph cuts, coverage functions).
newtype SubmodularOracle :: Type -> Type
newtype SubmodularOracle v = SubmodularOracle
  { -- | Evaluate f(S)
    eval :: ElementSet v -> SetValue
    
    -- | Evaluate marginal gain Δf(e | S) = f(S ∪ {e}) - f(S)
  , marginal :: Element v -> ElementSet v -> MarginalGain
  
    -- | Ground set
  , groundSet :: GroundSet v
  
    -- | Upper bound on f(OPT) if known (for normalized functions)
  , fMax :: Maybe SetValue
  }
