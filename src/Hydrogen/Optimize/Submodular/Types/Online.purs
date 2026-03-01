-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // submodular // online
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Online Learning State and Graded Monad Types.
-- |
-- | Types for tracking state in online submodular maximization:
-- | - Time horizon and rounds
-- | - Cumulative gradients for Frank-Wolfe updates
-- | - Dual variables for Blackwell approachability
-- | - Regret bounds
-- |
-- | ## Graded Monad
-- |
-- | OnlineLearn tracks co-effects: what resources the computation NEEDS
-- | (rounds, oracle access, regret budget) rather than what it produces.
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show, Semigroup, Monoid, Semiring)
-- | - Hydrogen.Schema.Tensor.Dimension (Dim)
-- | - Hydrogen.Optimize.Submodular.Types.GroundSet (Element)

module Hydrogen.Optimize.Submodular.Types.Online
  ( TimeHorizon(TimeHorizon)
  , Round(Round)
  , CumulativeGradient(CumulativeGradient)
  , DualVariable(DualVariable)
  , RegretBound(RegretBound)
  , OnlineGrade(..)
  , OnlineLearn
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
  , class Semiring
  , show
  , (<>)
  , (+)
  , (*)
  )

import Data.Map (Map)
import Data.Maybe (Maybe(Nothing, Just))

import Hydrogen.Schema.Tensor.Dimension (Dim(Dim))

import Hydrogen.Optimize.Submodular.Types.GroundSet (Element)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // online learning state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Time horizon T (number of rounds).
-- |
-- | May be known in advance (finite horizon) or unknown (anytime).
newtype TimeHorizon = TimeHorizon (Maybe Dim)

derive instance eqTimeHorizon :: Eq TimeHorizon

instance showTimeHorizon :: Show TimeHorizon where
  show (TimeHorizon Nothing) = "T=∞"
  show (TimeHorizon (Just (Dim t))) = "T=" <> show t

-- | Current round t ∈ [1, T].
newtype Round = Round Int

derive instance eqRound :: Eq Round
derive instance ordRound :: Ord Round

instance showRound :: Show Round where
  show (Round t) = "t=" <> show t

instance semiringRound :: Semiring Round where
  add (Round a) (Round b) = Round (a + b)
  mul (Round a) (Round b) = Round (a * b)
  zero = Round 0
  one = Round 1

-- | Cumulative gradient for an element across rounds.
-- |
-- | In the continuous relaxation, we track:
-- |   ∇_e = Σ_{t=1}^T ∂f_t/∂x_e
-- |
-- | This drives the Frank-Wolfe style update.
newtype CumulativeGradient :: Type -> Type
newtype CumulativeGradient v = CumulativeGradient
  { gradients :: Map (Element v) Number  -- ^ Per-element cumulative gradient
  , round :: Round                       -- ^ Current round
  }

-- | Dual variable for Blackwell approachability.
-- |
-- | The dual λ ∈ ℝ^d tracks the direction to the target set.
newtype DualVariable :: Type -> Type
newtype DualVariable d = DualVariable
  { components :: Array Number           -- ^ λ components
  , dimension :: Dim                     -- ^ d (dimension of dual space)
  }

-- | Regret bound guarantee.
-- |
-- | Encodes the theoretical bound: R(T) ≤ bound(k, T, n)
-- |
-- | For Harvey/Liaw/Soma: O(√(kT ln(n/k)))
newtype RegretBound = RegretBound
  { value :: Number                      -- ^ Numerical bound value
  , asymptotics :: String                -- ^ Asymptotic form (e.g., "√(kT ln(n/k))")
  , tight :: Boolean                     -- ^ Whether bound is known to be tight
  }

derive instance eqRegretBound :: Eq RegretBound

instance showRegretBound :: Show RegretBound where
  show (RegretBound r) = "O(" <> r.asymptotics <> ")≤" <> show r.value

-- ═════════════════════════════════════════════════════════════════════════════
--                                           // graded monad for online learning
-- ═════════════════════════════════════════════════════════════════════════════

-- | Grade for the online learning monad.
-- |
-- | Tracks what resources/state the computation has accumulated:
-- | - Rounds elapsed
-- | - Cumulative regret
-- | - Dual variable state
-- |
-- | Grades form a monoid under composition:
-- |   pure : G_0
-- |   bind : G_a → (a → G_b) → G_(a ⊕ b)
data OnlineGrade = OnlineGrade
  { rounds :: Int                        -- ^ Rounds elapsed
  , regret :: Number                     -- ^ Cumulative regret
  , queries :: Int                       -- ^ Oracle queries made
  }

derive instance eqOnlineGrade :: Eq OnlineGrade

instance showOnlineGrade :: Show OnlineGrade where
  show (OnlineGrade g) = 
    "⟨t=" <> show g.rounds 
    <> ",R=" <> show g.regret 
    <> ",q=" <> show g.queries <> "⟩"

instance semigroupOnlineGrade :: Semigroup OnlineGrade where
  append (OnlineGrade a) (OnlineGrade b) = OnlineGrade
    { rounds: a.rounds + b.rounds
    , regret: a.regret + b.regret
    , queries: a.queries + b.queries
    }

instance monoidOnlineGrade :: Monoid OnlineGrade where
  mempty = OnlineGrade { rounds: 0, regret: 0.0, queries: 0 }

-- | Graded monad for online learning computations.
-- |
-- | OnlineLearn g a represents a computation that:
-- | - Consumes grade g (rounds, regret, queries)
-- | - Produces a value of type a
-- |
-- | The graded monad laws ensure composition tracks cumulative resources.
-- |
-- | ## Co-Effect Interpretation
-- |
-- | The grade is a CO-EFFECT: it describes what the computation NEEDS
-- | (rounds to observe, oracle access, regret budget) rather than what
-- | it produces.
-- |
-- | This enables:
-- | - Static verification of regret bounds
-- | - Compile-time oracle query counting
-- | - Resource-aware scheduling
type OnlineLearn (g :: OnlineGrade) a = 
  { run :: a                             -- ^ The computed value
  , grade :: OnlineGrade                 -- ^ The grade (resources consumed)
  }
