-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // submodular // blackwell
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Blackwell Approachability Types.
-- |
-- | Blackwell's approachability theorem (1956) provides the foundation for
-- | online learning algorithms with vector-valued payoffs.
-- |
-- | ## Core Concept
-- |
-- | The algorithm maintains dual variables to approach a convex target set.
-- | For submodular maximization, the target encodes the α-regret guarantee.
-- |
-- | ## References
-- |
-- | - Blackwell, D. "An analog of the minimax theorem for vector payoffs"
-- |   Pacific J. Math. 6(1), 1-8 (1956)
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Show)

module Hydrogen.Optimize.Submodular.Types.Blackwell
  ( TargetSet(TargetSet)
  , ResponseSet(ResponseSet)
  , PayoffVector(PayoffVector)
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
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // blackwell approachability
-- ═════════════════════════════════════════════════════════════════════════════

-- | Target set for Blackwell approachability.
-- |
-- | The algorithm maintains dual variables to approach this convex set.
-- | For submodular maximization, the target encodes the α-regret guarantee.
newtype TargetSet :: Type -> Type
newtype TargetSet d = TargetSet
  { halfspaces :: Array { normal :: Array Number, offset :: Number }
  }

-- | Response set for Blackwell approachability.
-- |
-- | Given adversary's action, the learner's response set contains
-- | all achievable payoffs.
newtype ResponseSet :: Type -> Type
newtype ResponseSet d = ResponseSet
  { vertices :: Array (Array Number)     -- ^ Extreme points of response polytope
  }

-- | Payoff vector in the Blackwell game.
-- |
-- | u_t ∈ ℝ^d is the vector payoff at round t.
newtype PayoffVector :: Type -> Type
newtype PayoffVector d = PayoffVector (Array Number)

instance eqPayoffVector :: Eq (PayoffVector d) where
  eq (PayoffVector a) (PayoffVector b) = a == b

instance showPayoffVector :: Show (PayoffVector d) where
  show (PayoffVector v) = "u=" <> show v
