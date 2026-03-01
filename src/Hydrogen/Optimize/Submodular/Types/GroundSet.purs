-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // submodular // groundset
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Ground Set Elements for Submodular Maximization.
-- |
-- | Elements in the ground set V are uniquely identified by an index.
-- | The phantom type ties elements to their ground set for type safety.
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)
-- | - Hydrogen.Schema.Tensor.Dimension (Dim)

module Hydrogen.Optimize.Submodular.Types.GroundSet
  ( Element(Element)
  , ElementSet
  , GroundSet(GroundSet)
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

import Data.Set (Set)

import Hydrogen.Schema.Tensor.Dimension (Dim)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // ground set elements
-- ═════════════════════════════════════════════════════════════════════════════

-- | An element in the ground set V.
-- |
-- | Elements are uniquely identified by an index in [0, n-1] where n = |V|.
-- | The phantom type 'v' ties the element to its ground set.
-- |
-- | The kind of `v` is `Type` - it represents a specific ground set identity.
newtype Element :: Type -> Type
newtype Element v = Element Int

derive instance eqElement :: Eq (Element v)
derive instance ordElement :: Ord (Element v)

instance showElement :: Show (Element v) where
  show (Element i) = "e" <> show i

-- | A set of elements from ground set V.
-- |
-- | Represented as a sorted array for efficient iteration.
-- | Invariant: elements are unique and sorted by index.
type ElementSet :: Type -> Type
type ElementSet v = Set (Element v)

-- | The ground set V of n elements.
-- |
-- | The cardinality n is encoded in the Dim type to enable
-- | compile-time verification of regret bounds.
newtype GroundSet :: Type -> Type
newtype GroundSet v = GroundSet
  { size :: Dim                    -- | n = |V|
  , elements :: Array (Element v)  -- | All elements, indexed [0..n-1]
  }

derive instance eqGroundSet :: Eq (GroundSet v)

instance showGroundSet :: Show (GroundSet v) where
  show (GroundSet g) = "V[" <> show g.size <> "]"
