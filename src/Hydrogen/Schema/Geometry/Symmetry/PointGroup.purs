-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                     // hydrogen // schema // geometry // symmetry // pointgroup
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Point Groups — 2D symmetry groups that fix a point.
-- |
-- | ## Design Philosophy
-- |
-- | These are the finite symmetry groups in 2D:
-- | - C_n: Cyclic group (n-fold rotation only)
-- | - D_n: Dihedral group (n-fold rotation + reflections)
-- |
-- | ## Use Cases
-- |
-- | - Classifying symmetry of 2D shapes
-- | - Mathematical group theory
-- | - Pattern generation
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)

module Hydrogen.Schema.Geometry.Symmetry.PointGroup
  ( PointGroup(CyclicGroup, DihedralGroup)
  , pointGroupName
  , pointGroupOrder
  , isCyclic
  , isDihedral
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (*)
  , (<>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // point group classification
-- ═════════════════════════════════════════════════════════════════════════════

-- | 2D Point groups (symmetry groups that fix a point).
-- |
-- | These are the finite symmetry groups in 2D:
-- | - C_n: Cyclic group (n-fold rotational symmetry)
-- | - D_n: Dihedral group (n-fold rotational + n reflections)
data PointGroup
  = CyclicGroup Int      -- ^ C_n: n-fold rotational symmetry
  | DihedralGroup Int    -- ^ D_n: n-fold rotational + n reflections

derive instance eqPointGroup :: Eq PointGroup
derive instance ordPointGroup :: Ord PointGroup

instance showPointGroup :: Show PointGroup where
  show (CyclicGroup n) = "(CyclicGroup n:" <> show n <> ")"
  show (DihedralGroup n) = "(DihedralGroup n:" <> show n <> ")"

-- | Get the name of a point group
pointGroupName :: PointGroup -> String
pointGroupName (CyclicGroup n) = "C_" <> show n
pointGroupName (DihedralGroup n) = "D_" <> show n

-- | Get the order (number of elements) of a point group
pointGroupOrder :: PointGroup -> Int
pointGroupOrder (CyclicGroup n) = n
pointGroupOrder (DihedralGroup n) = 2 * n

-- | Check if point group is cyclic
isCyclic :: PointGroup -> Boolean
isCyclic (CyclicGroup _) = true
isCyclic (DihedralGroup _) = false

-- | Check if point group is dihedral
isDihedral :: PointGroup -> Boolean
isDihedral (DihedralGroup _) = true
isDihedral (CyclicGroup _) = false
