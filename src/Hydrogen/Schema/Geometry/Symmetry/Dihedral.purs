-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // schema // geometry // symmetry // dihedral
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Dihedral Symmetry — Combined rotation and reflection.
-- |
-- | ## Design Philosophy
-- |
-- | Dihedral group D_n has:
-- | - N-fold rotational symmetry
-- | - N reflection axes
-- |
-- | Examples:
-- | - D_3: equilateral triangle (3 rotations, 3 reflections)
-- | - D_4: square (4 rotations, 4 reflections)
-- | - D_6: regular hexagon (6 rotations, 6 reflections)
-- |
-- | ## Use Cases
-- |
-- | - Regular polygon symmetry
-- | - Logo and icon design
-- | - Symmetric UI components
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)

module Hydrogen.Schema.Geometry.Symmetry.Dihedral
  ( DihedralSymmetry(DihedralSymmetry)
  , dihedralSymmetry
  , dihedral2
  , dihedral3
  , dihedral4
  , dihedral5
  , dihedral6
  , dihedral8
  , dihedralFoldCount
  , dihedralReflectionCount
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
  , (<)
  , otherwise
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // dihedral symmetry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Dihedral symmetry: rotation + reflection combined.
-- |
-- | Dihedral group D_n has:
-- | - N-fold rotational symmetry
-- | - N reflection axes
newtype DihedralSymmetry = DihedralSymmetry { n :: Int }

derive instance eqDihedralSymmetry :: Eq DihedralSymmetry
derive instance ordDihedralSymmetry :: Ord DihedralSymmetry

instance showDihedralSymmetry :: Show DihedralSymmetry where
  show (DihedralSymmetry d) = "(DihedralSymmetry n:" <> show d.n <> ")"

-- | Create dihedral symmetry D_n
dihedralSymmetry :: Int -> DihedralSymmetry
dihedralSymmetry n
  | n < 1 = DihedralSymmetry { n: 1 }
  | otherwise = DihedralSymmetry { n }

-- | D_2: Rectangle symmetry (2 rotations, 2 reflections)
dihedral2 :: DihedralSymmetry
dihedral2 = DihedralSymmetry { n: 2 }

-- | D_3: Equilateral triangle symmetry
dihedral3 :: DihedralSymmetry
dihedral3 = DihedralSymmetry { n: 3 }

-- | D_4: Square symmetry
dihedral4 :: DihedralSymmetry
dihedral4 = DihedralSymmetry { n: 4 }

-- | D_5: Regular pentagon symmetry
dihedral5 :: DihedralSymmetry
dihedral5 = DihedralSymmetry { n: 5 }

-- | D_6: Regular hexagon symmetry
dihedral6 :: DihedralSymmetry
dihedral6 = DihedralSymmetry { n: 6 }

-- | D_8: Regular octagon symmetry
dihedral8 :: DihedralSymmetry
dihedral8 = DihedralSymmetry { n: 8 }

-- | Get the fold count of dihedral symmetry
dihedralFoldCount :: DihedralSymmetry -> Int
dihedralFoldCount (DihedralSymmetry d) = d.n

-- | Get the number of reflection axes in dihedral symmetry
dihedralReflectionCount :: DihedralSymmetry -> Int
dihedralReflectionCount (DihedralSymmetry d) = d.n
