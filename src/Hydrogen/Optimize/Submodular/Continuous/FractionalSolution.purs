-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--          // hydrogen // optimize // submodular // continuous // fractional solution
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Fractional solutions for continuous submodular optimization.
-- |
-- | ## Theoretical Foundation
-- |
-- | A fractional solution x ∈ [0,1]^n represents a point in the unit hypercube.
-- | Each coordinate x_e represents the probability/fraction of including
-- | element e in the solution.
-- |
-- | ## Type Safety (P1 Council Enhancement)
-- |
-- | Coordinates are `UnitInterval`, not raw `Number`. This guarantees:
-- | - Values are always in [0.0, 1.0]
-- | - No invalid polytope states can exist
-- | - Agents receiving solutions don't need defensive clamping
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Bounded (UnitInterval)
-- | - Hydrogen.Schema.Tensor.Dimension (Dim)
-- | - Hydrogen.Optimize.Submodular.Types (Element, GroundSet)

module Hydrogen.Optimize.Submodular.Continuous.FractionalSolution
  ( FractionalSolution(FractionalSolution)
  , mkFractionalSolution
  , mkFractionalSolutionBounded
  , solutionValue
  , solutionValueBounded
  , solutionCoord
  , solutionCoordBounded
  , solutionCoords
  , solutionSupport
  , zeroes
  , ones
  , uniform
  , addScaled
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , map
  , show
  , (+)
  , (-)
  , (*)
  , (>)
  , (<>)
  )

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Maybe (Maybe(Nothing, Just))
import Data.Set (Set)
import Data.Set as Set
import Data.Map (Map)
import Data.Map as Map

import Hydrogen.Schema.Bounded 
  ( UnitInterval
  , clampUnit
  , unwrapUnit
  , unitZero
  , unitOne
  )
import Hydrogen.Schema.Tensor.Dimension (unwrapDim)
import Hydrogen.Optimize.Submodular.Types
  ( Element(Element)
  , GroundSet(GroundSet)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // fractional solution
-- ═════════════════════════════════════════════════════════════════════════════

-- | A fractional solution x ∈ [0,1]^n.
-- |
-- | Each coordinate x_e represents the probability/fraction of including
-- | element e in the solution.
-- |
-- | Stored as a sparse map: elements not in the map have value 0.
newtype FractionalSolution :: Type -> Type
newtype FractionalSolution v = FractionalSolution
  { groundSetSize :: Int
  , coords :: Map Int UnitInterval    -- ^ Element index → fractional value in [0,1]
  }

derive instance eqFractionalSolution :: Eq (FractionalSolution v)

instance showFractionalSolution :: Show (FractionalSolution v) where
  show (FractionalSolution { coords }) =
    "FractionalSolution[" <> show (Map.size coords) <> " nonzero]"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a fractional solution from raw Number coordinates.
-- |
-- | Values are clamped to [0, 1] and wrapped in UnitInterval.
mkFractionalSolution :: forall v. GroundSet v -> Map Int Number -> FractionalSolution v
mkFractionalSolution (GroundSet { size }) rawCoords =
  let clamped = map clampUnit rawCoords
  in FractionalSolution { groundSetSize: unwrapDim size, coords: clamped }

-- | Create a fractional solution from UnitInterval coordinates.
-- |
-- | No clamping needed — UnitInterval guarantees validity.
mkFractionalSolutionBounded :: forall v. GroundSet v -> Map Int UnitInterval -> FractionalSolution v
mkFractionalSolutionBounded (GroundSet { size }) coords =
  FractionalSolution { groundSetSize: unwrapDim size, coords }

-- | The zero solution (all coordinates 0).
zeroes :: forall v. GroundSet v -> FractionalSolution v
zeroes (GroundSet { size }) =
  FractionalSolution { groundSetSize: unwrapDim size, coords: Map.empty }

-- | The all-ones solution (all coordinates 1).
ones :: forall v. GroundSet v -> FractionalSolution v
ones (GroundSet { size, elements }) =
  let coords = foldl (\acc (Element i) -> Map.insert i unitOne acc) Map.empty elements
  in FractionalSolution { groundSetSize: unwrapDim size, coords }

-- | Uniform solution: all coordinates equal to p.
uniform :: forall v. GroundSet v -> Number -> FractionalSolution v
uniform (GroundSet { size, elements }) p =
  let clampedP = clampUnit p
      coords = foldl (\acc (Element i) -> Map.insert i clampedP acc) Map.empty elements
  in FractionalSolution { groundSetSize: unwrapDim size, coords }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the value at a coordinate as raw Number.
-- |
-- | Returns 0.0 for elements not in the support.
solutionValue :: forall v. FractionalSolution v -> Int -> Number
solutionValue (FractionalSolution { coords }) i =
  case Map.lookup i coords of
    Nothing -> 0.0
    Just x -> unwrapUnit x

-- | Get the bounded coordinate for an element.
-- |
-- | Returns unitZero for elements not in the support.
solutionValueBounded :: forall v. FractionalSolution v -> Int -> UnitInterval
solutionValueBounded (FractionalSolution { coords }) i =
  case Map.lookup i coords of
    Nothing -> unitZero
    Just x -> x

-- | Get the coordinate for an element as raw Number.
solutionCoord :: forall v. FractionalSolution v -> Element v -> Number
solutionCoord sol (Element i) = solutionValue sol i

-- | Get the bounded coordinate for an element.
solutionCoordBounded :: forall v. FractionalSolution v -> Element v -> UnitInterval
solutionCoordBounded sol (Element i) = solutionValueBounded sol i

-- | Get all coordinates as an array (dense representation, raw Numbers).
solutionCoords :: forall v. FractionalSolution v -> Array Number
solutionCoords (FractionalSolution { groundSetSize, coords }) =
  map (\i -> case Map.lookup i coords of
    Nothing -> 0.0
    Just x -> unwrapUnit x) (Array.range 0 (groundSetSize - 1))

-- | Get the support: elements with x_e > 0.
solutionSupport :: forall v. FractionalSolution v -> Set (Element v)
solutionSupport (FractionalSolution { coords }) =
  let nonzero = Map.filter (\x -> unwrapUnit x > 0.0) coords
      indexSet = Map.keys nonzero
      indices = Set.toUnfoldable indexSet :: Array Int
  in Set.fromFoldable (map Element indices)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // arithmetic
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add scaled direction to solution: x + α·d
-- |
-- | Unwraps UnitInterval, performs arithmetic, then clamps result.
addScaled :: forall v. FractionalSolution v -> Number -> FractionalSolution v -> FractionalSolution v
addScaled (FractionalSolution { groundSetSize, coords: x }) alpha (FractionalSolution { coords: d }) =
  let 
      -- Unwrap to Numbers
      xNum = map unwrapUnit x
      dNum = map unwrapUnit d
      -- Add scaled direction
      newCoords = Map.unionWith (+) xNum (map (\v -> alpha * v) dNum)
      -- Clamp back to UnitInterval
      clamped = map clampUnit newCoords
  in FractionalSolution { groundSetSize, coords: clamped }
