-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // layout // decomposition // partition
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Viewport partition operations.
-- |
-- | A partition of elements into viewports: P = {V1, ..., Vk}
-- | where each Vi is a set of elements.
-- |
-- | ## Lean Correspondence
-- |
-- | This implements `ViewportPartition` from the Lean proofs.
-- | The `assignment` field corresponds to the function `Fin n -> Fin k`.
-- |
-- | ## Invariants
-- |
-- | - Each element is assigned to exactly one viewport
-- | - Viewports form a partition (cover all elements, pairwise disjoint)

module Hydrogen.Layout.Decomposition.Partition
  ( -- * Viewport Partition
    ViewportPartition
  , mkViewportPartition
  , viewportOf
  , elementsIn
  , viewportCount
  , viewportSize
  , maxViewportSize
  , unwrapPartition
  , wrapPartition
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , map
  , max
  , show
  , ($)
  , (<>)
  )

import Data.Foldable (foldl)
import Data.Maybe (Maybe(Just), fromMaybe)
import Data.Map (Map)
import Data.Map as Map
import Data.Set (Set)
import Data.Set as Set

import Hydrogen.Layout.Decomposition.Types
  ( ElementId
  , ViewportId
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // viewport partition
-- ═════════════════════════════════════════════════════════════════════════════

-- | A partition of elements into viewports.
-- |
-- | P = {V1, ..., Vk} where each V_i is a set of elements.
-- |
-- | ## Lean Correspondence
-- |
-- | This implements `ViewportPartition` from the Lean proofs.
-- | The `assignment` field corresponds to the function `Fin n -> Fin k`.
-- |
-- | ## Invariants
-- |
-- | - Each element is assigned to exactly one viewport
-- | - Viewports form a partition (cover all elements, pairwise disjoint)
newtype ViewportPartition = ViewportPartition
  { assignment :: Map ElementId ViewportId
  , viewportElements :: Map ViewportId (Set ElementId)
  , viewports :: Set ViewportId
  }

derive instance eqViewportPartition :: Eq ViewportPartition

instance showViewportPartition :: Show ViewportPartition where
  show (ViewportPartition p) =
    "ViewportPartition{k=" <> show (Set.size p.viewports) <> "}"

-- | Create a viewport partition from element-viewport assignments.
mkViewportPartition :: Array { element :: ElementId, viewport :: ViewportId } -> ViewportPartition
mkViewportPartition assignments =
  let
    assignment = foldl (\m a -> Map.insert a.element a.viewport m) Map.empty assignments
    viewportElements = foldl (\m a -> 
      Map.alter (\existing -> Just $ Set.insert a.element (fromMaybe Set.empty existing)) 
                a.viewport m) Map.empty assignments
    viewports = Set.fromFoldable $ map _.viewport assignments
  in
    ViewportPartition
      { assignment
      , viewportElements
      , viewports
      }

-- | Get the viewport an element belongs to.
viewportOf :: ViewportPartition -> ElementId -> Maybe ViewportId
viewportOf (ViewportPartition p) elemId = Map.lookup elemId p.assignment

-- | Get all elements in a viewport.
elementsIn :: ViewportPartition -> ViewportId -> Set ElementId
elementsIn (ViewportPartition p) viewId = 
  fromMaybe Set.empty (Map.lookup viewId p.viewportElements)

-- | Count the number of viewports.
viewportCount :: ViewportPartition -> Int
viewportCount (ViewportPartition p) = Set.size p.viewports

-- | Get the size of a viewport (number of elements).
viewportSize :: ViewportPartition -> ViewportId -> Int
viewportSize partition viewId = Set.size (elementsIn partition viewId)

-- | Get the maximum viewport size.
maxViewportSize :: ViewportPartition -> Int
maxViewportSize partition@(ViewportPartition p) =
  foldl max 0 (map (viewportSize partition) (Set.toUnfoldable p.viewports :: Array ViewportId))

-- | Unwrap a ViewportPartition to access its internal structure.
-- |
-- | This is needed for functions that need to iterate over all viewports.
unwrapPartition :: ViewportPartition 
                -> { assignment :: Map ElementId ViewportId
                   , viewportElements :: Map ViewportId (Set ElementId)
                   , viewports :: Set ViewportId 
                   }
unwrapPartition (ViewportPartition p) = p

-- | Wrap an internal structure into a ViewportPartition.
-- |
-- | This is the inverse of unwrapPartition, used for incremental updates.
wrapPartition :: { assignment :: Map ElementId ViewportId
                 , viewportElements :: Map ViewportId (Set ElementId)
                 , viewports :: Set ViewportId 
                 }
              -> ViewportPartition
wrapPartition = ViewportPartition
