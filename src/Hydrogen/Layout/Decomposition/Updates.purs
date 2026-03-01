-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // layout // decomposition // updates
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Incremental updates and validation utilities.
-- |
-- | This module provides functions for modifying partitions and graphs
-- | while maintaining decomposability invariants.
-- |
-- | ## Lean Correspondence
-- |
-- | The theorem `incremental_decomposable` guarantees that adding
-- | intra-viewport constraints preserves decomposability.

module Hydrogen.Layout.Decomposition.Updates
  ( -- * Incremental Updates
    addElementToViewport
  , addConstraintSafe
  , preservesDecomposability
  
  -- * Validation Utilities
  , allInSameViewport
  , anyUnassigned
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( not
  , ($)
  , (==)
  )

import Data.Array as Array
import Data.Foldable (all, any)
import Data.Maybe (Maybe(Nothing, Just), fromMaybe)
import Data.Tuple (Tuple(..))
import Data.Map as Map
import Data.Set (Set)
import Data.Set as Set

import Hydrogen.Layout.Decomposition.Types
  ( ElementId
  , ViewportId
  , ConstraintEdge
  )
import Hydrogen.Layout.Decomposition.Graph
  ( ConstraintGraph
  , addEdge
  )
import Hydrogen.Layout.Decomposition.Partition
  ( ViewportPartition
  , viewportOf
  , unwrapPartition
  , wrapPartition
  )
import Hydrogen.Layout.Decomposition.Analysis
  ( isCrossViewport
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // incremental updates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add a new element to a viewport.
-- |
-- | This updates the partition but does not add any constraints.
-- | Use `addConstraintSafe` to add constraints that preserve decomposability.
addElementToViewport 
  :: ElementId 
  -> ViewportId 
  -> ViewportPartition 
  -> ViewportPartition
addElementToViewport elemId viewId partition =
  let p = unwrapPartition partition
  in wrapPartition
       { assignment: Map.insert elemId viewId p.assignment
       , viewportElements: Map.alter 
           (\existing -> Just $ Set.insert elemId (fromMaybe Set.empty existing)) 
           viewId p.viewportElements
       , viewports: Set.insert viewId p.viewports
       }

-- | Add a constraint that preserves decomposability.
-- |
-- | Returns `Nothing` if the constraint would cross viewport boundaries.
-- |
-- | ## Lean Correspondence
-- |
-- | The theorem `incremental_decomposable` guarantees that adding
-- | intra-viewport constraints preserves decomposability.
addConstraintSafe 
  :: ConstraintEdge 
  -> ViewportPartition 
  -> ConstraintGraph 
  -> Maybe ConstraintGraph
addConstraintSafe edge partition graph =
  let srcViewport = viewportOf partition edge.source
      tgtViewport = viewportOf partition edge.target
  in case Tuple srcViewport tgtViewport of
    Tuple (Just sv) (Just tv) | sv == tv -> Just (addEdge edge graph)
    _ -> Nothing

-- | Check if adding a constraint would preserve decomposability.
preservesDecomposability 
  :: ConstraintEdge 
  -> ViewportPartition 
  -> Boolean
preservesDecomposability edge partition =
  not (isCrossViewport partition edge)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // validation utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if all elements in a set are in the same viewport.
allInSameViewport :: Set ElementId -> ViewportPartition -> Boolean
allInSameViewport elements partition =
  case Set.toUnfoldable elements :: Array ElementId of
    [] -> true
    xs -> 
      let firstViewport = viewportOf partition (safeHead xs)
      in all (\e -> viewportOf partition e == firstViewport) xs
  where
    safeHead :: Array ElementId -> ElementId
    safeHead arr = fromMaybe "" (Array.head arr)

-- | Check if any element in a set violates viewport assignment.
anyUnassigned :: Set ElementId -> ViewportPartition -> Boolean
anyUnassigned elements partition =
  any (\e -> viewportOf partition e == Nothing) 
      (Set.toUnfoldable elements :: Array ElementId)
