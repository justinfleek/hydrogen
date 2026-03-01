-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // layout // decomposition // solve
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Solution composition and parallel solving interface.
-- |
-- | This module provides the interface for solving decomposed layouts
-- | in parallel and composing the results.
-- |
-- | ## Lean Correspondence
-- |
-- | The theorem `parallel_solve_correct` guarantees that composing
-- | independent solutions yields a globally valid solution.
-- |
-- | ## Complexity
-- |
-- | - Parallel solve: O(max_i n_i^3) with k processors
-- | - Solution composition: O(n log n)

module Hydrogen.Layout.Decomposition.Solve
  ( -- * Solution Composition
    ViewportSolution
  , composeSolutions
  
  -- * Parallel Solving Interface
  , DecomposedLayout
  , ViewportSubproblem
  , extractSubproblems
  , solveDecomposed
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Ord
  , bind
  , compare
  , map
  , ($)
  )

import Data.Array as Array
import Data.Maybe (Maybe(Just))
import Data.Map (Map)
import Data.Map as Map
import Data.Set as Set

import Hydrogen.Layout.ILP.Formulate
  ( LayoutResult
  )
import Hydrogen.Layout.Encode
  ( LayoutElement
  , ContainerSpec
  )
import Hydrogen.Layout.Decomposition.Types
  ( ViewportId
  )
import Hydrogen.Layout.Decomposition.Graph
  ( ConstraintGraph
  )
import Hydrogen.Layout.Decomposition.Partition
  ( ViewportPartition
  , unwrapPartition
  )
import Hydrogen.Layout.Decomposition.Analysis
  ( extractSubgraphs
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // solution composition
-- ═════════════════════════════════════════════════════════════════════════════

-- | A solution for a single viewport.
type ViewportSolution =
  { viewportId :: ViewportId
  , results :: Array LayoutResult
  }

-- | Compose solutions from independent viewport solves.
-- |
-- | Precondition: All viewports solved successfully
-- |
-- | ## Lean Correspondence
-- |
-- | The theorem `parallel_solve_correct` guarantees that composing
-- | independent solutions yields a globally valid solution.
composeSolutions :: Array ViewportSolution -> Array LayoutResult
composeSolutions viewportSolutions =
  -- Solutions from different viewports don't overlap
  -- Simply concatenate and sort by element ID
  sortByElementId (Array.concatMap _.results viewportSolutions)
  where
    sortByElementId :: Array LayoutResult -> Array LayoutResult
    sortByElementId = Array.sortBy (\a b -> compare a.elementId b.elementId)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // parallel solve interface
-- ═════════════════════════════════════════════════════════════════════════════

-- | A decomposed layout ready for parallel solving.
type DecomposedLayout =
  { subproblems :: Array ViewportSubproblem
  , partition :: ViewportPartition
  }

-- | A single viewport's layout problem.
type ViewportSubproblem =
  { viewportId :: ViewportId
  , elements :: Array LayoutElement
  , graph :: ConstraintGraph
  , container :: ContainerSpec
  }

-- | Extract independent subproblems from a decomposable layout.
-- |
-- | Precondition: `isDecomposable graph partition = true`
-- |
-- | ## Lean Correspondence
-- |
-- | This implements extraction of `viewportSubgraph` for each viewport.
extractSubproblems 
  :: ConstraintGraph 
  -> ViewportPartition 
  -> Map ViewportId ContainerSpec 
  -> Map ViewportId (Array LayoutElement)
  -> Array ViewportSubproblem
extractSubproblems graph partition containers elementsByViewport =
  let
    subgraphs = extractSubgraphs graph partition
    p = unwrapPartition partition
    viewportIds = Set.toUnfoldable p.viewports :: Array ViewportId
  in
    Array.mapMaybe (buildSubproblem subgraphs containers elementsByViewport) viewportIds
  where
    buildSubproblem 
      :: Map ViewportId ConstraintGraph 
      -> Map ViewportId ContainerSpec 
      -> Map ViewportId (Array LayoutElement)
      -> ViewportId 
      -> Maybe ViewportSubproblem
    buildSubproblem subgraphs conts elems viewId = do
      subgraph <- Map.lookup viewId subgraphs
      container <- Map.lookup viewId conts
      elements <- Map.lookup viewId elems
      Just
        { viewportId: viewId
        , elements
        , graph: subgraph
        , container
        }

-- | Solve a decomposed layout in parallel.
-- |
-- | Each viewport is solved independently, then solutions are composed.
-- |
-- | ## Lean Correspondence
-- |
-- | The theorem `parallel_solve_correct` guarantees correctness.
solveDecomposed 
  :: (ViewportSubproblem -> Array LayoutResult) 
  -> DecomposedLayout 
  -> Array LayoutResult
solveDecomposed solver decomposed =
  let
    viewportSolutions = map (\sub -> 
      { viewportId: sub.viewportId
      , results: solver sub
      }) decomposed.subproblems
  in
    composeSolutions viewportSolutions
