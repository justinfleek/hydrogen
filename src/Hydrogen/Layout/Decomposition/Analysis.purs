-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // layout // decomposition // analysis
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Independence checking and decomposability analysis.
-- |
-- | This module implements the core decomposition analysis:
-- | - Check if constraints cross viewport boundaries
-- | - Determine if layout can be solved in parallel
-- | - Extract blocking edges that prevent decomposition
-- |
-- | ## Lean Correspondence
-- |
-- | Implements `IsDecomposable g p` from the proofs.
-- |
-- | ## Complexity
-- |
-- | Independence check: O(|E|) where E = constraint edges

module Hydrogen.Layout.Decomposition.Analysis
  ( -- * Independence Checking
    DecompositionResult(..)
  , checkDecomposable
  , isDecomposable
  , interViewportEdges
  , blockingEdges
  , isCrossViewport
  
  -- * Subgraph Extraction
  , viewportSubgraph
  , extractSubgraphs
  , computeViewportSizes
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , ($)
  , (&&)
  , (<>)
  , (/=)
  )

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Map (Map)
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
  , mkConstraintGraph
  , graphEdges
  )
import Hydrogen.Layout.Decomposition.Partition
  ( ViewportPartition
  , viewportOf
  , elementsIn
  , viewportSize
  , unwrapPartition
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // independence checking
-- ═════════════════════════════════════════════════════════════════════════════

-- | Result of checking layout decomposability.
-- |
-- | ## Lean Correspondence
-- |
-- | - `Decomposable` corresponds to `IsDecomposable g p` being true
-- | - `NotDecomposable` provides witness edges from `interViewportEdges`
data DecompositionResult
  = Decomposable
      { subgraphs :: Map ViewportId ConstraintGraph
      , viewportSizes :: Map ViewportId Int
      }
  | NotDecomposable
      { blockingEdges :: Array ConstraintEdge
      , minCutSize :: Int
      }

derive instance eqDecompositionResult :: Eq DecompositionResult

instance showDecompositionResult :: Show DecompositionResult where
  show (Decomposable d) = 
    "Decomposable{viewports=" <> show (Map.size d.subgraphs) <> "}"
  show (NotDecomposable n) = 
    "NotDecomposable{blocking=" <> show (Array.length n.blockingEdges) <> "}"

-- | Check if an edge crosses viewport boundaries.
-- |
-- | ## Lean Correspondence
-- |
-- | This implements `isCrossViewport` from the proofs.
isCrossViewport :: ViewportPartition -> ConstraintEdge -> Boolean
isCrossViewport partition edge =
  let
    srcViewport = viewportOf partition edge.source
    tgtViewport = viewportOf partition edge.target
  in
    srcViewport /= tgtViewport

-- | Find all edges that cross viewport boundaries.
-- |
-- | Complexity: O(|E|)
-- |
-- | ## Lean Correspondence
-- |
-- | This implements `interViewportEdges` from the proofs.
interViewportEdges :: ConstraintGraph -> ViewportPartition -> Array ConstraintEdge
interViewportEdges graph partition =
  Array.filter (isCrossViewport partition) (graphEdges graph)

-- | Alias for inter-viewport edges (witness of non-decomposability).
blockingEdges :: ConstraintGraph -> ViewportPartition -> Array ConstraintEdge
blockingEdges = interViewportEdges

-- | Check if a layout is decomposable by viewport.
-- |
-- | Complexity: O(|E|)
-- |
-- | ## Lean Correspondence
-- |
-- | This implements the decision procedure for `IsDecomposable g p`.
-- | The result includes subgraphs for parallel solving if decomposable.
-- |
-- | ## Theorem Reference
-- |
-- | `layout_decomposable`: If this returns `Decomposable`, then for any
-- | two distinct viewports v1 and v2, no constraint connects them.
checkDecomposable :: ConstraintGraph -> ViewportPartition -> DecompositionResult
checkDecomposable graph partition =
  let crossEdges = interViewportEdges graph partition
  in if Array.null crossEdges
     then Decomposable
       { subgraphs: extractSubgraphs graph partition
       , viewportSizes: computeViewportSizes partition
       }
     else NotDecomposable
       { blockingEdges: crossEdges
       , minCutSize: Array.length crossEdges
       }

-- | Simple predicate for decomposability.
isDecomposable :: ConstraintGraph -> ViewportPartition -> Boolean
isDecomposable graph partition =
  Array.null (interViewportEdges graph partition)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // subgraph extraction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the induced subgraph for a single viewport.
-- |
-- | ## Lean Correspondence
-- |
-- | This implements `viewportSubgraph` from the proofs.
-- | The theorem `constraint_graph_independent` guarantees that
-- | subgraphs for different viewports share no edges.
viewportSubgraph :: ConstraintGraph -> ViewportPartition -> ViewportId -> ConstraintGraph
viewportSubgraph graph partition viewId =
  let
    elements = elementsIn partition viewId
    edges = Array.filter (edgeInViewport elements) (graphEdges graph)
    nodes = Set.toUnfoldable elements :: Array ElementId
  in
    mkConstraintGraph nodes edges
  where
    edgeInViewport :: Set ElementId -> ConstraintEdge -> Boolean
    edgeInViewport elems edge =
      Set.member edge.source elems && Set.member edge.target elems

-- | Extract subgraphs for all viewports.
-- |
-- | ## Lean Correspondence
-- |
-- | The theorem `subgraph_edges_partition` guarantees that edges
-- | partition cleanly when the layout is decomposable.
extractSubgraphs :: ConstraintGraph -> ViewportPartition -> Map ViewportId ConstraintGraph
extractSubgraphs graph partition =
  let p = unwrapPartition partition
  in foldl (\m viewId -> Map.insert viewId (viewportSubgraph graph partition viewId) m) 
           Map.empty 
           (Set.toUnfoldable p.viewports :: Array ViewportId)

-- | Compute sizes for all viewports.
computeViewportSizes :: ViewportPartition -> Map ViewportId Int
computeViewportSizes partition =
  let p = unwrapPartition partition
  in foldl (\m viewId -> Map.insert viewId (viewportSize partition viewId) m)
           Map.empty
           (Set.toUnfoldable p.viewports :: Array ViewportId)
