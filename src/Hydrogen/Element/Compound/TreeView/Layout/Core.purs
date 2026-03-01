-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // treeview // layout // core
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TreeView Layout Core — Types, dispatch, and shared utilities.
-- |
-- | ## Purpose
-- |
-- | Core infrastructure for tree layout computation:
-- | - LayoutResult type for holding computed positions
-- | - computeLayout dispatcher to select algorithm
-- | - Shared helper functions for sizing and bounds
-- |
-- | ## Dependencies
-- |
-- | - TreeView.Types (NodeId, Depth)
-- | - TreeView.Node (Tree, traversal)
-- | - TreeView.State (ExpandedState)
-- | - Schema.Graph.Layout (LayoutConfig, NodePosition)

module Hydrogen.Element.Compound.TreeView.Layout.Core
  ( -- * Layout Result
    LayoutResult
  , layoutResult
  , emptyLayout
  , nodePosition
  , nodePositions
  , contentBounds
  , layoutNodeCount
  
  -- * Layout Computation
  , computeLayout
  , recomputeLayout
  
  -- * Helpers (exported for use by algorithm modules)
  , nodeSizeWidth
  , nodeSizeHeight
  , boundsFromConstraints
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (*)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Map (Map)
import Data.Map as Map

import Hydrogen.Element.Compound.TreeView.Node
  ( Tree
  )

import Hydrogen.Element.Compound.TreeView.State
  ( ExpandedState
  )

import Hydrogen.Schema.Graph.Layout
  ( LayoutConfig
  , LayoutAlgorithm(IndentedList, Outline, Radial, Sunburst, CirclePack, Treemap, Icicle, Partition, Tidy, Cluster, Dendrogram, OrgChart, MindMap, Force, HierarchicalForce)
  , NodeSizing(FixedSize, FitContent, Proportional, AspectRatio)
  , NodePosition
  ) as Schema

import Hydrogen.Schema.Graph.Viewport
  ( ViewportBounds
  , viewportBounds
  ) as Viewport

import Hydrogen.Element.Compound.TreeView.Types
  ( NodeId
  )

-- Layout algorithm imports (forward references resolved by leader module)
import Hydrogen.Element.Compound.TreeView.Layout.Linear
  ( layoutIndentedList
  ) as Linear

import Hydrogen.Element.Compound.TreeView.Layout.Radial
  ( layoutRadial
  , layoutSunburst
  , layoutCirclePack
  ) as Radial

import Hydrogen.Element.Compound.TreeView.Layout.SpaceFilling
  ( layoutTreemap
  , layoutIcicle
  ) as SpaceFilling

import Hydrogen.Element.Compound.TreeView.Layout.NodeLink
  ( layoutTidy
  , layoutDendrogram
  , layoutOrgChart
  , layoutMindMap
  ) as NodeLink

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // layout result
-- ═════════════════════════════════════════════════════════════════════════════

-- | Result of layout computation
-- |
-- | Contains computed positions for all visible nodes plus metadata
-- | about the layout bounds.
type LayoutResult =
  { positions :: Map NodeId Schema.NodePosition
  , bounds :: Viewport.ViewportBounds
  , nodeCount :: Int
  }

-- | Create a layout result
layoutResult :: 
  Map NodeId Schema.NodePosition -> 
  Viewport.ViewportBounds -> 
  Int -> 
  LayoutResult
layoutResult positions bounds nodeCount =
  { positions, bounds, nodeCount }

-- | Empty layout (no nodes)
emptyLayout :: LayoutResult
emptyLayout =
  { positions: Map.empty
  , bounds: Viewport.viewportBounds 0.0 0.0 0.0 0.0
  , nodeCount: 0
  }

-- | Get position for a specific node
nodePosition :: NodeId -> LayoutResult -> Maybe Schema.NodePosition
nodePosition nid layout = Map.lookup nid layout.positions

-- | Get all node positions
nodePositions :: LayoutResult -> Map NodeId Schema.NodePosition
nodePositions layout = layout.positions

-- | Get content bounds
contentBounds :: LayoutResult -> Viewport.ViewportBounds
contentBounds layout = layout.bounds

-- | Get node count
layoutNodeCount :: LayoutResult -> Int
layoutNodeCount layout = layout.nodeCount

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // layout computation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute layout for a tree with given configuration
-- |
-- | Dispatches to the appropriate layout algorithm based on config.
computeLayout :: 
  Schema.LayoutConfig -> 
  Tree -> 
  ExpandedState -> 
  LayoutResult
computeLayout config tree expanded =
  case config.algorithm of
    Schema.IndentedList -> Linear.layoutIndentedList config tree expanded
    Schema.Outline -> Linear.layoutIndentedList config tree expanded
    Schema.Radial -> Radial.layoutRadial config tree expanded
    Schema.Sunburst -> Radial.layoutSunburst config tree expanded
    Schema.CirclePack -> Radial.layoutCirclePack config tree expanded
    Schema.Treemap -> SpaceFilling.layoutTreemap config tree expanded
    Schema.Icicle -> SpaceFilling.layoutIcicle config tree expanded
    Schema.Partition -> SpaceFilling.layoutIcicle config tree expanded
    Schema.Tidy -> NodeLink.layoutTidy config tree expanded
    Schema.Cluster -> NodeLink.layoutDendrogram config tree expanded
    Schema.Dendrogram -> NodeLink.layoutDendrogram config tree expanded
    Schema.OrgChart -> NodeLink.layoutOrgChart config tree expanded
    Schema.MindMap -> NodeLink.layoutMindMap config tree expanded
    Schema.Force -> NodeLink.layoutTidy config tree expanded
    Schema.HierarchicalForce -> NodeLink.layoutTidy config tree expanded

-- | Recompute layout (alias for computeLayout)
recomputeLayout :: 
  Schema.LayoutConfig -> 
  Tree -> 
  ExpandedState -> 
  LayoutResult
recomputeLayout = computeLayout

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract node width from sizing config
nodeSizeWidth :: Schema.NodeSizing -> Number
nodeSizeWidth (Schema.FixedSize w _) = w
nodeSizeWidth (Schema.FitContent minW _) = minW
nodeSizeWidth Schema.Proportional = 100.0
nodeSizeWidth (Schema.AspectRatio r) = 100.0 * r

-- | Extract node height from sizing config
nodeSizeHeight :: Schema.NodeSizing -> Number
nodeSizeHeight (Schema.FixedSize _ h) = h
nodeSizeHeight (Schema.FitContent _ minH) = minH
nodeSizeHeight Schema.Proportional = 100.0
nodeSizeHeight (Schema.AspectRatio _) = 100.0

-- | Get bounds from layout constraints
boundsFromConstraints :: Schema.LayoutConfig -> Maybe Viewport.ViewportBounds
boundsFromConstraints config =
  let
    width = config.constraints.bounds.width
    height = config.constraints.bounds.height
  in
    case width, height of
      Just w, Just h -> Just (Viewport.viewportBounds 0.0 0.0 w h)
      _, _ -> Nothing
