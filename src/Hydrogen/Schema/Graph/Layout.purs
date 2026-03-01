-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // graph // layout
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Graph Layout — Spatial arrangement algorithms for hierarchical data.
-- |
-- | ## Design Philosophy
-- |
-- | Layout is pure geometry. Given a tree structure and constraints, a layout
-- | algorithm produces (x, y) positions for every node. No rendering — just math.
-- |
-- | ## Layout Categories
-- |
-- | **Linear**: IndentedList, Outline
-- | **Radial**: Radial, Sunburst, CirclePack
-- | **Space-Filling**: Treemap, Icicle, Partition
-- | **Node-Link**: Tidy, Dendrogram, Cluster, OrgChart
-- | **Force-Directed**: Force, Hierarchical Force
-- | **Custom**: Via layout function
-- |
-- | ## Algorithm Sources
-- |
-- | Many algorithms based on academic work:
-- | - Reingold-Tilford (1981): Tidy tree drawing
-- | - Walker (1990): Improving on R-T
-- | - Buchheim (2002): Linear time implementation
-- | - Shneiderman (1992): Treemaps
-- |
-- | ## Submodules
-- |
-- | - Layout.Types: Core types (LayoutAlgorithm, LayoutDirection, etc.)
-- | - Layout.Spacing: Spacing configuration
-- | - Layout.Constraints: Bounds, constraints, and node positions
-- | - Layout.Params: Algorithm-specific parameters
-- | - Layout.Config: Complete layout configuration compound

module Hydrogen.Schema.Graph.Layout
  ( module Types
  , module Spacing
  , module Constraints
  , module Params
  , module Config
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Graph.Layout.Types as Types
import Hydrogen.Schema.Graph.Layout.Spacing as Spacing
import Hydrogen.Schema.Graph.Layout.Constraints as Constraints
import Hydrogen.Schema.Graph.Layout.Params as Params
import Hydrogen.Schema.Graph.Layout.Config as Config
