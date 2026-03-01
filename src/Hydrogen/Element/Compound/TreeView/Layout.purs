-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // element // treeview // layout
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TreeView Layout — Leader module re-exporting all layout functionality.
-- |
-- | ## Design Philosophy
-- |
-- | Layout is pure computation. Given a tree structure and layout configuration,
-- | produce (x, y, width, height) for every node. No rendering — just positions.
-- |
-- | ## Layout Algorithms
-- |
-- | **Linear (1D)**:
-- | - IndentedList: Traditional file explorer (vertical list with indentation)
-- | - Outline: Outline/bullet style
-- |
-- | **Radial (Polar)**:
-- | - Radial: Nodes on concentric circles
-- | - Sunburst: Arcs representing hierarchy
-- | - CirclePack: Nested circles
-- |
-- | **Space-Filling (Area = Value)**:
-- | - Treemap: Nested rectangles
-- | - Icicle: Vertical/horizontal partitions
-- |
-- | **Node-Link (Nodes + Edges)**:
-- | - Tidy: Aesthetic tree (Reingold-Tilford)
-- | - Dendrogram: With branch lengths
-- | - OrgChart: Organizational hierarchy
-- | - MindMap: Central node radiating
-- |
-- | ## Module Structure
-- |
-- | - Layout.Core: Types, dispatch, helpers
-- | - Layout.Linear: Indented list layouts
-- | - Layout.Radial: Circular/polar layouts
-- | - Layout.SpaceFilling: Treemap/icicle layouts
-- | - Layout.NodeLink: Tidy tree/org chart layouts
-- | - Layout.Queries: Position queries and transformations

module Hydrogen.Element.Compound.TreeView.Layout
  ( -- * Layout Result (from Core)
    module Core
    
  -- * Indented List Layout (from Linear)
  , module Linear
  
  -- * Radial Layouts (from Radial)
  , module Radial
  
  -- * Space-Filling Layouts (from SpaceFilling)
  , module SpaceFilling
  
  -- * Node-Link Layouts (from NodeLink)
  , module NodeLink
  
  -- * Position Queries (from Queries)
  , module Queries
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Element.Compound.TreeView.Layout.Core
  ( LayoutResult
  , layoutResult
  , emptyLayout
  , nodePosition
  , nodePositions
  , contentBounds
  , layoutNodeCount
  , computeLayout
  , recomputeLayout
  , nodeSizeWidth
  , nodeSizeHeight
  , boundsFromConstraints
  ) as Core

import Hydrogen.Element.Compound.TreeView.Layout.Linear
  ( layoutIndentedList
  ) as Linear

import Hydrogen.Element.Compound.TreeView.Layout.Radial
  ( layoutRadial
  , layoutSunburst
  , layoutCirclePack
  , cos
  , sin
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

import Hydrogen.Element.Compound.TreeView.Layout.Queries
  ( positionOf
  , childPositions
  , boundingBox
  , centerOf
  , translateLayout
  , scaleLayout
  , rotateLayout
  ) as Queries
