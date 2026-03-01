-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // graph // layout // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Layout Types — Core type definitions for layout algorithms.
-- |
-- | ## Contents
-- |
-- | - LayoutAlgorithm: Enumeration of all layout algorithms
-- | - LayoutDirection: Horizontal vs Vertical
-- | - LayoutOrientation: Flow direction (TopDown, BottomUp, etc.)
-- | - NodeSizing: How node dimensions are determined
-- |
-- | ## Dependencies
-- |
-- | - Prelude

module Hydrogen.Schema.Graph.Layout.Types
  ( -- * Layout Algorithm
    LayoutAlgorithm(..)
  , isLinearLayout
  , isRadialLayout
  , isSpaceFillingLayout
  , isNodeLinkLayout
  , isForceLayout
  
  -- * Layout Direction
  , LayoutDirection(..)
  , isHorizontal
  , isVertical
  , flipDirection
  
  -- * Layout Orientation  
  , LayoutOrientation(..)
  , isTopDown
  , isBottomUp
  , isLeftRight
  , isRightLeft
  
  -- * Node Sizing
  , NodeSizing(..)
  , isFixedSize
  , isFitContent
  , isProportional
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
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // layout algorithm
-- ═════════════════════════════════════════════════════════════════════════════

-- | Layout algorithm determines spatial arrangement
data LayoutAlgorithm
  -- Linear layouts (1D with nesting)
  = IndentedList       -- ^ Traditional file explorer style
  | Outline            -- ^ Outline/bullet list style
  
  -- Radial layouts (polar coordinates)
  | Radial             -- ^ Nodes on concentric circles
  | Sunburst           -- ^ Arcs representing hierarchy
  | CirclePack         -- ^ Nested circles
  
  -- Space-filling layouts (area = value)
  | Treemap            -- ^ Nested rectangles
  | Icicle             -- ^ Vertical/horizontal partitions
  | Partition          -- ^ Generic partition layout
  
  -- Node-link layouts (nodes + edges)
  | Tidy               -- ^ Aesthetic tree (Reingold-Tilford)
  | Cluster            -- ^ Leaves at same level
  | Dendrogram         -- ^ With branch lengths
  | OrgChart           -- ^ Organizational hierarchy
  | MindMap            -- ^ Central node radiating
  
  -- Force-directed layouts
  | Force              -- ^ Physics simulation
  | HierarchicalForce  -- ^ Force with hierarchy constraints

derive instance eqLayoutAlgorithm :: Eq LayoutAlgorithm
derive instance ordLayoutAlgorithm :: Ord LayoutAlgorithm

instance showLayoutAlgorithm :: Show LayoutAlgorithm where
  show IndentedList = "indented-list"
  show Outline = "outline"
  show Radial = "radial"
  show Sunburst = "sunburst"
  show CirclePack = "circle-pack"
  show Treemap = "treemap"
  show Icicle = "icicle"
  show Partition = "partition"
  show Tidy = "tidy"
  show Cluster = "cluster"
  show Dendrogram = "dendrogram"
  show OrgChart = "org-chart"
  show MindMap = "mind-map"
  show Force = "force"
  show HierarchicalForce = "hierarchical-force"

-- | Is this a linear (list-based) layout?
isLinearLayout :: LayoutAlgorithm -> Boolean
isLinearLayout IndentedList = true
isLinearLayout Outline = true
isLinearLayout _ = false

-- | Is this a radial (polar) layout?
isRadialLayout :: LayoutAlgorithm -> Boolean
isRadialLayout Radial = true
isRadialLayout Sunburst = true
isRadialLayout CirclePack = true
isRadialLayout _ = false

-- | Is this a space-filling layout?
isSpaceFillingLayout :: LayoutAlgorithm -> Boolean
isSpaceFillingLayout Treemap = true
isSpaceFillingLayout Icicle = true
isSpaceFillingLayout Partition = true
isSpaceFillingLayout _ = false

-- | Is this a node-link layout?
isNodeLinkLayout :: LayoutAlgorithm -> Boolean
isNodeLinkLayout Tidy = true
isNodeLinkLayout Cluster = true
isNodeLinkLayout Dendrogram = true
isNodeLinkLayout OrgChart = true
isNodeLinkLayout MindMap = true
isNodeLinkLayout _ = false

-- | Is this a force-directed layout?
isForceLayout :: LayoutAlgorithm -> Boolean
isForceLayout Force = true
isForceLayout HierarchicalForce = true
isForceLayout _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // layout direction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Primary axis direction for linear layouts
data LayoutDirection
  = Horizontal  -- ^ Nodes arranged left-to-right
  | Vertical    -- ^ Nodes arranged top-to-bottom

derive instance eqLayoutDirection :: Eq LayoutDirection
derive instance ordLayoutDirection :: Ord LayoutDirection

instance showLayoutDirection :: Show LayoutDirection where
  show Horizontal = "horizontal"
  show Vertical = "vertical"

isHorizontal :: LayoutDirection -> Boolean
isHorizontal Horizontal = true
isHorizontal _ = false

isVertical :: LayoutDirection -> Boolean
isVertical Vertical = true
isVertical _ = false

flipDirection :: LayoutDirection -> LayoutDirection
flipDirection Horizontal = Vertical
flipDirection Vertical = Horizontal

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // layout orientation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Flow direction for hierarchical layouts
data LayoutOrientation
  = TopDown    -- ^ Root at top, children below
  | BottomUp   -- ^ Root at bottom, children above
  | LeftRight  -- ^ Root at left, children to right
  | RightLeft  -- ^ Root at right, children to left

derive instance eqLayoutOrientation :: Eq LayoutOrientation
derive instance ordLayoutOrientation :: Ord LayoutOrientation

instance showLayoutOrientation :: Show LayoutOrientation where
  show TopDown = "top-down"
  show BottomUp = "bottom-up"
  show LeftRight = "left-right"
  show RightLeft = "right-left"

isTopDown :: LayoutOrientation -> Boolean
isTopDown TopDown = true
isTopDown _ = false

isBottomUp :: LayoutOrientation -> Boolean
isBottomUp BottomUp = true
isBottomUp _ = false

isLeftRight :: LayoutOrientation -> Boolean
isLeftRight LeftRight = true
isLeftRight _ = false

isRightLeft :: LayoutOrientation -> Boolean
isRightLeft RightLeft = true
isRightLeft _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // node sizing
-- ═════════════════════════════════════════════════════════════════════════════

-- | How node sizes are determined
data NodeSizing
  = FixedSize Number Number          -- ^ Fixed width × height
  | FitContent Number Number         -- ^ Fit to content with min size
  | Proportional                     -- ^ Size proportional to value
  | AspectRatio Number               -- ^ Maintain aspect ratio

derive instance eqNodeSizing :: Eq NodeSizing

instance showNodeSizing :: Show NodeSizing where
  show (FixedSize w h) = "fixed(" <> show w <> "×" <> show h <> ")"
  show (FitContent minW minH) = "fit-content(" <> show minW <> "," <> show minH <> ")"
  show Proportional = "proportional"
  show (AspectRatio r) = "aspect-ratio(" <> show r <> ")"

isFixedSize :: NodeSizing -> Boolean
isFixedSize (FixedSize _ _) = true
isFixedSize _ = false

isFitContent :: NodeSizing -> Boolean
isFitContent (FitContent _ _) = true
isFitContent _ = false

isProportional :: NodeSizing -> Boolean
isProportional Proportional = true
isProportional _ = false
