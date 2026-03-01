-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // treeview // layout // linear
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TreeView Linear Layout — Indented list and outline styles.
-- |
-- | ## Design Philosophy
-- |
-- | Linear layouts arrange nodes in a vertical list with indentation
-- | representing depth. This is the classic file explorer pattern.
-- |
-- | ## Algorithms
-- |
-- | - IndentedList: Traditional file explorer (vertical list with indentation)
-- | - Outline: Same as indented list, used for outline/bullet style
-- |
-- | ## Dependencies
-- |
-- | - TreeView.Types (NodeId, Depth)
-- | - TreeView.Node (Tree, TreeNode, traversal)
-- | - TreeView.State (ExpandedState)
-- | - Schema.Graph.Layout (LayoutConfig, NodePosition)

module Hydrogen.Element.Compound.TreeView.Layout.Linear
  ( -- * Indented List Layout
    layoutIndentedList
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (+)
  , (*)
  , (>)
  , (&&)
  , max
  )

import Data.Array as Array
import Data.Map (Map)
import Data.Map as Map
import Data.Foldable (foldl)
import Data.Int (toNumber) as Int

import Hydrogen.Element.Compound.TreeView.Types
  ( NodeId
  , unwrapDepth
  )

import Hydrogen.Element.Compound.TreeView.Node
  ( Tree
  , TreeNode
  , nodeId
  , nodeChildren
  , rootNodes
  , getNode
  , nodeDepth
  )

import Hydrogen.Element.Compound.TreeView.State
  ( ExpandedState
  , isExpanded
  )

import Hydrogen.Schema.Graph.Layout
  ( LayoutConfig
  , NodeSizing(FixedSize, FitContent, Proportional, AspectRatio)
  , NodePosition
  , siblingGap
  , levelGap
  , nodePosition
  ) as Schema

import Hydrogen.Schema.Graph.Viewport
  ( ViewportBounds
  , viewportBounds
  ) as Viewport

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // layout result
-- ═════════════════════════════════════════════════════════════════════════════

-- | Result of layout computation
-- |
-- | Duplicated here to avoid circular imports. The leader module
-- | re-exports from Core.
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

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // indented list layout
-- ═════════════════════════════════════════════════════════════════════════════

-- | Layout for traditional file explorer style
-- |
-- | Nodes arranged vertically with indentation per depth level.
-- | Only expanded nodes and their visible children are laid out.
layoutIndentedList :: 
  Schema.LayoutConfig -> 
  Tree -> 
  ExpandedState -> 
  LayoutResult
layoutIndentedList config tree expanded =
  let
    roots = rootNodes tree
    
    initialState = { y: 0.0, positions: Map.empty, maxX: 0.0 }
    
    finalState = foldl (layoutIndentedNode config tree expanded) initialState roots
    
    bounds = Viewport.viewportBounds 
      0.0 
      0.0 
      finalState.maxX 
      finalState.y
  in
    layoutResult finalState.positions bounds (Map.size finalState.positions)

-- | Layout state for indented list
type IndentedState =
  { y :: Number
  , positions :: Map NodeId Schema.NodePosition
  , maxX :: Number
  }

-- | Layout a single node and its children in indented list style
layoutIndentedNode ::
  Schema.LayoutConfig ->
  Tree ->
  ExpandedState ->
  IndentedState ->
  TreeNode ->
  IndentedState
layoutIndentedNode config tree expanded state node =
  let
    nid = nodeId node
    depth = nodeDepth nid tree
    spacing = config.spacing
    nodeHeight = nodeSizeHeight config.sizing
    nodeWidth = nodeSizeWidth config.sizing
    
    indentPerLevel = Schema.levelGap spacing
    x = Int.toNumber (unwrapDepth depth) * indentPerLevel
    
    pos = Schema.nodePosition x state.y nodeWidth nodeHeight
    
    newPositions = Map.insert nid pos state.positions
    newY = state.y + nodeHeight + Schema.siblingGap spacing
    newMaxX = max state.maxX (x + nodeWidth)
    
    stateAfterNode = 
      { y: newY
      , positions: newPositions
      , maxX: newMaxX
      }
    
    children = nodeChildren node
    isExp = isExpanded nid expanded
  in
    if isExp && Array.length children > 0
      then
        let
          childNodes = Array.mapMaybe (\cid -> getNode cid tree) children
        in
          foldl (layoutIndentedNode config tree expanded) stateAfterNode childNodes
      else
        stateAfterNode

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
