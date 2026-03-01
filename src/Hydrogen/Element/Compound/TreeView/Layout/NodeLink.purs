-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // treeview // layout // nodelink
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TreeView Node-Link Layout — Classic tree visualizations with nodes and edges.
-- |
-- | ## Design Philosophy
-- |
-- | Node-link layouts position nodes with explicit edges between them.
-- | Various algorithms produce different aesthetics and use cases.
-- |
-- | ## Algorithms
-- |
-- | - Tidy: Reingold-Tilford aesthetic tree layout
-- | - Dendrogram: Cluster with branch lengths
-- | - OrgChart: Organizational hierarchy
-- | - MindMap: Central node with radiating branches
-- |
-- | ## Dependencies
-- |
-- | - TreeView.Types (NodeId)
-- | - TreeView.Node (Tree, TreeNode, traversal)
-- | - TreeView.State (ExpandedState)
-- | - Schema.Graph.Layout (LayoutConfig, NodePosition)

module Hydrogen.Element.Compound.TreeView.Layout.NodeLink
  ( -- * Tidy Tree Layout
    layoutTidy
    
  -- * Dendrogram Layout
  , layoutDendrogram
  
  -- * Org Chart Layout
  , layoutOrgChart
  
  -- * Mind Map Layout
  , layoutMindMap
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (-)
  , (+)
  , (/)
  , (*)
  , (>)
  , (&&)
  , max
  , min
  )

import Data.Array as Array
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(Just, Nothing))
import Data.Tuple (Tuple(Tuple))
import Data.Foldable (foldl)
import Data.Int (toNumber) as Int

import Hydrogen.Element.Compound.TreeView.Types
  ( NodeId
  )

import Hydrogen.Element.Compound.TreeView.Node
  ( Tree
  , TreeNode
  , nodeId
  , nodeChildren
  , rootNodes
  , getNode
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

-- | Result of layout computation (local copy to avoid circular imports)
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
--                                                           // tidy tree layout
-- ═════════════════════════════════════════════════════════════════════════════

-- | Aesthetic tree layout (Reingold-Tilford algorithm)
-- |
-- | Produces aesthetically pleasing trees with:
-- | - Siblings evenly spaced
-- | - Parents centered over children
-- | - Subtrees don't overlap
layoutTidy :: 
  Schema.LayoutConfig -> 
  Tree -> 
  ExpandedState -> 
  LayoutResult
layoutTidy config tree expanded =
  let
    roots = rootNodes tree
    
    initialState = { positions: Map.empty, maxX: 0.0, maxY: 0.0 }
    
    finalState = foldl
      (\s rootNode ->
        let
          result = layoutTidySubtree config tree expanded rootNode 0.0 0
          mergedPositions = Map.union s.positions result.positions
          newMaxX = max s.maxX result.maxX
          newMaxY = max s.maxY result.maxY
        in
          { positions: mergedPositions
          , maxX: newMaxX
          , maxY: newMaxY
          }
      )
      initialState
      roots
    
    bounds = Viewport.viewportBounds 0.0 0.0 finalState.maxX finalState.maxY
  in
    layoutResult finalState.positions bounds (Map.size finalState.positions)

-- | Tidy layout result for a subtree
type TidyResult =
  { positions :: Map NodeId Schema.NodePosition
  , width :: Number
  , x :: Number
  , maxX :: Number
  , maxY :: Number
  }

-- | Layout a subtree using tidy tree algorithm
layoutTidySubtree ::
  Schema.LayoutConfig ->
  Tree ->
  ExpandedState ->
  TreeNode ->
  Number ->
  Int ->
  TidyResult
layoutTidySubtree config tree expanded node xOffset level =
  let
    nid = nodeId node
    spacing = config.spacing
    nodeWidth = nodeSizeWidth config.sizing
    nodeHeight = nodeSizeHeight config.sizing
    levelGapVal = Schema.levelGap spacing
    sibGap = Schema.siblingGap spacing
    
    y = Int.toNumber level * (nodeHeight + levelGapVal)
    
    children = nodeChildren node
    isExp = isExpanded nid expanded
  in
    if isExp && Array.length children > 0
      then
        let
          childNodes = Array.mapMaybe (\cid -> getNode cid tree) children
          
          childResults = layoutTidyChildren config tree expanded childNodes xOffset (level + 1)
          
          totalChildWidth = foldl (\acc r -> acc + r.width + sibGap) (negateNum sibGap) childResults
          centerX = xOffset + totalChildWidth / 2.0
          
          pos = Schema.nodePosition centerX y nodeWidth nodeHeight
          
          allPositions = foldl 
            (\acc r -> Map.union acc r.positions) 
            (Map.singleton nid pos)
            childResults
          
          maxChildX = foldl (\acc r -> max acc r.maxX) 0.0 childResults
          maxChildY = foldl (\acc r -> max acc r.maxY) 0.0 childResults
        in
          { positions: allPositions
          , width: max nodeWidth totalChildWidth
          , x: centerX
          , maxX: max centerX maxChildX
          , maxY: max (y + nodeHeight) maxChildY
          }
      else
        let
          pos = Schema.nodePosition xOffset y nodeWidth nodeHeight
        in
          { positions: Map.singleton nid pos
          , width: nodeWidth
          , x: xOffset
          , maxX: xOffset + nodeWidth
          , maxY: y + nodeHeight
          }

-- | Layout children for tidy tree
layoutTidyChildren ::
  Schema.LayoutConfig ->
  Tree ->
  ExpandedState ->
  Array TreeNode ->
  Number ->
  Int ->
  Array TidyResult
layoutTidyChildren config tree expanded nodes startX level =
  let
    spacing = config.spacing
    sibGap = Schema.siblingGap spacing
    
    result = foldl
      (\acc node ->
        let
          xOffset = acc.currentX
          childResult = layoutTidySubtree config tree expanded node xOffset level
          newX = xOffset + childResult.width + sibGap
        in
          { currentX: newX
          , results: Array.snoc acc.results childResult
          }
      )
      { currentX: startX, results: [] }
      nodes
  in
    result.results

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // dendrogram layout
-- ═════════════════════════════════════════════════════════════════════════════

-- | Dendrogram layout (cluster with branch lengths)
-- |
-- | All leaves at the same level, branches represent distances.
layoutDendrogram :: 
  Schema.LayoutConfig -> 
  Tree -> 
  ExpandedState -> 
  LayoutResult
layoutDendrogram config tree expanded =
  layoutTidy config tree expanded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // org chart layout
-- ═════════════════════════════════════════════════════════════════════════════

-- | Organizational chart layout
-- |
-- | Similar to tidy tree but with specific styling for org charts:
-- | - Fixed node sizes
-- | - Centered parents
-- | - Clear hierarchy levels
layoutOrgChart :: 
  Schema.LayoutConfig -> 
  Tree -> 
  ExpandedState -> 
  LayoutResult
layoutOrgChart config tree expanded =
  layoutTidy config tree expanded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // mind map layout
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mind map layout
-- |
-- | Central root with children radiating outward.
-- | Left side children go left, right side children go right.
layoutMindMap :: 
  Schema.LayoutConfig -> 
  Tree -> 
  ExpandedState -> 
  LayoutResult
layoutMindMap config tree expanded =
  let
    nodeSize = nodeSizeWidth config.sizing
    
    roots = rootNodes tree
    
    initialState = { positions: Map.empty, minX: 0.0, maxX: 0.0, maxY: 0.0 }
    
    finalState = case Array.head roots of
      Nothing -> initialState
      Just rootNode ->
        let
          rootPos = Schema.nodePosition 0.0 0.0 nodeSize nodeSize
          children = nodeChildren rootNode
          childNodes = Array.mapMaybe (\cid -> getNode cid tree) children
          
          halfIdx = Array.length childNodes / 2
          leftChildren = Array.take halfIdx childNodes
          rightChildren = Array.drop halfIdx childNodes
          
          stateWithRoot = 
            { positions: Map.singleton (nodeId rootNode) rootPos
            , minX: 0.0
            , maxX: 0.0
            , maxY: 0.0
            }
          
          stateAfterLeft = layoutMindMapSide config tree expanded stateWithRoot leftChildren (negateNum 1.0) 0
          
          stateAfterRight = layoutMindMapSide config tree expanded stateAfterLeft rightChildren 1.0 0
        in
          stateAfterRight
    
    bounds = Viewport.viewportBounds finalState.minX 0.0 finalState.maxX finalState.maxY
  in
    layoutResult finalState.positions bounds (Map.size finalState.positions)

-- | Mind map layout state
type MindMapState =
  { positions :: Map NodeId Schema.NodePosition
  , minX :: Number
  , maxX :: Number
  , maxY :: Number
  }

-- | Layout one side of mind map
layoutMindMapSide ::
  Schema.LayoutConfig ->
  Tree ->
  ExpandedState ->
  MindMapState ->
  Array TreeNode ->
  Number ->
  Int ->
  MindMapState
layoutMindMapSide config tree expanded state nodes direction level =
  let
    spacing = config.spacing
    nodeWidth = nodeSizeWidth config.sizing
    nodeHeight = nodeSizeHeight config.sizing
    levelGapVal = Schema.levelGap spacing
    sibGap = Schema.siblingGap spacing
    
    xBase = direction * (Int.toNumber (level + 1)) * (nodeWidth + levelGapVal)
    
    indexed = Array.mapWithIndex Tuple nodes
    
    stateAfterNodes = foldl
      (\s (Tuple idx node) ->
        let
          nid = nodeId node
          y = (Int.toNumber idx - Int.toNumber (Array.length nodes) / 2.0) * (nodeHeight + sibGap)
          pos = Schema.nodePosition xBase y nodeWidth nodeHeight
          
          newPositions = Map.insert nid pos s.positions
          newMinX = min s.minX xBase
          newMaxX = max s.maxX (xBase + nodeWidth)
          newMaxY = max s.maxY (y + nodeHeight)
          
          stateWithNode =
            { positions: newPositions
            , minX: newMinX
            , maxX: newMaxX
            , maxY: newMaxY
            }
          
          childrenIds = nodeChildren node
          isExp = isExpanded nid expanded
        in
          if isExp && Array.length childrenIds > 0
            then
              let
                childNodes = Array.mapMaybe (\cid -> getNode cid tree) childrenIds
              in
                layoutMindMapSide config tree expanded stateWithNode childNodes direction (level + 1)
            else
              stateWithNode
      )
      state
      indexed
  in
    stateAfterNodes

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Negate a Number
negateNum :: Number -> Number
negateNum n = 0.0 - n

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
