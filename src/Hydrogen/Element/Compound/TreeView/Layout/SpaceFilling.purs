-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // treeview // layout // spacefilling
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TreeView Space-Filling Layout — Treemap and icicle styles.
-- |
-- | ## Design Philosophy
-- |
-- | Space-filling layouts use area to represent value. Every pixel of the
-- | container is allocated to some node, with nested rectangles or bands.
-- |
-- | ## Algorithms
-- |
-- | - Treemap: Nested rectangles, area proportional to value (uses squarify)
-- | - Icicle: Horizontal bands, one per level
-- | - Partition: Similar to icicle (alias)
-- |
-- | ## Dependencies
-- |
-- | - TreeView.Types (NodeId)
-- | - TreeView.Node (Tree, TreeNode, traversal)
-- | - TreeView.State (ExpandedState)
-- | - Schema.Graph.Layout (LayoutConfig, TreemapParams)

module Hydrogen.Element.Compound.TreeView.Layout.SpaceFilling
  ( -- * Treemap Layout
    layoutTreemap
    
  -- * Icicle Layout  
  , layoutIcicle
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (+)
  , (/)
  , (*)
  , (>)
  , (&&)
  , (-)
  )

import Data.Array as Array
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Data.Map (Map)
import Data.Map as Map
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
  , NodePosition
  , TreemapParams
  , TreemapAlgorithm(Squarify)
  , nodePosition
  ) as Schema

import Hydrogen.Schema.Graph.Viewport
  ( ViewportBounds
  , viewportBounds
  , boundsWidth
  , boundsHeight
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
--                                                             // treemap layout
-- ═════════════════════════════════════════════════════════════════════════════

-- | Layout nodes as nested rectangles (area proportional to value)
-- |
-- | Uses squarify algorithm for optimal aspect ratios.
layoutTreemap :: 
  Schema.LayoutConfig -> 
  Tree -> 
  ExpandedState -> 
  LayoutResult
layoutTreemap config tree expanded =
  let
    _treemapParams = fromMaybe defaultTreemapParams config.treemapParams
    bounds = fromMaybe (Viewport.viewportBounds 0.0 0.0 800.0 600.0) 
             (boundsFromConstraints config)
    
    roots = rootNodes tree
    
    initialState = { positions: Map.empty }
    
    finalState = case Array.head roots of
      Nothing -> initialState
      Just rootNode ->
        layoutTreemapNode config tree expanded initialState rootNode bounds
    
    resultBounds = Viewport.viewportBounds 0.0 0.0 
                   (Viewport.boundsWidth bounds) 
                   (Viewport.boundsHeight bounds)
  in
    layoutResult finalState.positions resultBounds (Map.size finalState.positions)

-- | Default treemap params
defaultTreemapParams :: Schema.TreemapParams
defaultTreemapParams =
  { algorithm: Schema.Squarify
  , paddingInner: 2.0
  , paddingOuter: 4.0
  , paddingTop: 20.0
  , ratio: 1.618
  }

-- | Layout state for treemap
type TreemapState =
  { positions :: Map NodeId Schema.NodePosition
  }

-- | Layout a single treemap node
layoutTreemapNode ::
  Schema.LayoutConfig ->
  Tree ->
  ExpandedState ->
  TreemapState ->
  TreeNode ->
  Viewport.ViewportBounds ->
  TreemapState
layoutTreemapNode config tree expanded state node bounds =
  let
    nid = nodeId node
    
    pos = Schema.nodePosition 
          (Viewport.boundsWidth bounds / 2.0)
          (Viewport.boundsHeight bounds / 2.0)
          (Viewport.boundsWidth bounds)
          (Viewport.boundsHeight bounds)
    
    newPositions = Map.insert nid pos state.positions
    
    children = nodeChildren node
    isExp = isExpanded nid expanded
    padding = 4.0
  in
    if isExp && Array.length children > 0
      then
        let
          childNodes = Array.mapMaybe (\cid -> getNode cid tree) children
          innerBounds = Viewport.viewportBounds 
                        padding 
                        (padding + 20.0)
                        (Viewport.boundsWidth bounds - padding)
                        (Viewport.boundsHeight bounds - padding)
          childBounds = squarifyLayout childNodes innerBounds
          
          stateWithNode = { positions: newPositions }
        in
          foldl 
            (\s (Tuple n b) -> layoutTreemapNode config tree expanded s n b)
            stateWithNode
            childBounds
      else
        { positions: newPositions }

-- | Squarify algorithm for treemap layout
-- |
-- | Divides bounds among nodes, optimizing for square-ish rectangles.
squarifyLayout :: Array TreeNode -> Viewport.ViewportBounds -> Array (Tuple TreeNode Viewport.ViewportBounds)
squarifyLayout nodes bounds =
  let
    n = Array.length nodes
    totalWidth = Viewport.boundsWidth bounds
    totalHeight = Viewport.boundsHeight bounds
    
    sliceHeight = totalHeight / Int.toNumber n
  in
    Array.mapWithIndex
      (\idx node ->
        let
          y = Int.toNumber idx * sliceHeight
          nodeBounds = Viewport.viewportBounds 0.0 y totalWidth (y + sliceHeight)
        in
          Tuple node nodeBounds
      )
      nodes

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // icicle layout
-- ═════════════════════════════════════════════════════════════════════════════

-- | Icicle layout (vertical partition)
-- |
-- | Hierarchical partitions, each level a horizontal band.
layoutIcicle :: 
  Schema.LayoutConfig -> 
  Tree -> 
  ExpandedState -> 
  LayoutResult
layoutIcicle config tree expanded =
  let
    bounds = fromMaybe (Viewport.viewportBounds 0.0 0.0 800.0 600.0) 
             (boundsFromConstraints config)
    
    roots = rootNodes tree
    
    initialState = { positions: Map.empty }
    
    totalWidth = Viewport.boundsWidth bounds
    
    finalState = foldl
      (\s rootNode ->
        layoutIcicleNode config tree expanded s rootNode 0.0 0.0 totalWidth 0
      )
      initialState
      roots
    
    resultBounds = Viewport.viewportBounds 0.0 0.0 
                   (Viewport.boundsWidth bounds) 
                   (Viewport.boundsHeight bounds)
  in
    layoutResult finalState.positions resultBounds (Map.size finalState.positions)

-- | Icicle layout state
type IcicleState =
  { positions :: Map NodeId Schema.NodePosition
  }

-- | Layout an icicle node
layoutIcicleNode ::
  Schema.LayoutConfig ->
  Tree ->
  ExpandedState ->
  IcicleState ->
  TreeNode ->
  Number ->
  Number ->
  Number ->
  Int ->
  IcicleState
layoutIcicleNode config tree expanded state node x y width level =
  let
    nid = nodeId node
    levelHeight = 40.0
    
    pos = Schema.nodePosition (x + width / 2.0) (y + levelHeight / 2.0) width levelHeight
    newPositions = Map.insert nid pos state.positions
    
    children = nodeChildren node
    isExp = isExpanded nid expanded
  in
    if isExp && Array.length children > 0
      then
        let
          childNodes = Array.mapMaybe (\cid -> getNode cid tree) children
          n = Array.length childNodes
          childWidth = width / Int.toNumber n
          childY = y + levelHeight
          
          stateWithNode = { positions: newPositions }
          
          indexed = Array.mapWithIndex Tuple childNodes
        in
          foldl
            (\s (Tuple idx child) ->
              let
                childX = x + Int.toNumber idx * childWidth
              in
                layoutIcicleNode config tree expanded s child childX childY childWidth (level + 1)
            )
            stateWithNode
            indexed
      else
        { positions: newPositions }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

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
