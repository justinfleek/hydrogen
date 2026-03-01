-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // treeview // layout // radial
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TreeView Radial Layout — Circular and polar coordinate layouts.
-- |
-- | ## Design Philosophy
-- |
-- | Radial layouts use polar coordinates to position nodes. The root is at
-- | the center, with children on concentric rings radiating outward.
-- |
-- | ## Algorithms
-- |
-- | - Radial: Nodes on concentric circles
-- | - Sunburst: Arc segments representing hierarchy
-- | - CirclePack: Nested circles with children packed inside
-- |
-- | ## Dependencies
-- |
-- | - TreeView.Types (NodeId)
-- | - TreeView.Node (Tree, TreeNode, traversal)
-- | - TreeView.State (ExpandedState)
-- | - Schema.Graph.Layout (LayoutConfig, RadialParams)

module Hydrogen.Element.Compound.TreeView.Layout.Radial
  ( -- * Radial Layout
    layoutRadial
    
  -- * Sunburst Layout
  , layoutSunburst
  
  -- * Circle Pack Layout
  , layoutCirclePack
  
  -- * Trigonometry Helpers
  , cos
  , sin
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (-)
  , (+)
  , (/)
  , (*)
  , (==)
  , (>)
  , (&&)
  )

import Data.Array as Array
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Data.Map (Map)
import Data.Map as Map
import Data.Tuple (Tuple(Tuple))
import Data.Foldable (foldl)
import Data.Int (toNumber, floor) as Int

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
  , RadialParams
  , startAngle
  , endAngle
  , innerRadius
  , outerRadius
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
--                                                              // radial layout
-- ═════════════════════════════════════════════════════════════════════════════

-- | Layout nodes on concentric circles
-- |
-- | Root at center, children on first ring, grandchildren on second ring, etc.
layoutRadial :: 
  Schema.LayoutConfig -> 
  Tree -> 
  ExpandedState -> 
  LayoutResult
layoutRadial config tree expanded =
  let
    radialParams = fromMaybe defaultRadialParams config.radialParams
    start = Schema.startAngle radialParams
    end = Schema.endAngle radialParams
    inner = Schema.innerRadius radialParams
    outer = Schema.outerRadius radialParams
    
    roots = rootNodes tree
    nodeSize = nodeSizeWidth config.sizing
    
    initialState = { positions: Map.empty }
    
    finalState = case Array.head roots of
      Nothing -> initialState
      Just rootNode -> 
        let
          rootPos = Schema.nodePosition 0.0 0.0 nodeSize nodeSize
          stateWithRoot = { positions: Map.insert (nodeId rootNode) rootPos Map.empty }
          childIds = nodeChildren rootNode
          childNodes = Array.mapMaybe (\cid -> getNode cid tree) childIds
          angleStep = (end - start) / Int.toNumber (Array.length childNodes)
        in
          layoutRadialLevel config tree expanded stateWithRoot childNodes inner angleStep start 1
    
    bounds = Viewport.viewportBounds (negateNum outer) (negateNum outer) outer outer
  in
    layoutResult finalState.positions bounds (Map.size finalState.positions)

-- | Default radial params
defaultRadialParams :: Schema.RadialParams
defaultRadialParams = 
  { startAngle: 0.0
  , endAngle: 6.28318
  , innerRadius: 50.0
  , outerRadius: 300.0
  , clockwise: true
  }

-- | Layout state for radial
type RadialState =
  { positions :: Map NodeId Schema.NodePosition
  }

-- | Layout a level of radial tree
layoutRadialLevel ::
  Schema.LayoutConfig ->
  Tree ->
  ExpandedState ->
  RadialState ->
  Array TreeNode ->
  Number ->
  Number ->
  Number ->
  Int ->
  RadialState
layoutRadialLevel config tree expanded state nodes radius angleStep startAngle level =
  let
    nodeSize = nodeSizeWidth config.sizing
    radiusStep = 60.0
    
    indexed = Array.mapWithIndex Tuple nodes
    
    stateAfterLevel = foldl 
      (\s (Tuple idx node) ->
        let
          angle = startAngle + (Int.toNumber idx * angleStep)
          x = radius * cos angle
          y = radius * sin angle
          pos = Schema.nodePosition x y nodeSize nodeSize
        in
          { positions: Map.insert (nodeId node) pos s.positions }
      )
      state
      indexed
    
    stateAfterChildren = foldl
      (\s node ->
        let
          nid = nodeId node
          children = nodeChildren node
          isExp = isExpanded nid expanded
        in
          if isExp && Array.length children > 0
            then
              let
                childNodes = Array.mapMaybe (\cid -> getNode cid tree) children
                childAngleStep = angleStep / Int.toNumber (Array.length childNodes)
                parentIdx = fromMaybe 0 (Array.findIndex (\n -> nodeId n == nid) nodes)
                parentAngle = startAngle + (Int.toNumber parentIdx * angleStep)
                childStartAngle = parentAngle - (angleStep / 2.0)
              in
                layoutRadialLevel config tree expanded s childNodes (radius + radiusStep) childAngleStep childStartAngle (level + 1)
            else
              s
      )
      stateAfterLevel
      nodes
  in
    stateAfterChildren

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // sunburst layout
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sunburst layout (radial treemap)
-- |
-- | Arcs radiating from center, angle represents hierarchy.
layoutSunburst :: 
  Schema.LayoutConfig -> 
  Tree -> 
  ExpandedState -> 
  LayoutResult
layoutSunburst config tree expanded =
  layoutRadial config tree expanded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // circle pack layout
-- ═════════════════════════════════════════════════════════════════════════════

-- | Circle packing layout
-- |
-- | Nested circles, children packed inside parent circle.
layoutCirclePack :: 
  Schema.LayoutConfig -> 
  Tree -> 
  ExpandedState -> 
  LayoutResult
layoutCirclePack config tree expanded =
  let
    roots = rootNodes tree
    
    initialState = { positions: Map.empty }
    
    finalState = case Array.head roots of
      Nothing -> initialState
      Just rootNode ->
        layoutCirclePackNode config tree expanded initialState rootNode 0.0 0.0 200.0
    
    bounds = Viewport.viewportBounds (negateNum 200.0) (negateNum 200.0) 200.0 200.0
  in
    layoutResult finalState.positions bounds (Map.size finalState.positions)

-- | Circle pack state
type CirclePackState =
  { positions :: Map NodeId Schema.NodePosition
  }

-- | Layout a circle pack node
layoutCirclePackNode ::
  Schema.LayoutConfig ->
  Tree ->
  ExpandedState ->
  CirclePackState ->
  TreeNode ->
  Number ->
  Number ->
  Number ->
  CirclePackState
layoutCirclePackNode config tree expanded state node cx cy radius =
  let
    nid = nodeId node
    diameter = radius * 2.0
    pos = Schema.nodePosition cx cy diameter diameter
    
    newPositions = Map.insert nid pos state.positions
    
    children = nodeChildren node
    isExp = isExpanded nid expanded
  in
    if isExp && Array.length children > 0
      then
        let
          childNodes = Array.mapMaybe (\cid -> getNode cid tree) children
          n = Array.length childNodes
          childRadius = radius * 0.4
          
          stateWithNode = { positions: newPositions }
          
          indexed = Array.mapWithIndex Tuple childNodes
        in
          foldl
            (\s (Tuple idx child) ->
              let
                angle = 2.0 * 3.14159 * Int.toNumber idx / Int.toNumber n
                childCx = cx + (radius - childRadius) * cos angle
                childCy = cy + (radius - childRadius) * sin angle
              in
                layoutCirclePackNode config tree expanded s child childCx childCy childRadius
            )
            stateWithNode
            indexed
      else
        { positions: newPositions }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // trigonometry helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cosine function (Taylor series approximation)
-- |
-- | Uses Taylor series for angles in radians:
-- | cos(x) ≈ 1 - x²/2! + x⁴/4! - x⁶/6!
cos :: Number -> Number
cos angle = 
  let
    pi = 3.14159265359
    tau = 2.0 * pi
    normalized = angle - (Int.toNumber (floor (angle / tau))) * tau
    x = normalized
    x2 = x * x
    x4 = x2 * x2
    x6 = x4 * x2
  in
    1.0 - (x2 / 2.0) + (x4 / 24.0) - (x6 / 720.0)

-- | Sine function (derived from cosine)
-- |
-- | sin(x) = cos(x - π/2)
sin :: Number -> Number
sin angle =
  let
    pi = 3.14159265359
  in
    cos (angle - pi / 2.0)

-- | Floor function - delegate to Data.Int.floor
floor :: Number -> Int
floor = Int.floor

-- | Negate a Number
negateNum :: Number -> Number
negateNum n = 0.0 - n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract node width from sizing config
nodeSizeWidth :: Schema.NodeSizing -> Number
nodeSizeWidth (Schema.FixedSize w _) = w
nodeSizeWidth (Schema.FitContent minW _) = minW
nodeSizeWidth Schema.Proportional = 100.0
nodeSizeWidth (Schema.AspectRatio r) = 100.0 * r
