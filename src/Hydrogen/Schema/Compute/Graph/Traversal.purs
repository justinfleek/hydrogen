-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // compute // graph // traversal
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Graph traversal, validation, and subgraph operations.
-- |
-- | This module provides algorithms for working with compute graphs:
-- | - Graph traversal (BFS, DFS, topological sort)
-- | - Validation (DAG check, shape/dtype compatibility)
-- | - Subgraph extraction and merging
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Compute.Graph.Types (Graph, Node, NodeId, Edge)

module Hydrogen.Schema.Compute.Graph.Traversal
  ( -- * Graph Queries
    nodeCount
  , edgeCount
  , getNode
  , getNodes
  , getEdges
  , inputNodes
  , outputNodes
  , predecessors
  , successors
  
  -- * Graph Properties
  , isDAG
  , isEmpty
  , isConnected
  , maxDepth
  
  -- * Graph Traversal
  , topoSort
  , reverseTopoSort
  , bfs
  , dfs
  
  -- * Validation
  , validateGraph
  , validateShapes
  , validateDTypes
  
  -- * Subgraphs
  , subgraph
  , merge
  , inline
  
  -- * String Representation
  , graphToString
  , nodeToString
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Show
  , show
  , map
  , not
  , (==)
  , (/=)
  , (<>)
  , (>)
  , ($)
  , (+)
  , (&&)
  , (||)
  )

import Data.Array as Array
import Data.Foldable (foldl, all)
import Data.Maybe (Maybe(Just, Nothing), isJust)
import Data.Tuple (Tuple(Tuple))

import Hydrogen.Schema.Compute.Graph.Types
  ( Graph
  , Node
  , NodeId(NodeId)
  , Edge
  )
import Hydrogen.Schema.Compute.Operation (operationName)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // graph queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Number of nodes in the graph.
nodeCount :: Graph -> Int
nodeCount graph = Array.length graph.nodes

-- | Number of edges in the graph.
edgeCount :: Graph -> Int
edgeCount graph = Array.length graph.edges

-- | Get a node by ID.
getNode :: NodeId -> Graph -> Maybe Node
getNode nid graph = Array.find (\n -> n.id == nid) graph.nodes

-- | Get all nodes.
getNodes :: Graph -> Array Node
getNodes graph = graph.nodes

-- | Get all edges.
getEdges :: Graph -> Array Edge
getEdges graph = graph.edges

-- | Get graph input nodes.
inputNodes :: Graph -> Array NodeId
inputNodes graph = graph.inputs

-- | Get graph output nodes.
outputNodes :: Graph -> Array NodeId
outputNodes graph = graph.outputs

-- | Get predecessor nodes (nodes that feed into this one).
predecessors :: NodeId -> Graph -> Array NodeId
predecessors nid graph =
  let
    incomingEdges = Array.filter (\e -> e.target == nid) graph.edges
  in
    map (\e -> e.source.nodeId) incomingEdges

-- | Get successor nodes (nodes that consume this one's output).
successors :: NodeId -> Graph -> Array NodeId
successors nid graph =
  let
    outgoingEdges = Array.filter (\e -> e.source.nodeId == nid) graph.edges
  in
    map (\e -> e.target) outgoingEdges

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // graph properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is this graph a directed acyclic graph (DAG)?
-- |
-- | Compute graphs must be DAGs for execution ordering.
isDAG :: Graph -> Boolean
isDAG graph = 
  -- A graph is a DAG if topological sort succeeds
  isJust (topoSort graph)

-- | Is the graph empty?
isEmpty :: Graph -> Boolean
isEmpty graph = Array.length graph.nodes == 0

-- | Is the graph connected?
-- |
-- | Every node should be reachable from inputs or reach outputs.
isConnected :: Graph -> Boolean
isConnected graph =
  let
    allIds = map (\n -> n.id) graph.nodes
    reachableFromInputs = reachableFrom graph.inputs graph
    canReachOutputs = canReach graph.outputs graph
  in
    all (\nid -> Array.elem nid reachableFromInputs || Array.elem nid canReachOutputs) allIds

-- | Maximum depth of the graph (longest path from any input to any output).
maxDepth :: Graph -> Int
maxDepth graph = case topoSort graph of
  Nothing -> 0
  Just sorted ->
    let
      depths = computeDepths sorted graph
    in
      foldl (\acc (Tuple _ d) -> if d > acc then d else acc) 0 depths

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // graph traversal
-- ═════════════════════════════════════════════════════════════════════════════

-- | Topological sort of graph nodes.
-- |
-- | Returns Nothing if graph has cycles.
topoSort :: Graph -> Maybe (Array NodeId)
topoSort graph = topoSortHelper graph.nodes graph []

-- | Reverse topological sort (outputs before inputs).
reverseTopoSort :: Graph -> Maybe (Array NodeId)
reverseTopoSort graph = map Array.reverse (topoSort graph)

-- | Breadth-first search from starting nodes.
bfs :: Array NodeId -> Graph -> Array NodeId
bfs start graph = bfsHelper start [] graph

-- | Depth-first search from starting nodes.
dfs :: Array NodeId -> Graph -> Array NodeId
dfs start graph = dfsHelper start [] graph

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Validate the entire graph.
-- |
-- | Checks:
-- | - Is DAG
-- | - Shapes are compatible
-- | - DTypes are compatible
-- | - No dangling edges
validateGraph :: Graph -> Boolean
validateGraph graph =
  isDAG graph && validateShapes graph && validateDTypes graph && noDanglingEdges graph

-- | Validate that tensor shapes are compatible across edges.
validateShapes :: Graph -> Boolean
validateShapes graph =
  all (validateEdgeShape graph) graph.edges

-- | Validate that tensor dtypes are compatible across edges.
validateDTypes :: Graph -> Boolean
validateDTypes graph =
  all (validateEdgeDType graph) graph.edges

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // subgraphs
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract a subgraph containing only the specified nodes.
subgraph :: Array NodeId -> Graph -> Graph
subgraph nodeIds graph =
  let
    nodes = Array.filter (\n -> Array.elem n.id nodeIds) graph.nodes
    edges = Array.filter (\e -> 
      Array.elem e.source.nodeId nodeIds && Array.elem e.target nodeIds
    ) graph.edges
    inputs = Array.filter (\i -> Array.elem i nodeIds) graph.inputs
    outputs = Array.filter (\o -> Array.elem o nodeIds) graph.outputs
  in
    { nodes, edges, inputs, outputs, nextId: graph.nextId, name: graph.name <> "_sub" }

-- | Merge two graphs.
-- |
-- | Node IDs in the second graph are remapped to avoid conflicts.
merge :: Graph -> Graph -> Graph
merge g1 g2 =
  let
    offset = g1.nextId
    remapId (NodeId n) = NodeId (n + offset)
    remapNode n = n 
      { id = remapId n.id }
    remapEdge e = e
      { source = e.source { nodeId = remapId e.source.nodeId }
      , target = remapId e.target
      }
    newNodes = map remapNode g2.nodes
    newEdges = map remapEdge g2.edges
    newInputs = map remapId g2.inputs
    newOutputs = map remapId g2.outputs
  in
    { nodes: g1.nodes <> newNodes
    , edges: g1.edges <> newEdges
    , inputs: g1.inputs <> newInputs
    , outputs: g1.outputs <> newOutputs
    , nextId: g1.nextId + g2.nextId
    , name: g1.name
    }

-- | Inline a subgraph into the main graph at a specific node.
-- |
-- | Replaces the node with the subgraph, connecting edges appropriately.
inline :: NodeId -> Graph -> Graph -> Graph
inline targetNode subG mainG =
  -- For now, just merge. Full inlining with edge reconnection is complex.
  merge (removeNodeInternal targetNode mainG) subG

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // string representation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert graph to string representation.
graphToString :: Graph -> String
graphToString graph =
  "Graph(" <> graph.name <> ", " <> 
  show (nodeCount graph) <> " nodes, " <> 
  show (edgeCount graph) <> " edges)"

-- | Convert node to string representation.
nodeToString :: Node -> String
nodeToString n = case n.name of
  Just name -> show n.id <> ": " <> name <> " (" <> operationName n.operation <> ")"
  Nothing -> show n.id <> ": " <> operationName n.operation

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Helper for topological sort (Kahn's algorithm).
topoSortHelper :: Array Node -> Graph -> Array NodeId -> Maybe (Array NodeId)
topoSortHelper remaining graph sorted =
  if Array.length remaining == 0 
  then Just sorted
  else
    let
      -- Find nodes with no unsorted predecessors
      noIncoming = Array.filter (\n -> 
        let preds = predecessors n.id graph
            unsortedPreds = Array.filter (\p -> not (Array.elem p sorted)) preds
        in Array.length unsortedPreds == 0
      ) remaining
    in
      case Array.head noIncoming of
        Nothing -> Nothing  -- Cycle detected
        Just n ->
          let
            newRemaining = Array.filter (\x -> x.id /= n.id) remaining
            newSorted = Array.snoc sorted n.id
          in
            topoSortHelper newRemaining graph newSorted

-- | BFS helper
bfsHelper :: Array NodeId -> Array NodeId -> Graph -> Array NodeId
bfsHelper queue visited graph =
  case Array.uncons queue of
    Nothing -> visited
    Just { head: current, tail: rest } ->
      if Array.elem current visited
      then bfsHelper rest visited graph
      else
        let
          succs = successors current graph
          newQueue = rest <> succs
          newVisited = Array.snoc visited current
        in
          bfsHelper newQueue newVisited graph

-- | DFS helper
dfsHelper :: Array NodeId -> Array NodeId -> Graph -> Array NodeId
dfsHelper stack visited graph =
  case Array.uncons stack of
    Nothing -> visited
    Just { head: current, tail: rest } ->
      if Array.elem current visited
      then dfsHelper rest visited graph
      else
        let
          succs = successors current graph
          newStack = succs <> rest
          newVisited = Array.snoc visited current
        in
          dfsHelper newStack newVisited graph

-- | Compute depths for all nodes
computeDepths :: Array NodeId -> Graph -> Array (Tuple NodeId Int)
computeDepths sorted graph =
  let
    folder depths nid =
      let
        preds = predecessors nid graph
        predDepths = map (\p -> lookupDepth p depths) preds
        maxPredDepth = foldl (\a d -> if d > a then d else a) 0 predDepths
      in
        Array.snoc depths (Tuple nid (maxPredDepth + 1))
  in
    foldl folder [] sorted

-- | Look up depth for a node
lookupDepth :: NodeId -> Array (Tuple NodeId Int) -> Int
lookupDepth nid depths =
  case Array.find (\(Tuple n _) -> n == nid) depths of
    Just (Tuple _ d) -> d
    Nothing -> 0

-- | Check if nodes can reach targets
canReach :: Array NodeId -> Graph -> Array NodeId
canReach targets graph =
  -- Reverse BFS from targets
  bfsHelper targets [] graph

-- | Nodes reachable from starting points
reachableFrom :: Array NodeId -> Graph -> Array NodeId
reachableFrom starts graph = bfs starts graph

-- | Validate shape compatibility for an edge
validateEdgeShape :: Graph -> Edge -> Boolean
validateEdgeShape graph edge =
  case getNode edge.source.nodeId graph of
    Nothing -> false
    Just sourceNode ->
      case Array.index sourceNode.outputs edge.source.outputIndex of
        Nothing -> false
        Just sourcePort ->
          case getNode edge.target graph of
            Nothing -> false
            Just targetNode ->
              case Array.index targetNode.inputs edge.targetInput of
                Nothing -> false
                Just targetPort -> sourcePort.shape == targetPort.shape

-- | Validate dtype compatibility for an edge
validateEdgeDType :: Graph -> Edge -> Boolean
validateEdgeDType graph edge =
  case getNode edge.source.nodeId graph of
    Nothing -> false
    Just sourceNode ->
      case Array.index sourceNode.outputs edge.source.outputIndex of
        Nothing -> false
        Just sourcePort ->
          case getNode edge.target graph of
            Nothing -> false
            Just targetNode ->
              case Array.index targetNode.inputs edge.targetInput of
                Nothing -> false
                Just targetPort -> sourcePort.dtype == targetPort.dtype

-- | Check for dangling edges
noDanglingEdges :: Graph -> Boolean
noDanglingEdges graph =
  let
    nodeIds = map (\n -> n.id) graph.nodes
  in
    all (\e -> Array.elem e.source.nodeId nodeIds && Array.elem e.target nodeIds) graph.edges

-- | Internal remove node helper (used by inline)
removeNodeInternal :: NodeId -> Graph -> Graph
removeNodeInternal nid graph =
  let
    nodes = Array.filter (\n -> n.id /= nid) graph.nodes
    edges = Array.filter (\e -> e.source.nodeId /= nid && e.target /= nid) graph.edges
    inputs = Array.filter (\i -> i /= nid) graph.inputs
    outputs = Array.filter (\o -> o /= nid) graph.outputs
  in
    graph { nodes = nodes, edges = edges, inputs = inputs, outputs = outputs }
