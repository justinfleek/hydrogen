-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // compute // graph // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core types for compute graphs.
-- |
-- | This module defines the fundamental data structures:
-- | - NodeId: Unique node identifier
-- | - Port: Named input/output slot
-- | - TensorRef: Reference to tensor output
-- | - Node: Graph node (operation with inputs/outputs)
-- | - Edge: Connection between nodes
-- | - Graph: The complete compute graph

module Hydrogen.Schema.Compute.Graph.Types
  ( -- * Node Identity
    NodeId(..)
  , unwrapNodeId
  
  -- * Port Types
  , Port
  , TensorRef
  
  -- * Core Types
  , Node
  , Edge
  , Graph
  
  -- * Graph Construction
  , emptyGraph
  , addNode
  , addEdge
  , addInput
  , addOutput
  , removeNode
  , removeEdge
  
  -- * Node Accessors
  , nodeId
  , nodeOp
  , nodeInputs
  , nodeOutputs
  , nodeShape
  , nodeDType
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , map
  , not
  , (==)
  , (/=)
  , (<>)
  , ($)
  , (+)
  , (&&)
  )

import Data.Array as Array
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Tensor.Shape (Shape)
import Hydrogen.Schema.Tensor.DType (DType)
import Hydrogen.Schema.Compute.Operation (Operation)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // node id
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for a node in the graph.
newtype NodeId = NodeId Int

derive instance eqNodeId :: Eq NodeId
derive instance ordNodeId :: Ord NodeId

instance showNodeId :: Show NodeId where
  show (NodeId n) = "n" <> show n

-- | Unwrap node ID
unwrapNodeId :: NodeId -> Int
unwrapNodeId (NodeId n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // port
-- ═════════════════════════════════════════════════════════════════════════════

-- | A named port (input or output) on a node.
-- |
-- | Ports have a name, shape, and dtype.
type Port =
  { name :: String
  , shape :: Shape
  , dtype :: DType
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // tensor ref
-- ═════════════════════════════════════════════════════════════════════════════

-- | Reference to a tensor (output of a node).
-- |
-- | Used to specify inputs to operations.
type TensorRef =
  { nodeId :: NodeId
  , outputIndex :: Int  -- Which output of the node
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // node
-- ═════════════════════════════════════════════════════════════════════════════

-- | A node in the compute graph.
-- |
-- | Each node has:
-- | - A unique ID
-- | - An operation to perform
-- | - Input ports (consumed tensors)
-- | - Output ports (produced tensors)
-- | - Optional name for debugging
type Node =
  { id :: NodeId
  , operation :: Operation
  , inputs :: Array Port
  , outputs :: Array Port
  , name :: Maybe String
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // edge
-- ═════════════════════════════════════════════════════════════════════════════

-- | An edge connecting two nodes.
-- |
-- | Edges represent tensor flow from a source node's output
-- | to a target node's input.
type Edge =
  { source :: TensorRef      -- Which node/output produces the tensor
  , target :: NodeId         -- Which node consumes it
  , targetInput :: Int       -- Which input slot
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // graph
-- ═════════════════════════════════════════════════════════════════════════════

-- | A compute graph.
-- |
-- | Contains nodes (operations) and edges (tensor flow).
-- | Graph inputs and outputs are special nodes marked accordingly.
type Graph =
  { nodes :: Array Node
  , edges :: Array Edge
  , inputs :: Array NodeId   -- Graph input nodes
  , outputs :: Array NodeId  -- Graph output nodes
  , nextId :: Int            -- For generating unique IDs
  , name :: String           -- Graph name
  }

-- ════════════════════════════════════════════════════════════════════════��════
--                                                         // graph construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create an empty graph.
emptyGraph :: String -> Graph
emptyGraph graphName =
  { nodes: []
  , edges: []
  , inputs: []
  , outputs: []
  , nextId: 0
  , name: graphName
  }

-- | Add a node to the graph.
-- |
-- | Returns the new graph and the ID of the added node.
addNode :: Operation -> Array Port -> Array Port -> Maybe String -> Graph -> { graph :: Graph, nodeId :: NodeId }
addNode operation inputs outputs nodeName graph =
  let
    nid = NodeId graph.nextId
    node = 
      { id: nid
      , operation
      , inputs
      , outputs
      , name: nodeName
      }
    newGraph = graph
      { nodes = Array.snoc graph.nodes node
      , nextId = graph.nextId + 1
      }
  in
    { graph: newGraph, nodeId: nid }

-- | Add an edge between two nodes.
addEdge :: TensorRef -> NodeId -> Int -> Graph -> Graph
addEdge source target targetInput graph =
  let
    edge = { source, target, targetInput }
  in
    graph { edges = Array.snoc graph.edges edge }

-- | Mark a node as a graph input.
addInput :: NodeId -> Graph -> Graph
addInput nid graph = 
  graph { inputs = Array.snoc graph.inputs nid }

-- | Mark a node as a graph output.
addOutput :: NodeId -> Graph -> Graph
addOutput nid graph = 
  graph { outputs = Array.snoc graph.outputs nid }

-- | Remove a node from the graph.
-- |
-- | Also removes all edges connected to this node.
removeNode :: NodeId -> Graph -> Graph
removeNode nid graph =
  let
    nodes = Array.filter (\n -> n.id /= nid) graph.nodes
    edges = Array.filter (\e -> e.source.nodeId /= nid && e.target /= nid) graph.edges
    graphInputs = Array.filter (\i -> i /= nid) graph.inputs
    graphOutputs = Array.filter (\o -> o /= nid) graph.outputs
  in
    graph { nodes = nodes, edges = edges, inputs = graphInputs, outputs = graphOutputs }

-- | Remove an edge from the graph.
removeEdge :: TensorRef -> NodeId -> Int -> Graph -> Graph
removeEdge source target targetInput graph =
  let
    edges = Array.filter (\e -> 
      not (e.source == source && e.target == target && e.targetInput == targetInput)
    ) graph.edges
  in
    graph { edges = edges }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // node operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the ID of a node.
nodeId :: Node -> NodeId
nodeId n = n.id

-- | Get the operation of a node.
nodeOp :: Node -> Operation
nodeOp n = n.operation

-- | Get the input ports of a node.
nodeInputs :: Node -> Array Port
nodeInputs n = n.inputs

-- | Get the output ports of a node.
nodeOutputs :: Node -> Array Port
nodeOutputs n = n.outputs

-- | Get the shape of a node's first output.
nodeShape :: Node -> Maybe Shape
nodeShape n = map (\p -> p.shape) (Array.head n.outputs)

-- | Get the dtype of a node's first output.
nodeDType :: Node -> Maybe DType
nodeDType n = map (\p -> p.dtype) (Array.head n.outputs)
