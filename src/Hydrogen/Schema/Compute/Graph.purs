-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // compute // graph
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Graph — Compute graph primitives for ML models.
-- |
-- | ## Design Philosophy
-- |
-- | A compute graph is a directed acyclic graph (DAG) of operations.
-- | Nodes represent operations, edges represent tensor flow between them.
-- | This structure enables:
-- | - Static analysis and optimization
-- | - Automatic differentiation
-- | - Parallel execution scheduling
-- | - Hardware-specific compilation
-- |
-- | ## Graph Structure
-- |
-- | - **Node**: An operation with typed inputs and outputs
-- | - **Edge**: Tensor flow from one node's output to another's input
-- | - **Port**: Named input/output slot on a node
-- |
-- | ## Module Structure
-- |
-- | This is the leader module that re-exports:
-- | - `Graph.Types`: Core types and construction
-- | - `Graph.Traversal`: Queries, traversal, validation, subgraphs
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)
-- | - Hydrogen.Schema.Tensor.Shape (Shape)
-- | - Hydrogen.Schema.Tensor.DType (DType)
-- | - Hydrogen.Schema.Compute.Operation (Operation)

module Hydrogen.Schema.Compute.Graph
  ( -- * Re-export Types
    module Hydrogen.Schema.Compute.Graph.Types
  -- * Re-export Traversal
  , module Hydrogen.Schema.Compute.Graph.Traversal
  ) where

-- Re-export all types and construction
import Hydrogen.Schema.Compute.Graph.Types
  ( NodeId(..)
  , unwrapNodeId
  , Port
  , TensorRef
  , Node
  , Edge
  , Graph
  , emptyGraph
  , addNode
  , addEdge
  , addInput
  , addOutput
  , removeNode
  , removeEdge
  , nodeId
  , nodeOp
  , nodeInputs
  , nodeOutputs
  , nodeShape
  , nodeDType
  )

-- Re-export all traversal, queries, validation, subgraphs
import Hydrogen.Schema.Compute.Graph.Traversal
  ( nodeCount
  , edgeCount
  , getNode
  , getNodes
  , getEdges
  , inputNodes
  , outputNodes
  , predecessors
  , successors
  , isDAG
  , isEmpty
  , isConnected
  , maxDepth
  , topoSort
  , reverseTopoSort
  , bfs
  , dfs
  , validateGraph
  , validateShapes
  , validateDTypes
  , subgraph
  , merge
  , inline
  , graphToString
  , nodeToString
  )
