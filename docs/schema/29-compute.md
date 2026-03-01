━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                                 // 29 // compute
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Compute Pillar

ML compute graphs, operations, and tensor flow for neural network inference.

────────────────────────────────────────────────────────────────────────────────
                                                                      // overview
────────────────────────────────────────────────────────────────────────────────

## Implementation

- **Location**: `src/Hydrogen/Schema/Compute/`
- **Files**: 4 modules
- **Key features**: Compute graph DAG, ML operations, shape inference,
  graph traversal and validation

## Purpose

Compute provides infrastructure for **ML model representation** as pure data:

- **Graph**: Directed acyclic graph (DAG) of operations
- **Node**: Operation with typed inputs and outputs
- **Edge**: Tensor flow between nodes
- **Operation**: Linear, elementwise, attention, normalization, shape ops

## Module Structure

```
Compute/
├── Graph.purs           # Leader module (re-exports Types + Traversal)
├── Graph/
│   ├── Types.purs       # Core types and construction
│   └── Traversal.purs   # Queries, traversal, validation, subgraphs
└── Operation.purs       # ML operations vocabulary
```

────────────────────────────────────────────────────────────────────────────────
                                                        // design // philosophy
────────────────────────────────────────────────────────────────────────────────

## Why Pure Data Matters

A compute graph is a **pure description** of computation:
- Nodes describe WHAT operations to perform
- Edges describe HOW tensors flow between operations
- Execution happens separately (interpreter pattern)

**Benefits at billion-agent scale:**
- Static analysis before execution
- Automatic differentiation
- Hardware-agnostic representation
- Deterministic shape/dtype validation
- Parallel execution scheduling

────────────────────────────────────────────────────────────────────────────────
                                                                 // graph // types
────────────────────────────────────────────────────────────────────────────────

## NodeId

Unique identifier for graph nodes.

```purescript
newtype NodeId = NodeId Int
```

| Function | Type | Description |
|----------|------|-------------|
| `unwrapNodeId` | `NodeId -> Int` | Extract underlying integer |

## Port

Named input/output slot on a node.

```purescript
type Port =
  { name :: String
  , shape :: Shape
  , dtype :: DType
  }
```

## TensorRef

Reference to a tensor (output of a node).

```purescript
type TensorRef =
  { nodeId :: NodeId
  , outputIndex :: Int
  }
```

## Node

A node in the compute graph.

```purescript
type Node =
  { id :: NodeId
  , operation :: Operation
  , inputs :: Array Port
  , outputs :: Array Port
  , name :: Maybe String
  }
```

## Edge

Connection between nodes (tensor flow).

```purescript
type Edge =
  { source :: TensorRef
  , target :: NodeId
  , targetInput :: Int
  }
```

## Graph

The complete compute graph.

```purescript
type Graph =
  { nodes :: Array Node
  , edges :: Array Edge
  , inputs :: Array NodeId
  , outputs :: Array NodeId
  , nextId :: Int
  , name :: String
  }
```

────────────────────────────────────────────────────────────────────────────────
                                                        // graph // construction
────────────────────────────────────────────────────────────────────────────────

## Construction Functions

| Function | Description |
|----------|-------------|
| `emptyGraph name` | Create empty graph with given name |
| `addNode op inputs outputs name graph` | Add node, returns `{ graph, nodeId }` |
| `addEdge source target targetInput graph` | Connect nodes |
| `addInput nodeId graph` | Mark node as graph input |
| `addOutput nodeId graph` | Mark node as graph output |
| `removeNode nodeId graph` | Remove node and connected edges |
| `removeEdge source target targetInput graph` | Remove specific edge |

## Node Accessors

| Function | Description |
|----------|-------------|
| `nodeId` | Get node ID |
| `nodeOp` | Get node operation |
| `nodeInputs` | Get input ports |
| `nodeOutputs` | Get output ports |
| `nodeShape` | Get first output shape |
| `nodeDType` | Get first output dtype |

────────────────────────────────────────────────────────────────────────────────
                                                           // graph // traversal
────────────────────────────────────────────────────────────────────────────────

## Graph Queries

| Function | Type | Description |
|----------|------|-------------|
| `nodeCount` | `Graph -> Int` | Number of nodes |
| `edgeCount` | `Graph -> Int` | Number of edges |
| `getNode` | `NodeId -> Graph -> Maybe Node` | Find node by ID |
| `getNodes` | `Graph -> Array Node` | All nodes |
| `getEdges` | `Graph -> Array Edge` | All edges |
| `inputNodes` | `Graph -> Array NodeId` | Graph inputs |
| `outputNodes` | `Graph -> Array NodeId` | Graph outputs |
| `predecessors` | `NodeId -> Graph -> Array NodeId` | Nodes feeding into this one |
| `successors` | `NodeId -> Graph -> Array NodeId` | Nodes consuming this one's output |

## Graph Properties

| Function | Type | Description |
|----------|------|-------------|
| `isDAG` | `Graph -> Boolean` | Is directed acyclic graph? |
| `isEmpty` | `Graph -> Boolean` | Has no nodes? |
| `isConnected` | `Graph -> Boolean` | All nodes reachable? |
| `maxDepth` | `Graph -> Int` | Longest path length |

## Traversal Algorithms

| Function | Type | Description |
|----------|------|-------------|
| `topoSort` | `Graph -> Maybe (Array NodeId)` | Topological order (Nothing if cyclic) |
| `reverseTopoSort` | `Graph -> Maybe (Array NodeId)` | Reverse topological order |
| `bfs` | `Array NodeId -> Graph -> Array NodeId` | Breadth-first search |
| `dfs` | `Array NodeId -> Graph -> Array NodeId` | Depth-first search |

────────────────────────────────────────────────────────────────────────────────
                                                           // graph // validation
────────────────────────────────────────────────────────────────────────────────

## Validation Functions

| Function | Description |
|----------|-------------|
| `validateGraph` | Full validation (DAG + shapes + dtypes + edges) |
| `validateShapes` | Check shape compatibility across edges |
| `validateDTypes` | Check dtype compatibility across edges |

**validateGraph** checks:
1. Graph is a DAG (no cycles)
2. Tensor shapes are compatible across edges
3. Tensor dtypes are compatible across edges
4. No dangling edges (all referenced nodes exist)

────────────────────────────────────────────────────────────────────────────────
                                                              // graph // subgraphs
────────────────────────────────────────────────────────────────────────────────

## Subgraph Operations

| Function | Description |
|----------|-------------|
| `subgraph nodeIds graph` | Extract subgraph with specified nodes |
| `merge g1 g2` | Merge two graphs (remaps IDs to avoid conflicts) |
| `inline targetNode subG mainG` | Replace node with subgraph |

**merge** handles ID conflicts by offsetting all IDs in the second graph
by `g1.nextId`, ensuring uniqueness.

────────────────────────────────────────────────────────────────────────────────
                                                                  // operations
────────────────────────────────────────────────────────────────────────────────

## Operation Categories

Operations are pure descriptions of computation. Categories:

### Linear Operations

Matrix/tensor multiplication operations.

| Operation | Shape Transform | Description |
|-----------|-----------------|-------------|
| `MatMul` | [B,M,K] × [B,K,N] → [B,M,N] | Matrix multiplication |
| `Linear { outFeatures, bias }` | [B,in] → [B,out] | Fully connected layer |
| `Conv1D params` | [B,Cin,L] → [B,Cout,Lout] | 1D convolution |
| `Conv2D params` | [B,Cin,H,W] → [B,Cout,Hout,Wout] | 2D convolution |
| `Conv3D params` | [B,Cin,D,H,W] → [B,Cout,Dout,Hout,Wout] | 3D convolution |

### Elementwise Operations

Apply independently to each element (preserve shape).

| Operation | Formula | Description |
|-----------|---------|-------------|
| `Add` | a + b | Addition |
| `Mul` | a × b | Multiplication |
| `Sub` | a - b | Subtraction |
| `Div` | a / b | Division |
| `Neg` | -x | Negation |
| `Abs` | \|x\| | Absolute value |
| `Sqrt` | √x | Square root |
| `Exp` | eˣ | Exponential |
| `Log` | ln(x) | Natural logarithm |

### Activation Functions

| Operation | Formula | Notes |
|-----------|---------|-------|
| `Activation ReLU` | max(0, x) | Classic activation |
| `Activation GELU` | x × Φ(x) | Transformer default |
| `Activation SiLU` | x × σ(x) | Also called Swish |
| `Activation Sigmoid` | 1/(1+e⁻ˣ) | Logistic function |
| `Activation Tanh` | tanh(x) | Hyperbolic tangent |
| `Softmax { axis }` | exp(x)/Σexp(x) | Probability distribution |
| `Activation (LeakyReLU { negativeSlope })` | max(αx, x) | Leaky ReLU |

### Normalization

| Operation | Description | Use Case |
|-----------|-------------|----------|
| `LayerNorm params` | Normalize across features | Transformers |
| `BatchNorm params` | Normalize across batch | CNNs |
| `GroupNorm params` | Normalize across channel groups | Small batches |
| `RMSNorm params` | LayerNorm without mean centering | LLaMA, efficient transformers |

### Attention

| Operation | Formula | Description |
|-----------|---------|-------------|
| `ScaledDotProductAttention params` | softmax(QKᵀ/√d)V | Core attention |
| `MultiHeadAttention params` | Concat(head₁,...,headₙ)Wₒ | Multi-head variant |
| `FlashAttention params` | Fused kernel | Memory-efficient |

### Shape Operations

| Operation | Description |
|-----------|-------------|
| `Reshape { targetShape }` | Change shape (element count preserved) |
| `Transpose { axes }` | Permute dimensions |
| `Concat { axis }` | Concatenate along axis |
| `Split { axis, numSplits }` | Split along axis |
| `Broadcast { targetShape }` | Expand to target shape |
| `Squeeze { axes }` | Remove size-1 dimensions |
| `Unsqueeze { axes }` | Add size-1 dimensions |
| `Permute { perm }` | Reorder dimensions |

### Reduction Operations

| Operation | Description |
|-----------|-------------|
| `ReduceSum { axes, keepDims }` | Sum along axes |
| `ReduceMean { axes, keepDims }` | Mean along axes |
| `ReduceMax { axes, keepDims }` | Maximum along axes |
| `ReduceMin { axes, keepDims }` | Minimum along axes |

────────────────────────────────────────────────────────────────────────────────
                                                         // operation // params
────────────────────────────────────────────────────────────────────────────────

## ConvParams

```purescript
type ConvParams =
  { kernelSize :: Array Int
  , stride :: Array Int
  , padding :: Array Int
  , dilation :: Array Int
  , groups :: Int
  }
```

**Default:** `defaultConvParams spatialDims` (3×3 kernel, stride 1, padding 1)

## AttentionParams

```purescript
type AttentionParams =
  { numHeads :: Int
  , headDim :: Int
  , dropout :: Number
  , causal :: Boolean
  , scale :: Maybe Number
  }
```

**Default:** `defaultAttentionParams numHeads headDim`

## NormParams

```purescript
type NormParams =
  { eps :: Number
  , affine :: Boolean
  , numGroups :: Maybe Int
  }
```

**Default:** `defaultNormParams` (eps=1e-5, affine=true)

────────────────────────────────────────────────────────────────────────────────
                                                       // operation // properties
────────────────────────────────────────────────────────────────────────────────

## Operation Classification

| Function | Description |
|----------|-------------|
| `isElementwise op` | Does op apply independently to each element? |
| `isLinear op` | Does op involve matrix multiplication? |
| `isReduction op` | Does op reduce dimensions? |
| `requiresTraining op` | Does op behave differently in training vs inference? |
| `operationName op` | Human-readable name |

## Shape Inference

| Function | Description |
|----------|-------------|
| `inferOutputShape op inputs` | Infer output shape from operation and inputs |
| `checkInputShapes op inputs` | Validate input shapes for operation |

**inferOutputShape** returns `Maybe Shape`:
- `Just shape` if shapes are compatible
- `Nothing` if shapes are incompatible

────────────────────────────────────────────────────────────────────────────────
                                                              // source // files
────────────────────────────────────────────────────────────────────────────────

```
src/Hydrogen/Schema/Compute/
├── Graph.purs               # Leader module (95 lines)
├── Graph/
│   ├── Types.purs           # Core types and construction (270 lines)
│   └── Traversal.purs       # Traversal, validation, subgraphs (429 lines)
└── Operation.purs           # ML operations vocabulary (649 lines)
```

4 files, ~1,443 lines total.

────────────────────────────────────────────────────────────────────────────────
                                                         // design // philosophy
────────────────────────────────────────────────────────────────────────────────

## Why Compute Graphs Matter

At billion-agent scale, ML inference must be:

1. **Deterministic**: Same graph + same inputs = same outputs
2. **Verifiable**: Shape/dtype validation before execution
3. **Composable**: Graphs can be merged, subgraphed, inlined
4. **Hardware-agnostic**: Pure data, execution happens elsewhere

## Graph as Pure Data

The Graph type is a complete description of an ML model:
- No hidden state
- No side effects
- Serializable (CBOR/JSON)
- Comparable (equality check)

**An agent can:**
- Receive a graph from another agent
- Validate it completely (`validateGraph`)
- Compose it with other graphs (`merge`)
- Execute it on any hardware target

## Operations as Vocabulary

The Operation type is a **closed vocabulary** of ML primitives:
- Every operation has well-defined semantics
- Shape inference is deterministic
- No escape hatches (no "custom" operations)

This enables:
- Static optimization passes
- Automatic differentiation
- Hardware-specific compilation
- Cross-agent model sharing

────────────────────────────────────────────────────────────────────────────────
                                                                 // usage example
────────────────────────────────────────────────────────────────────────────────

## Building a Simple MLP

```purescript
import Hydrogen.Schema.Compute.Graph as G
import Hydrogen.Schema.Compute.Operation as Op

-- Build a 2-layer MLP: input -> linear -> relu -> linear -> output
buildMLP :: Int -> Int -> Int -> G.Graph
buildMLP inputDim hiddenDim outputDim =
  let
    g0 = G.emptyGraph "mlp"
    
    -- Add first linear layer
    { graph: g1, nodeId: linear1 } = G.addNode
      (Op.linear hiddenDim true)
      [{ name: "x", shape: inputShape, dtype: Float32 }]
      [{ name: "h", shape: hiddenShape, dtype: Float32 }]
      (Just "linear1")
      g0
    
    -- Add ReLU activation
    { graph: g2, nodeId: relu1 } = G.addNode
      Op.relu
      [{ name: "h", shape: hiddenShape, dtype: Float32 }]
      [{ name: "a", shape: hiddenShape, dtype: Float32 }]
      (Just "relu1")
      g1
    
    -- Connect linear1 -> relu1
    g3 = G.addEdge { nodeId: linear1, outputIndex: 0 } relu1 0 g2
    
    -- ... continue building
  in
    g3
```

────────────────────────────────────────────────────────────────────────────────
