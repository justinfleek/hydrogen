━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                                 // 28 // tensor
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Tensor Pillar

DType, shape, layout, and dimensions for machine learning tensors.

────────────────────────────────────────────────────────────────────────────────
                                                                    // overview
────────────────────────────────────────────────────────────────────────────────

## Implementation

- **Location**: `src/Hydrogen/Schema/Tensor/`
- **Files**: 8 modules (4 core + 4 DType submodules)
- **Lines**: 2,590 total
- **Key features**: Data types (FP32→FP4), dimensions, shapes, memory layouts,
  quantization modes, broadcasting, stride algebra

## Purpose

Tensor provides bounded, deterministic primitives for:
- Data type specification (IEEE floats, NVIDIA FP8/FP4, integer quantization)
- Dimension atoms (strictly positive integers with symbolic variants)
- Shape molecules (N-dimensional arrays of dimensions)
- Memory layout (NCHW/NHWC, row/column-major, strides)
- Quantization modes (W8A8, W4A16, NVFP4, MXFP4)
- Broadcasting and reshape validation

## Module Structure

```
Tensor/
├── DType.purs           -- Leader module (re-exports submodules)
├── DType/
│   ├── Types.purs       -- Core FloatFormat, IntFormat, DType
│   ├── Properties.purs  -- Bit width, classification queries
│   ├── Operations.purs  -- Casting, precision comparison
│   └── QuantMode.purs   -- Quantization mode specifications
├── Dimension.purs       -- Dim, DimVar, DimExpr atoms
├── Shape.purs           -- Shape molecule, broadcasting
└── Layout.purs          -- Memory layout, strides, named layouts
```

## Design Philosophy

At billion-agent scale, tensor specifications must be:
- **Bounded**: No unbounded integers that overflow
- **Deterministic**: Same specification → same memory layout
- **Composable**: Shapes compose via broadcasting, layouts via strides
- **Hardware-aware**: Support for cutting-edge quantization (Blackwell FP4)

────────────────────────────────────────────────────────────────────────────────
                                                              // dtype // atoms
────────────────────────────────────────────────────────────────────────────────

## DType Atoms

Tensor element data types define how individual values are stored and computed.

### FloatFormat

IEEE and NVIDIA floating-point format specification.

| Constructor | Sign | Exp | Mantissa | Total | Notes |
|-------------|------|-----|----------|-------|-------|
| `IEEE_FP32` | 1 | 8 | 23 | 32 | Standard float |
| `IEEE_FP16` | 1 | 5 | 10 | 16 | Half precision |
| `BF16` | 1 | 8 | 7 | 16 | Brain float (wider range than FP16) |
| `FP8_E4M3` | 1 | 4 | 3 | 8 | NVIDIA FP8, higher precision |
| `FP8_E5M2` | 1 | 5 | 2 | 8 | NVIDIA FP8, wider range |
| `FP4_E2M1` | 1 | 2 | 1 | 4 | NVFP4, no Inf/NaN |
| `MXFP4_E2M1` | 1 | 2 | 1 | 4 | Microscaling FP4 |

**FP8 variants explained:**
- `FP8_E4M3`: Preferred for **inference** — 4 exponent bits give adequate range,
  3 mantissa bits provide better precision for weight storage
- `FP8_E5M2`: Preferred for **training gradients** — 5 exponent bits handle the
  wider dynamic range of gradients during backpropagation

**FP4 variants explained:**
- `FP4_E2M1` (NVFP4): 4-bit float with **no infinity or NaN representations**.
  All 16 bit patterns represent finite values. Used in TensorRT-LLM for
  extreme weight compression.
- `MXFP4_E2M1`: Like NVFP4 but with block-level scaling factors. Each block
  (typically 32-128 elements) shares a higher-precision scale, improving
  effective precision while maintaining 4-bit storage.

### IntFormat

Integer format specification for quantized tensors.

| Constructor | Bits | Signed | Range | Notes |
|-------------|------|--------|-------|-------|
| `Int4Signed` | 4 | Yes | -8 to 7 | Weight quantization |
| `Int4Unsigned` | 4 | No | 0 to 15 | Rare, mostly weights |
| `Int8Signed` | 8 | Yes | -128 to 127 | Common activation quant |
| `Int8Unsigned` | 8 | No | 0 to 255 | Image preprocessing |
| `Int16Signed` | 16 | Yes | -32768 to 32767 | Audio, accumulation |
| `Int32Signed` | 32 | Yes | Full 32-bit | Indices, accumulation |
| `Int64Signed` | 64 | Yes | Full 64-bit | Large indices |
| `Bool` | 1 | No | 0 or 1 | Masks (typically 8-bit storage) |

### QuantFormat

Quantization scale granularity specification.

| Constructor | Parameters | Description |
|-------------|------------|-------------|
| `PerTensor` | — | Single scale for entire tensor |
| `PerChannel` | — | Scale per output channel |
| `PerGroup` | `{ groupSize :: Int }` | Scale per group of elements |
| `PerBlock` | `{ blockSize :: Int }` | Microscaling block-level |

**Trade-offs:**
- `PerTensor`: Fastest inference, lowest memory, lowest accuracy
- `PerChannel`: Standard for weight quantization
- `PerGroup`: AWQ/GPTQ style (group size typically 128)
- `PerBlock`: MXFP4 style (block size typically 32)

────────────────────────────────────────────────────────────────────────────────
                                                          // dtype // molecules
────────────────────────────────────────────────────────────────────────────────

## DType Molecule

The unified tensor element type, composed from format atoms.

```purescript
data DType
  = FloatType FloatFormat
  | IntType IntFormat
  | QuantizedType
      { baseType :: DType
      , quantFormat :: QuantFormat
      }
```

### Smart Constructors

| Function | Return Type | Description |
|----------|-------------|-------------|
| `float32` | `DType` | 32-bit IEEE float |
| `float16` | `DType` | 16-bit IEEE half |
| `bfloat16` | `DType` | 16-bit brain float |
| `fp8e4m3` | `DType` | 8-bit E4M3 (inference) |
| `fp8e5m2` | `DType` | 8-bit E5M2 (gradients) |
| `nvfp4` | `DType` | NVIDIA 4-bit float |
| `mxfp4` | `DType` | Microscaling 4-bit float |
| `int8` | `DType` | 8-bit signed integer |
| `uint8` | `DType` | 8-bit unsigned integer |
| `int4` | `DType` | 4-bit signed integer |
| `int32` | `DType` | 32-bit signed integer |
| `int64` | `DType` | 64-bit signed integer |
| `bool` | `DType` | Boolean type |

### Quantized DType Example

```purescript
-- INT8 weights with per-channel scaling
quantizedWeights :: DType
quantizedWeights = QuantizedType
  { baseType: int8
  , quantFormat: PerChannel
  }

-- NVFP4 weights with block-level microscaling
nvfp4Weights :: DType
nvfp4Weights = QuantizedType
  { baseType: nvfp4
  , quantFormat: PerBlock { blockSize: 32 }
  }
```

────────────────────────────────────────────────────────────────────────────────
                                                       // dtype // properties
────────────────────────────────────────────────────────────────────────────────

## DType Properties

Query functions for tensor element types.

### Bit Width

| Function | Type | Description |
|----------|------|-------------|
| `bitWidth` | `DType -> Int` | Bits per element |
| `byteWidth` | `DType -> Int` | Bytes per element (rounded up) |

**Examples:**
```purescript
bitWidth float32  -- 32
bitWidth nvfp4    -- 4
byteWidth int4    -- 1 (sub-byte types round up)
```

### Type Classification

| Function | Type | Description |
|----------|------|-------------|
| `isFloatingPoint` | `DType -> Boolean` | True for all float types |
| `isInteger` | `DType -> Boolean` | True for all int types |
| `isQuantized` | `DType -> Boolean` | True for QuantizedType |
| `isSigned` | `DType -> Boolean` | True for signed types |
| `isNumeric` | `DType -> Boolean` | True for non-boolean types |

### Format Details

| Function | Type | Description |
|----------|------|-------------|
| `hasInfNaN` | `DType -> Boolean` | Supports Inf/NaN? |
| `exponentBits` | `DType -> Int` | Exponent bit count (0 for ints) |
| `mantissaBits` | `DType -> Int` | Mantissa bit count (0 for ints) |

**Key insight:** `hasInfNaN` returns `false` for NVFP4/MXFP4 — these formats
use all bit patterns for finite values.

### Memory Calculation

| Function | Type | Description |
|----------|------|-------------|
| `elementsPerByte` | `DType -> Int` | How many elements fit in 1 byte |
| `bytesForElements` | `DType -> Int -> Int` | Bytes needed for N elements |

**Examples:**
```purescript
elementsPerByte int4       -- 2 (two 4-bit values per byte)
bytesForElements int4 10   -- 5 bytes for 10 INT4 elements
bytesForElements float32 10 -- 40 bytes
```

────────────────────────────────────────────────────────────────────────────────
                                                        // dtype // operations
────────────────────────────────────────────────────────────────────────────────

## DType Operations

Comparison, casting, and transformation functions.

### Precision Comparison

| Function | Type | Description |
|----------|------|-------------|
| `higherPrecision` | `DType -> DType -> Boolean` | First has more bits? |
| `lowerPrecision` | `DType -> DType -> Boolean` | First has fewer bits? |
| `canCastTo` | `DType -> DType -> Boolean` | Safe cast (no data loss)? |
| `commonType` | `DType -> DType -> Maybe DType` | Broadcast result type |

**Casting rules:**
- Float to larger float: Safe
- Int to larger int: Safe
- Int to float (if int ≤ 24 bits and float ≥ 32 bits): Safe
- Everything else: Potentially lossy

### Transformation

| Function | Type | Description |
|----------|------|-------------|
| `promoteTo` | `Int -> DType -> Maybe DType` | Promote to min bit width |
| `mapBaseType` | `(DType -> DType) -> DType -> DType` | Map over quantized base |
| `describeType` | `DType -> String` | Human-readable description |

**Example:**
```purescript
describeType float16  -- "16-bit signed float"
describeType int8     -- "8-bit signed integer"
```

────────────────────────────────────────────────────────────────────────────────
                                                            // quantmode // enum
────────────────────────────────────────────────────────────────────────────────

## QuantMode Enum

Quantization modes from TensorRT-LLM `quantization.mode.QuantAlgo`.

| Constructor | Weight Type | Activation Type | Description |
|-------------|-------------|-----------------|-------------|
| `NoQuant` | FP16 | FP16 | No quantization |
| `W8A8_SQ` | INT8 | INT8 | SmoothQuant |
| `W8A16` | INT8 | FP16 | INT8 weights only |
| `W4A16` | INT4 | FP16 | INT4 weights only |
| `W4A16_AWQ` | INT4 | FP16 | Activation-aware Weight Quant |
| `W4A16_GPTQ` | INT4 | FP16 | GPTQ quantization |
| `FP8_Linear` | FP8_E4M3 | FP8_E4M3 | FP8 linear layers only |
| `FP8_Full` | FP8_E4M3 | FP8_E4M3 | FP8 all operations |
| `W4A8_NVFP4_FP8` | NVFP4 | FP8_E4M3 | Blackwell 4-bit |
| `W4A8_MXFP4_FP8` | MXFP4 | FP8_E4M3 | Blackwell microscaling |
| `W8A8_FP8` | FP8_E4M3 | FP8_E4M3 | FP8 weights and activations |

### Nomenclature

**W{bits}A{bits}** means:
- W = Weights at `{bits}` precision
- A = Activations at `{bits}` precision

### Hardware Support

| Hardware | Supported Modes |
|----------|-----------------|
| Blackwell (B200) | All modes including NVFP4/MXFP4 |
| Hopper (H100) | FP8, INT8, INT4 (no NVFP4) |
| Ampere (A100) | INT8, INT4 only |
| Older (V100, etc.) | INT8 only |

### Smart Constructors

| Function | Mode | Description |
|----------|------|-------------|
| `quantNone` | `NoQuant` | No quantization |
| `quantW8A8` | `W8A8_SQ` | SmoothQuant INT8 |
| `quantW4A16` | `W4A16` | INT4 weights |
| `quantW4A8NVFP4` | `W4A8_NVFP4_FP8` | NVIDIA 4-bit |
| `quantW4A8MXFP4` | `W4A8_MXFP4_FP8` | Microscaling 4-bit |
| `quantFP8` | `FP8_Full` | Full FP8 |

### Properties

| Function | Type | Description |
|----------|------|-------------|
| `requiresScaling` | `QuantMode -> Boolean` | Needs scale factors? |
| `weightDType` | `QuantMode -> DType` | Weight storage type |
| `activationDType` | `QuantMode -> DType` | Activation storage type |
| `supportedQuantModes` | `String -> Array QuantMode` | Modes for hardware |

────────────────────────────────────────────────────────────────────────────────
                                                          // dimension // atoms
────────────────────────────────────────────────────────────────────────────────

## Dimension Atoms

Bounded positive integers for tensor dimensions.

### Dim

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Dim | Int | 1 | 1,073,741,824 | clamps | 2^30 max (4GB per axis) |

**Key invariant:** Tensor dimensions are **strictly positive**. A dimension of 0
or negative is meaningless and cannot be constructed.

```purescript
newtype Dim = Dim Int

-- Smart constructor clamps to [1, 2^30]
dim :: Int -> Dim
dim n = Dim (clamp 1 1073741824 n)

dim 64    -- Dim 64
dim 0     -- Dim 1 (clamped)
dim (-5)  -- Dim 1 (clamped)
```

### DimVar

Symbolic dimension variable for dynamic shapes.

```purescript
newtype DimVar = DimVar String

dimVar "batch"     -- Variable batch dimension
dimVar "seq_len"   -- Variable sequence length
```

### DimExpr

Dimension expression combining concrete and symbolic values.

```purescript
data DimExpr
  = DimLit Dim           -- Concrete: 768
  | DimSym DimVar        -- Symbolic: batch
  | DimMul DimExpr DimExpr  -- Product: batch * 4
  | DimDiv DimExpr DimExpr  -- Division: total / heads
  | DimAdd DimExpr DimExpr  -- Sum: seq1 + seq2
```

**Use case:** Representing shapes like `[batch, 77, 768]` where batch is
determined at runtime.

────────────────────────────────────────────────────────────────────────────────
                                                       // dimension // presets
────────────────────────────────────────────────────────────────────────────────

## Common Dimension Presets

### Small Dimensions

| Name | Value | Use Case |
|------|-------|----------|
| `dim1` | 1 | Scalar/singleton |
| `dim2` | 2 | Stereo audio, 2D coords |
| `dim3` | 3 | RGB channels |
| `dim4` | 4 | RGBA/latent channels |

### Powers of 2

| Name | Value | Use Case |
|------|-------|----------|
| `dim8` | 8 | Attention heads |
| `dim16` | 16 | Small feature maps |
| `dim32` | 32 | Feature maps |
| `dim64` | 64 | Common spatial/channel |
| `dim128` | 128 | Common channel |
| `dim256` | 256 | Common channel |
| `dim512` | 512 | Common spatial/channel |
| `dim1024` | 1024 | Large spatial/channel |

### Sequence Lengths (Transformers)

| Name | Value | Use Case |
|------|-------|----------|
| `dimSeq77` | 77 | CLIP text encoder |
| `dimSeq512` | 512 | BERT default |
| `dimSeq1024` | 1024 | Extended context |
| `dimSeq2048` | 2048 | Long context |

### Embedding Dimensions

| Name | Value | Use Case |
|------|-------|----------|
| `dimEmbed320` | 320 | SD 1.x base |
| `dimEmbed640` | 640 | SD intermediate |
| `dimEmbed768` | 768 | CLIP, BERT base |
| `dimEmbed1024` | 1024 | Larger models |
| `dimEmbed1280` | 1280 | SD 2.x, SDXL |

### Channel Dimensions

| Name | Value | Use Case |
|------|-------|----------|
| `dimRGB` | 3 | RGB image |
| `dimRGBA` | 4 | RGBA image |
| `dimLatent4` | 4 | SD latent space |

### Symbolic Variables

| Name | String | Use Case |
|------|--------|----------|
| `dimBatch` | "batch" | Dynamic batch size |

────────────────────────────────────────────────────────────────────────────────
                                                     // dimension // operations
────────────────────────────────────────────────────────────────────────────────

## Dimension Operations

All operations preserve positivity where possible.

### Arithmetic

| Function | Type | Description |
|----------|------|-------------|
| `mulDim` | `Dim -> Dim -> Dim` | Multiply (always valid) |
| `divDim` | `Dim -> Dim -> Maybe Dim` | Divide (fails if not evenly divisible) |
| `addDim` | `Dim -> Dim -> Dim` | Add (always valid) |
| `subDim` | `Dim -> Dim -> Maybe Dim` | Subtract (fails if result <= 0) |

**Key insight:** `divDim` returns `Nothing` if the division isn't exact. This
enforces that reshapes preserve total element count.

### Queries

| Function | Type | Description |
|----------|------|-------------|
| `isPowerOf2` | `Dim -> Boolean` | Is this 2^n? |
| `log2Dim` | `Dim -> Maybe Int` | Log2 (fails if not power of 2) |
| `isOne` | `Dim -> Boolean` | Is this dimension 1? |
| `isDivisibleBy` | `Dim -> Dim -> Boolean` | First divisible by second? |
| `inRange` | `Dim -> Dim -> Dim -> Boolean` | Is value in [min, max]? |
| `minDim` | `Dim -> Dim -> Dim` | Minimum of two |
| `maxDim` | `Dim -> Dim -> Dim` | Maximum of two |

### DimExpr Operations

| Function | Type | Description |
|----------|------|-------------|
| `evalDimExpr` | `(DimVar -> Maybe Dim) -> DimExpr -> Maybe Dim` | Evaluate with bindings |
| `simplifyDimExpr` | `DimExpr -> DimExpr` | Simplify where possible |
| `mapDimExpr` | `(Dim -> Dim) -> DimExpr -> DimExpr` | Map over literals |
| `dimExprToString` | `DimExpr -> String` | Pretty print |

**Example:**
```purescript
-- Shape: [batch, 77, 768]
shapeExpr = ShapeExpr
  [ DimSym dimBatch
  , DimLit dimSeq77
  , DimLit dimEmbed768
  ]

-- Evaluate with batch=4
env v = if v == dimBatch then Just (dim 4) else Nothing
evalDimExpr env (DimSym dimBatch)  -- Just (Dim 4)
```

────────────────────────────────────────────────────────────────────────────────
                                                             // shape // molecule
────────────────────────────────────────────────────────────────────────────────

## Shape Molecule

Tensor shape — an ordered array of dimensions.

```purescript
newtype Shape = Shape (Array Dim)
newtype ShapeExpr = ShapeExpr (Array DimExpr)
```

### Constructors

| Function | Type | Description |
|----------|------|-------------|
| `scalar` | `Shape` | 0D tensor (1 element) |
| `shape1d` | `Dim -> Shape` | 1D tensor |
| `shape2d` | `Dim -> Dim -> Shape` | 2D tensor (matrix) |
| `shape3d` | `Dim -> Dim -> Dim -> Shape` | 3D tensor |
| `shape4d` | `Dim -> Dim -> Dim -> Dim -> Shape` | 4D tensor (images) |
| `shape5d` | `Dim -> Dim -> Dim -> Dim -> Dim -> Shape` | 5D tensor (video) |
| `shapeFromArray` | `Array Dim -> Shape` | From array |
| `shapeExprFromArray` | `Array DimExpr -> ShapeExpr` | Symbolic shape |

### Accessors

| Function | Type | Description |
|----------|------|-------------|
| `rank` | `Shape -> Int` | Number of dimensions |
| `dims` | `Shape -> Array Dim` | All dimensions |
| `dimAt` | `Int -> Shape -> Maybe Dim` | Dimension at index |
| `firstDim` | `Shape -> Maybe Dim` | First (usually batch) |
| `lastDim` | `Shape -> Maybe Dim` | Last (usually features) |

### Element Count

| Function | Type | Description |
|----------|------|-------------|
| `numel` | `Shape -> Dim` | Total elements (product of dims) |
| `numelExpr` | `ShapeExpr -> DimExpr` | Symbolic element count |

**Examples:**
```purescript
numel (shape2d dim3 dim4)  -- Dim 12
numel scalar               -- Dim 1
```

────────────────────────────────────────────────────────────────────────────────
                                                       // shape // operations
────────────────────────────────────────────────────────────────────────────────

## Shape Operations

### Manipulation

| Function | Type | Description |
|----------|------|-------------|
| `concat` | `Shape -> Shape -> Shape` | Concatenate dimension lists |
| `slice` | `Int -> Int -> Shape -> Shape` | Slice dimensions |
| `take` | `Int -> Shape -> Shape` | Take first N dimensions |
| `drop` | `Int -> Shape -> Shape` | Drop first N dimensions |
| `reverse` | `Shape -> Shape` | Reverse dimension order |
| `squeeze` | `Shape -> Shape` | Remove size-1 dimensions |
| `unsqueeze` | `Int -> Shape -> Shape` | Insert size-1 dimension |
| `flatten` | `Shape -> Shape` | Collapse to 1D |

**Examples:**
```purescript
squeeze (shape4d dim1 dim3 dim1 dim4)  -- [3, 4]
unsqueeze 0 (shape2d dim3 dim4)        -- [1, 3, 4]
flatten (shape3d dim2 dim3 dim4)       -- [24]
```

### Reshape

| Function | Type | Description |
|----------|------|-------------|
| `reshape` | `Shape -> Shape -> Maybe Shape` | Reshape (must preserve numel) |
| `canReshape` | `Shape -> Shape -> Boolean` | Is reshape valid? |
| `inferDim` | `Shape -> Array Int -> Maybe Shape` | Infer -1 placeholder |

**Reshape rule:** `numel src == numel target` must hold.

**Infer example:**
```purescript
-- [2, 3, 4] has 24 elements
-- [6, -1] should become [6, 4]
inferDim (shape3d dim2 dim3 dim4) [6, -1]  -- Just [6, 4]
```

### Broadcasting

NumPy-style broadcasting for compatible shapes.

| Function | Type | Description |
|----------|------|-------------|
| `broadcast` | `Shape -> Shape -> Maybe Shape` | Broadcast shapes |
| `canBroadcast` | `Shape -> Shape -> Boolean` | Are shapes compatible? |
| `broadcastShapes` | `Shape -> Shape -> Maybe Shape` | Compute result shape |

**Broadcasting rules:**
1. Shapes are aligned from the right
2. Dimensions are compatible if equal or one is 1
3. Missing dimensions are treated as 1

**Examples:**
```purescript
broadcast [3] [2, 3]        -- Just [2, 3]
broadcast [1, 3] [2, 3]     -- Just [2, 3]
broadcast [2] [3]           -- Nothing (incompatible)
broadcast [4, 1, 3] [5, 3]  -- Just [4, 5, 3]
```

────────────────────────────────────────────────────────────────────────────────
                                                          // shape // presets
────────────────────────────────────────────────────────────────────────────────

## Common Shape Presets

### Image Shapes

| Function | Parameters | Layout | Description |
|----------|------------|--------|-------------|
| `shapeNCHW` | N, C, H, W | PyTorch | Batch, Channels, Height, Width |
| `shapeNHWC` | N, H, W, C | TensorFlow | Batch, Height, Width, Channels |

### Sequence Shapes

| Function | Parameters | Description |
|----------|------------|-------------|
| `shapeNLC` | N, L, C | Batch, Length, Channels |
| `shapeNLCH` | N, L, C, H | Multi-head attention intermediate |
| `shapeBatchSeqEmbed` | batch, seq, embed | Standard transformer input |

### Diffusion Model Shapes

```purescript
-- SD latent: [batch, 4, H/8, W/8]
sdLatent = shapeNCHW dim1 dimLatent4 dim64 dim64

-- CLIP text embedding: [batch, 77, 768]
clipEmbed = shapeBatchSeqEmbed dim1 dimSeq77 dimEmbed768

-- UNet input: [batch, 320, 64, 64]
unetInput = shapeNCHW dim1 dimEmbed320 dim64 dim64
```

────────────────────────────────────────────────────────────────────────────────
                                                        // shape // validation
────────────────────────────────────────────────────────────────────────────────

## Shape Validation

### Comparison

| Function | Type | Description |
|----------|------|-------------|
| `isScalar` | `Shape -> Boolean` | Is rank 0? |
| `is1d` | `Shape -> Boolean` | Is rank 1? |
| `is2d` | `Shape -> Boolean` | Is rank 2? |
| `is3d` | `Shape -> Boolean` | Is rank 3? |
| `is4d` | `Shape -> Boolean` | Is rank 4? |
| `sameRank` | `Shape -> Shape -> Boolean` | Same number of dims? |
| `sameShape` | `Shape -> Shape -> Boolean` | Identical shapes? |

### Operation Validation

| Function | Type | Description |
|----------|------|-------------|
| `isValidMatmul` | `Shape -> Shape -> Boolean` | Valid for matmul? |
| `isValidConcat` | `Int -> Shape -> Shape -> Boolean` | Valid for concat on axis? |
| `totalRank` | `Array Shape -> Int` | Sum of all ranks |

**Matmul rule:** Last dim of A must equal second-to-last dim of B.

```purescript
-- [2, 3, 4] x [2, 4, 5] -> valid (4 == 4)
isValidMatmul (shape3d dim2 dim3 dim4) (shape3d dim2 dim4 dim5)  -- true

-- [2, 3, 4] x [2, 3, 5] -> invalid (4 /= 3)
isValidMatmul (shape3d dim2 dim3 dim4) (shape3d dim2 dim3 dim5)  -- false
```

────────────────────────────────────────────────────────────────────────────────
                                                             // layout // atoms
────────────────────────────────────────────────────────────────────────────────

## Layout Atoms

Memory layout primitives for tensor storage.

### MemoryOrder

| Constructor | Description | Index Behavior |
|-------------|-------------|----------------|
| `RowMajor` | C-style | Last index varies fastest |
| `ColumnMajor` | Fortran-style | First index varies fastest |

**Practical impact:**
- Row-major: `a[i][j+1]` is adjacent to `a[i][j]` in memory
- Column-major: `a[i+1][j]` is adjacent to `a[i][j]` in memory

### Stride

Number of elements to skip when incrementing an index.

```purescript
newtype Stride = Stride Int

-- Stride 0 indicates broadcasting (same value repeated)
```

────────────────────────────────────────────────────────────────────────────────
                                                          // layout // molecule
────────────────────────────────────────────────────────────────────────────────

## Layout Molecule

Complete tensor memory layout specification.

```purescript
data Layout
  = Contiguous
      { shape :: Array Dim
      , order :: MemoryOrder
      }
  | Strided
      { shape :: Array Dim
      , strides :: Array Stride
      }
  | Named
      { shape :: Array Dim
      , strides :: Array Stride
      , dimNames :: Array String
      }
```

### Constructors

| Function | Type | Description |
|----------|------|-------------|
| `contiguous` | `Array Dim -> MemoryOrder -> Layout` | Packed layout |
| `strided` | `Array Dim -> Array Stride -> Layout` | Explicit strides |
| `broadcasted` | `Array Dim -> Array Dim -> Layout` | Broadcast layout |

────────────────────────────────────────────────────────────────────────────────
                                                          // layout // presets
────────────────────────────────────────────────────────────────────────────────

## Named Layout Presets

### Image Layouts

| Function | Dim Names | Default Framework |
|----------|-----------|-------------------|
| `nchw` | N, C, H, W | PyTorch, cuDNN, TensorRT |
| `nhwc` | N, H, W, C | TensorFlow, ONNX Runtime |
| `chwn` | C, H, W, N | Some accelerators |
| `nwhc` | N, W, H, C | Transposed spatial |

**Framework notes:**
- PyTorch defaults to NCHW (channel-first)
- TensorFlow defaults to NHWC (channel-last)
- cuDNN supports both but NCHW is often faster on NVIDIA GPUs
- TensorRT can optimize both layouts

### Sequence Layouts

| Function | Dim Names | Use Case |
|----------|-----------|----------|
| `nlc` | N, L, C | Transformers, most sequence models |
| `ncl` | N, C, L | Some Conv1d operations |
| `lnc` | L, N, C | Some RNN implementations |

**Examples:**
```purescript
-- NCHW layout for 4 images, 3 channels, 64x64
imageLayout = nchw dim4 dimRGB dim64 dim64

-- NLC layout for batch=1, seq=77, embed=768
textLayout = nlc dim1 dimSeq77 dimEmbed768
```

────────────────────────────────────────────────────────────────────────────────
                                                       // layout // properties
────────────────────────────────────────────────────────────────────────────────

## Layout Properties

### Classification

| Function | Type | Description |
|----------|------|-------------|
| `isContiguous` | `Layout -> Boolean` | No memory gaps? |
| `isBroadcasted` | `Layout -> Boolean` | Has stride-0 dimensions? |
| `isRowMajor` | `Layout -> Boolean` | C-style ordering? |
| `isColumnMajor` | `Layout -> Boolean` | Fortran-style ordering? |
| `memoryOrder` | `Layout -> MemoryOrder` | Get memory order |

### Stride Queries

| Function | Type | Description |
|----------|------|-------------|
| `stridesFor` | `Layout -> Array Stride` | Get stride array |
| `hasPositiveStrides` | `Layout -> Boolean` | All strides >= 0? |

────────────────────────────────────────────────────────────────────────────────
                                                       // layout // operations
────────────────────────────────────────────────────────────────────────────────

## Layout Operations

### Stride Computation

| Function | Type | Description |
|----------|------|-------------|
| `computeStrides` | `Array Dim -> MemoryOrder -> Array Stride` | Compute strides |
| `stridesFromDims` | `Array Dim -> MemoryOrder -> Array Stride` | Same as above |

**Row-major stride formula:**
```
stride[i] = product(shape[i+1:])
stride[last] = 1
```

**Column-major stride formula:**
```
stride[i] = product(shape[:i])
stride[0] = 1
```

**Example (shape [2, 3, 4]):**
```
Row-major:    [12, 4, 1]  -- 3x4=12, 4, 1
Column-major: [1, 2, 6]   -- 1, 2, 2x3=6
```

### Memory Access

| Function | Type | Description |
|----------|------|-------------|
| `offsetAt` | `Layout -> Array Int -> Int` | Memory offset for indices |
| `totalElements` | `Layout -> Dim` | Total element count |
| `effectiveShape` | `Layout -> Array Dim` | Shape without strides |

**Offset formula:**
```
offset = sum(index[i] * stride[i])
```

### Conversion

| Function | Type | Description |
|----------|------|-------------|
| `toRowMajor` | `Layout -> Layout` | Convert to row-major |
| `toColumnMajor` | `Layout -> Layout` | Convert to column-major |
| `transpose` | `Layout -> Maybe Layout` | Swap last two dims |
| `permute` | `Array Int -> Layout -> Maybe Layout` | Reorder dimensions |

**Transpose example:**
```purescript
-- NCHW -> NCWH (transpose H and W)
transpose (nchw dim1 dim3 dim64 dim64)
-- Result: strides swapped for last two dimensions
```

### Stride Manipulation

| Function | Type | Description |
|----------|------|-------------|
| `reverseStrides` | `Layout -> Layout` | Reverse stride order |
| `negateStrides` | `Layout -> Layout` | Negate all strides |

**Negative strides:** Enable backward iteration through memory.

────────────────────────────────────────────────────────────────────────────────
                                                // layout // memory // calculation
────────────────────────────────────────────────────────────────────────────────

## Memory Calculation

### Buffer Size

| Function | Type | Description |
|----------|------|-------------|
| `minBufferSize` | `Layout -> Int` | Minimum buffer (elements) |
| `fitsInBuffer` | `Int -> Layout -> Boolean` | Does layout fit? |
| `isOverlapping` | `Layout -> Boolean` | Do indices share memory? |

**minBufferSize formula:**
```
max((dim[i] - 1) * stride[i]) + 1
```

### Memory Efficiency

| Function | Type | Description |
|----------|------|-------------|
| `memoryEfficiency` | `Layout -> Number` | Ratio: used/allocated |

**Efficiency interpretation:**
- 1.0 = perfectly packed, no gaps
- <1.0 = has gaps (wasted memory)
- Broadcasted layouts typically have efficiency << 1.0

### Compatibility

| Function | Type | Description |
|----------|------|-------------|
| `isCompatibleWith` | `Layout -> Layout -> Boolean` | Same shape? |
| `canBroadcastTo` | `Layout -> Array Dim -> Boolean` | Can broadcast to target? |
| `requiresTranspose` | `Layout -> Layout -> Boolean` | Different strides for same shape? |

────────────────────────────────────────────────────────────────────────────────
                                                      // mathematical // formulas
────────────────────────────────────────────────────────────────────────────────

## Mathematical Formulas

### Memory Offset Calculation

For a tensor with shape `[d0, d1, ..., d(n-1)]` and strides `[s0, s1, ..., s(n-1)]`:

```
offset(i0, i1, ..., i(n-1)) = SUM_j (i_j * s_j)
```

### Row-Major Stride Computation

```
s(n-1) = 1
s_i = d(i+1) * s(i+1)   for i < n-1
```

Equivalently: `s_i = PRODUCT_{j=i+1}^{n-1} d_j`

### Column-Major Stride Computation

```
s_0 = 1
s_i = d(i-1) * s(i-1)   for i > 0
```

Equivalently: `s_i = PRODUCT_{j=0}^{i-1} d_j`

### Total Element Count

```
numel(shape) = PRODUCT_i d_i
```

For empty shape (scalar): `numel([]) = 1`

### Broadcasting Compatibility

Two dimensions are compatible if:
```
d1 == d2  OR  d1 == 1  OR  d2 == 1
```

Broadcast result dimension:
```
broadcast(d1, d2) = max(d1, d2)  if compatible
```

### Matmul Shape Computation

For A: `[..., m, k]` and B: `[..., k, n]`:
```
result: [..., m, n]
```

Batch dimensions must broadcast.

### Memory Efficiency

```
efficiency = numel(shape) / minBufferSize
           = PRODUCT_i d_i / (max((d_i - 1) * s_i) + 1)
```

────────────────────────────────────────────────────────────────────────────────
                                                        // design // philosophy
────────────────────────────────────────────────────────────────────────────────

## Design Philosophy

### Why Bounded Dimensions

Traditional tensor libraries use unbounded integers for dimensions:
```python
# Python/NumPy: No type-level bounds
tensor = np.zeros((999999999999, 999999999999))  # OOM crash
```

Hydrogen enforces bounds at construction:
```purescript
-- PureScript: Bounded at construction
dim 999999999999  -- Clamped to max 2^30
```

**At billion-agent scale**, unbounded dimensions cause:
- Memory exhaustion across swarms
- Inconsistent behavior between systems
- Unrecoverable failures in distributed training

### Why Symbolic Dimensions

Dynamic batch sizes are universal in ML:
```python
# Shape: [batch, 77, 768] where batch varies
```

Rather than defer to runtime entirely, Hydrogen captures structure:
```purescript
ShapeExpr
  [ DimSym dimBatch    -- Symbolic: resolved later
  , DimLit dimSeq77    -- Concrete: always 77
  , DimLit dimEmbed768 -- Concrete: always 768
  ]
```

**Benefits:**
- Type-level documentation of intent
- Static validation where possible
- Clear API contracts between agents

### Why Explicit Layouts

Memory layout is critical for performance but often implicit:
```python
# NumPy: Is this row-major or column-major?
a = np.array([[1,2],[3,4]])  # Default is row-major, but...
b = np.asfortranarray(a)     # Now column-major
```

Hydrogen makes layout explicit:
```purescript
-- Explicitly NCHW, row-major
layout = nchw dim1 dim3 dim64 dim64
isRowMajor layout  -- true
```

**At swarm scale**, implicit layouts cause:
- Transpose overhead when formats mismatch
- Silent correctness bugs
- Performance cliffs

### Why Named Dimensions

Anonymous dimensions are error-prone:
```python
# Which is batch? Which is channels?
tensor.shape  # (1, 3, 64, 64)
```

Named layouts are self-documenting:
```purescript
-- Named: no ambiguity
nchw dim1 dim3 dim64 dim64
-- dimNames: ["N", "C", "H", "W"]
```

### Why Hardware-Aware Quantization

Quantization varies dramatically by hardware generation:
- Blackwell: NVFP4, MXFP4, FP8
- Hopper: FP8, INT8, INT4
- Ampere: INT8, INT4
- Older: INT8 only

Hydrogen encodes this knowledge:
```purescript
supportedQuantModes "blackwell"  -- All modes
supportedQuantModes "hopper"     -- No NVFP4/MXFP4
```

**At scale**, deploying incompatible quantization to hardware causes:
- Silent fallback to slower kernels
- Memory budget violations
- Inference failures

────────────────────────────────────────────────────────────────────────────────
                                                                    // glossary
────────────────────────────────────────────────────────────────────────────────

## Glossary

| Term | Definition |
|------|------------|
| **BFloat16** | Brain float: 8 exp, 7 mantissa, wider range than FP16 |
| **Broadcasting** | Extending dimensions of size 1 to match other tensors |
| **Contiguous** | Memory layout with no gaps between elements |
| **DType** | Data type: how tensor elements are stored |
| **FBM** | Fractional Brownian Motion (see Surface pillar) |
| **FP8** | 8-bit floating point (NVIDIA format) |
| **FP4/NVFP4** | 4-bit floating point (NVIDIA Blackwell) |
| **GPTQ** | Post-training quantization method |
| **Layout** | Memory arrangement: shape + strides + order |
| **Microscaling** | Block-level scaling for sub-byte quantization |
| **MXFP4** | Microscaling FP4: block-level scales for better accuracy |
| **NCHW** | Batch, Channels, Height, Width (PyTorch default) |
| **NHWC** | Batch, Height, Width, Channels (TensorFlow default) |
| **Numel** | Number of elements in a tensor |
| **Quantization** | Reducing precision for efficiency |
| **Rank** | Number of dimensions in a tensor shape |
| **Shape** | Ordered list of dimension sizes |
| **SmoothQuant** | Quantization method for large language models |
| **Stride** | Elements to skip per index increment |
| **TensorRT-LLM** | NVIDIA's LLM inference library |

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                                    // // // //
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
