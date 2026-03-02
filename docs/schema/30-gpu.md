━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                                     // 30 // gpu
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# GPU Pillar

Landauer limits, entropy-based precision selection, and GPU-storable types.

────────────────────────────────────────────────────────────────────────────────
                                                                    // overview
────────────────────────────────────────────────────────────────────────────────

## Implementation

- **Location**: `src/Hydrogen/Schema/GPU/`
- **Files**: 8 modules
- **Lines**: 1,949 total
- **Key features**: Landauer entropy-based precision, GPU buffer serialization,
  thermodynamic cost computation, semantic type entropy bounds

## Module Structure

| Module | Lines | Description |
|--------|-------|-------------|
| `Landauer.purs` | 78 | Leader module, re-exports all Landauer submodules |
| `Landauer/Types.purs` | 204 | Core types: Entropy, NaturalPrecision, LandauerCost |
| `Landauer/Internal.purs` | 85 | Internal constructors for sibling module access |
| `Landauer/Tolerance.purs` | 177 | Distortion tolerance and dual sensitivity |
| `Landauer/Format.purs` | 87 | Hardware precision formats |
| `Landauer/Semantic.purs` | 117 | Semantic types and information bundles |
| `Landauer/Domain.purs` | 144 | Domain boundaries and gauge transformations |
| `Storable.purs` | 1,057 | GPUStorable typeclass and instances |

## Purpose

The GPU pillar provides bounded, deterministic primitives for:

1. **Entropy-based precision selection** — Precision as a physical quantity, not
   a hyperparameter
2. **Landauer cost computation** — Thermodynamic cost of precision transitions
3. **GPU buffer serialization** — Type-safe serialization to WebGPU buffers
4. **Semantic type entropy bounds** — Natural information content for data types

## Core Insight

**Precision is not a hyperparameter to optimize — it is a physical quantity
to measure.**

Drawing on Landauer's principle: the computational cost of precision transitions
is determined by the mismatch between representation capacity and actual
information content.

────────────────────────────────────────────────────────────────────────────────
                                                      // landauer // principle
────────────────────────────────────────────────────────────────────────────────

## Landauer's Principle

Erasing one bit of information requires dissipating at least kT ln 2 joules.

```
E_min = kT ln 2 * (H_in - H_out)
```

**Crucially**: If H_out = H_in, the operation is thermodynamically reversible
and can be performed at ZERO energy cost. This includes:
- Bijective mappings
- Any transformation preserving information content

At room temperature (300K):
```
E_min = 1.380649e-23 * 300 * 0.693147 = 2.87e-21 J/bit
```

This theoretical limit establishes the fundamental boundary for computation.

────────────────────────────────────────────────────────────────────────────────
                                                        // natural // precision
────────────────────────────────────────────────────────────────────────────────

## Natural Precision

Given tolerance epsilon, the **natural precision** at a point is:

```
b* = min{ b in N : E[D(phi(x), phi(Q_b(x)))] <= epsilon }
```

This is the minimum bits needed to stay within tolerated distortion.

**Key property:** Natural precision is DERIVED from entropy, not chosen.

```purescript
naturalPrecision :: Entropy -> NaturalPrecision
naturalPrecision (Entropy h) = NaturalPrecision (ceilInt h)
```

────────────────────────────────────────────────────────────────────────────────
                                                         // entropy // atoms
────────────────────────────────────────────────────────────────────────────────

## Entropy Atoms

### Entropy

Information content in bits.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Entropy | Number | 0.0 | 64.0 | clamps | Information entropy in bits |

**Smart Constructors:**
- `entropy :: Number -> Entropy` — Create with clamping
- `entropyBits :: Int -> Entropy` — Create from integer bit count
- `entropyUnsafe :: Number -> Entropy` — Create without bounds checking
- `unwrapEntropy :: Entropy -> Number` — Extract inner value

**Show Format:** `H(24.0 bits)`

### NaturalPrecision

Minimum bits needed given measured entropy.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| NaturalPrecision | Int | 1 | 64 | clamps | Ceiling of entropy |

**Formula:**
```
b* = ceil(H) where H is measured entropy
```

**Smart Constructors:**
- `naturalPrecision :: Entropy -> NaturalPrecision` — Derive from entropy
- `precisionBits :: Int -> NaturalPrecision` — Direct construction
- `precisionFromEntropy :: Entropy -> NaturalPrecision` — Alias
- `unwrapPrecision :: NaturalPrecision -> Int` — Extract inner value

**Show Format:** `24-bit`

### LandauerCost

Thermodynamic cost of a precision transition.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| LandauerCost | Number | 0.0 | 64.0 | implicit | Bits erased in transition |

**Formula:**
```
Cost = max(0, H_source - b_target)
```

If target precision can hold source entropy, cost is ZERO (free boundary).

**Smart Constructors:**
- `landauerCost :: Entropy -> NaturalPrecision -> LandauerCost` — Calculate cost
- `landauerCostNumber :: LandauerCost -> Number` — Extract bits erased
- `freeBoundary :: LandauerCost` — Zero cost constant
- `isFree :: LandauerCost -> Boolean` — Check if transition is free
- `costInJoules :: LandauerCost -> Number` — Convert to physical energy

**Show Format:** `Cost(4.5 bits erased)`

────────────────────────────────────────────────────────────────────────────────
                                                     // physical // constants
────────────────────────────────────────────────────────────────────────────────

## Physical Constants

| Constant | Value | Unit | Description |
|----------|-------|------|-------------|
| `boltzmannConstant` | 1.380649e-23 | J/K | Boltzmann constant |
| `roomTemperature` | 300.0 | K | Reference temperature |
| `thermalEnergy` | ~2.87e-21 | J/bit | kT ln 2 at room temp |

**Thermal Energy Calculation:**
```
thermalEnergy = boltzmannConstant * roomTemperature * ln(2)
              = 1.380649e-23 * 300 * 0.693147
              = 2.87e-21 J/bit
```

This is the minimum energy required to erase one bit of information.

────────────────────────────────────────────────────────────────────────────────
                                                      // tolerance // molecules
────────────────────────────────────────────────────────────────────────────────

## Distortion Tolerance

From Definition 2 in the Landauer paper, precision selection requires dual
criteria:

### DistortionTolerance

| Field | Type | Min | Max | Notes |
|-------|------|-----|-----|-------|
| forward | Number | 0.0 | 64.0 | epsilon_fwd: Shannon tolerance (output distortion) |
| backward | Number | 0.0 | 64.0 | epsilon_bwd: Gibbs tolerance (gradient distortion) |

**Constructors:**
- `distortionTolerance :: Number -> Number -> DistortionTolerance` — Asymmetric
- `symmetricTolerance :: Number -> DistortionTolerance` — Same for both flows

**Accessors:**
- `toleranceForward :: DistortionTolerance -> Number`
- `toleranceBackward :: DistortionTolerance -> Number`

### Why Dual Criteria?

Forward pass (inference) and backward pass (training) have different precision
requirements:

| Pass | Tolerance | What it measures |
|------|-----------|------------------|
| Forward | epsilon_fwd | How much output error is acceptable |
| Backward | epsilon_bwd | How much gradient error is acceptable |

A precision that works for inference may be too coarse for gradient flow.

────────────────────────────────────────────────────────────────────────────────
                                                         // dual // sensitivity
────────────────────────────────────────────────────────────────────────────────

## Dual Sensitivity Functions

### Forward Sensitivity (Shannon Entropy Flow)

Measures how much quantization affects forward pass outputs.

**Formula:**
```
Delta_fwd(b) = max(0, H_source - b)
```

```purescript
forwardSensitivity :: Entropy -> NaturalPrecision -> Number
```

### Backward Sensitivity (Gibbs Entropy Flow)

Measures how much quantization affects gradient computation.

**Formula:**
```
Delta_bwd(b) = max(0, H_gradient - b)
```

```purescript
backwardSensitivity :: Entropy -> NaturalPrecision -> Number
```

### Tolerance Satisfaction

```purescript
-- Check forward tolerance: Delta_fwd(b) <= epsilon_fwd
satisfiesForwardTolerance :: Entropy -> NaturalPrecision -> DistortionTolerance -> Boolean

-- Check backward tolerance: Delta_bwd(b) <= epsilon_bwd
satisfiesBackwardTolerance :: Entropy -> NaturalPrecision -> DistortionTolerance -> Boolean

-- Check BOTH tolerances (Definition 2)
satisfiesDualTolerance :: Entropy -> Entropy -> NaturalPrecision -> DistortionTolerance -> Boolean
```

────────────────────────────────────────────────────────────────────────────────
                                                    // operational // precision
────────────────────────────────────────────────────────────────────────────────

## Operational Precision

### Definition 1 (Single Tolerance)

```
b*_v(epsilon) = min{ b in N : E[D(phi_v(x), phi_v(Q_b(x)))] <= epsilon }
```

```purescript
operationalPrecision :: Entropy -> Number -> NaturalPrecision
```

Given entropy and tolerance, find minimum bits where distortion <= tolerance.
Result: `ceil(entropy - tolerance)`, clamped to [1, 64].

### Definition 2 (Dual Criteria)

```
b*_v = min{ b : Delta_fwd_v(b) <= epsilon_fwd AND Delta_bwd_v(b) <= epsilon_bwd }
```

```purescript
effectivePrecision :: Entropy -> Entropy -> DistortionTolerance -> NaturalPrecision
```

Finds minimum precision satisfying BOTH forward and backward requirements.
Result: `max(ceil(H_fwd - eps_fwd), ceil(H_bwd - eps_bwd))`, clamped to [1, 64].

```purescript
effectivePrecisionSymmetric :: Entropy -> DistortionTolerance -> NaturalPrecision
```

Simplified version when forward and backward entropy are equal.

────────────────────────────────────────────────────────────────────────────────
                                                       // precision // formats
────────────────────────────────────────────────────────────────────────────────

## PrecisionFormat Enum

Hardware precision formats available for GPU computation.

| Constructor | Bits | Capacity | Description |
|-------------|------|----------|-------------|
| `FP32` | 32 | 24.0 | 32-bit float (23 mantissa + implicit) |
| `FP16` | 16 | 11.0 | 16-bit float (10 mantissa + implicit) |
| `BF16` | 16 | 8.0 | 16-bit bfloat (7 mantissa + implicit) |
| `FP8E4M3` | 8 | 4.0 | 8-bit float (4 exp, 3 mantissa) |
| `FP8E5M2` | 8 | 3.0 | 8-bit float (5 exp, 2 mantissa) |
| `FP4` | 4 | 2.5 | 4-bit float (NVFP4) |
| `INT8` | 8 | 8.0 | 8-bit integer |
| `INT4` | 4 | 4.0 | 4-bit integer |

**Capacity vs Bits:**

Capacity is the EFFECTIVE bits for information content. For floating-point
formats, this accounts for overhead (exponent, sign). INT formats have 1:1
capacity-to-bits ratio.

### Format Selection

```purescript
formatForEntropy :: Entropy -> PrecisionFormat
```

Selects minimum format that can hold the entropy:

| Entropy Range | Format Selected |
|---------------|-----------------|
| H <= 2.5 | FP4 |
| H <= 3.0 | FP8E5M2 |
| H <= 4.0 | FP8E4M3 |
| H <= 8.0 | BF16 |
| H <= 11.0 | FP16 |
| H > 11.0 | FP32 |

────────────────────────────────────────────────────────────────────────────────
                                                         // semantic // types
────────────────────────────────────────────────────────────────────────────────

## SemanticType Enum

Different data types have natural entropy bounds based on their meaning.

| Constructor | Typical Entropy | Derived Bits | Description |
|-------------|-----------------|--------------|-------------|
| `Pixel` | 24.0 | 24 | RGB pixel values |
| `Latent` | 4.0 | 4 | VAE latent space (highly compressed) |
| `Token` | 16.0 | 16 | Token IDs (~65k vocab typical) |
| `Embedding` | 12.0 | 12 | Token embeddings |
| `Attention` | 8.0 | 8 | Attention weights |
| `Probability` | 10.0 | 10 | Output probabilities (~1000 classes) |
| `Gradient` | 8.0 | 8 | Gradient values |
| `Accumulator` | 32.0 | 32 | FP32 accumulator |

**Usage:**
```purescript
semanticTypeEntropy :: SemanticType -> Entropy
semanticTypeBits :: SemanticType -> Int
```

### Why Semantic Types Matter

At billion-agent scale, agents need to know the natural precision of data
WITHOUT measuring it. A Pixel has ~24 bits of information; a VAE Latent has
~4 bits. This is semantic knowledge, not runtime measurement.

────────────────────────────────────────────────────────────────────────────────
                                                      // information // bundle
────────────────────────────────────────────────────────────────────────────────

## InfoBundle

Data described by entropy, not precision.

```purescript
type InfoBundle =
  { shape :: Array Int          -- Logical dimensions
  , entropy :: Entropy          -- Upper bound on bits of information
  , semanticType :: SemanticType
  }
```

**Key insight:** Precision is a GAUGE CHOICE at materialization time, not part
of the bundle definition.

**Constructors:**
- `infoBundle :: Array Int -> Entropy -> SemanticType -> InfoBundle`

**Accessors:**
- `bundleShape :: InfoBundle -> Array Int`
- `bundleEntropy :: InfoBundle -> Entropy`
- `bundleSemanticType :: InfoBundle -> SemanticType`

### Example

```purescript
-- A batch of 32 images, 256x256, RGB
imageBundle = infoBundle [32, 256, 256, 3] (entropy 24.0) Pixel

-- VAE latent representation
latentBundle = infoBundle [32, 64, 64, 4] (entropy 4.0) Latent
```

The same logical data can be materialized at different precisions depending
on the operation (training vs inference, forward vs backward).

────────────────────────────────────────────────────────────────────────────────
                                                                // domains
────────────────────────────────────────────────────────────────────────────────

## Domain

A connected region with consistent gauge choices (precision and layout).

```purescript
type Domain =
  { id :: Int
  , entropy :: Entropy
  , precision :: PrecisionFormat
  }
```

**Constructors:**
- `domain :: Int -> Entropy -> PrecisionFormat -> Domain`

**Accessors:**
- `domainEntropy :: Domain -> Entropy`
- `domainPrecision :: Domain -> PrecisionFormat`

### Why Domains Matter

Within a domain, no precision conversions occur. All operations use the same
format. Boundaries between domains are where gauge transformations happen.

────────────────────────────────────────────────────────────────────────────────
                                                              // boundaries
────────────────────────────────────────────────────────────────────────────────

## Boundary

A boundary between two domains where gauge transformation occurs.

```purescript
type Boundary =
  { source :: Domain
  , target :: Domain
  , cost :: LandauerCost
  }
```

**Constructors:**
- `boundary :: Domain -> Domain -> Boundary`

Cost is automatically computed from source entropy and target precision.

**Predicates:**
- `boundaryIsFree :: Boundary -> Boolean` — True if cost is zero
- `boundaryCost :: Boundary -> LandauerCost`

### Free Boundaries

A boundary is FREE (zero Landauer cost) when:
```
target_bits >= source_entropy
```

Free boundaries can be fused into kernel epilogues without memory spill.

────────────────────────────────────────────────────────────────────────────────
                                                    // gauge // transformations
────────────────────────────────────────────────────────────────────────────────

## GaugeTransform

A precision/layout change between representations.

```purescript
type GaugeTransform =
  { sourcePrecision :: PrecisionFormat
  , targetPrecision :: PrecisionFormat
  , injective :: Boolean
  }
```

**Constructors:**
- `bijectiveRemap :: PrecisionFormat -> PrecisionFormat -> GaugeTransform`

The `bijectiveRemap` constructor asserts injectivity (caller responsibility).

**Predicates:**
- `isInjective :: GaugeTransform -> Boolean`

**Cost Calculation:**
- `gaugeTransformCost :: GaugeTransform -> Entropy -> LandauerCost`

### Bijective Transformations

Gauge transformations that are bijective (injective on realized support) have
ZERO Landauer cost. These can be fused into epilogues.

Examples of bijective transformations:
- FP32 -> FP16 when all values fit in FP16 range
- Channel permutation (RGB -> BGR)
- Normalization with known inverse

Non-bijective transformations incur cost based on bits erased.

────────────────────────────────────────────────────────────────────────────────
                                                          // storable // class
────────────────────────────────────────────────────────────────────────────────

## GPUStorable Typeclass

Types that can be serialized to GPU buffers.

```purescript
class GPUStorable a where
  byteSize :: a -> Int              -- Size in bytes
  alignment :: a -> Alignment       -- Memory alignment
  toBytes :: a -> ByteArray         -- Serialize
  fromBytes :: ByteArray -> Maybe a -- Deserialize
```

### Laws

1. **Roundtrip**: `fromBytes (toBytes x) == Just x`
2. **Size consistency**: `bytesLength (toBytes x) == byteSize`
3. **Alignment**: Buffer offset must be multiple of alignment

### Determinism Guarantee

**Same value -> same bytes. Always.**

This is critical for:
- Cache keying (UUID5 of serialized data)
- Distributed agents producing identical buffers
- Reproducible rendering across sessions

────────────────────────────────────────────────────────────────────────────────
                                                         // alignment // atoms
────────────────────────────────────────────────────────────────────────────────

## Alignment

Memory alignment requirement (must be power of 2).

| Constructor | Bytes | Usage |
|-------------|-------|-------|
| `align4` | 4 | f32, i32, u32 |
| `align8` | 8 | vec2<f32>, f64 |
| `align16` | 16 | vec3<f32>, vec4<f32>, mat4x4<f32> |

**WebGPU Alignment Rules:**

| Type | Size | Alignment | Notes |
|------|------|-----------|-------|
| f32 | 4 | 4 | Standard float |
| vec2<f32> | 8 | 8 | Two floats |
| vec3<f32> | 12 | **16** | Three floats, 16-byte aligned! |
| vec4<f32> | 16 | 16 | Four floats |
| mat4x4<f32> | 64 | 16 | 4x4 matrix |

**Critical:** vec3<f32> requires 16-byte alignment despite being only 12 bytes.
This is a WebGPU spec requirement.

────────────────────────────────────────────────────────────────────────────────
                                                        // byte // array // type
────────────────────────────────────────────────────────────────────────────────

## ByteArray

Byte array for GPU serialization.

```purescript
newtype ByteArray = ByteArray (Array Int)
```

Each Int is 0-255 (one byte). In actual WebGPU, this maps to ArrayBuffer/TypedArray.

**Operations:**
- `emptyBytes :: ByteArray` — Empty array
- `concatBytes :: ByteArray -> ByteArray -> ByteArray` — Concatenation
- `bytesLength :: ByteArray -> Int` — Length in bytes

**Padding Utilities:**
- `paddingNeeded :: Int -> Alignment -> Int` — Bytes to reach alignment
- `alignedSize :: Int -> Alignment -> Int` — Size with padding

────────────────────────────────────────────────────────────────────────────────
                                                     // primitive // instances
────────────────────────────────────────────────────────────────────────────────

## Primitive Type Instances

### Number (f32)

| Size | Alignment | WGSL Type |
|------|-----------|-----------|
| 4 bytes | 4-byte | f32 |

Uses IEEE 754 single-precision. Little-endian byte order.

### Int (i32)

| Size | Alignment | WGSL Type |
|------|-----------|-----------|
| 4 bytes | 4-byte | i32 |

32-bit signed integer. Little-endian byte order.

### Boolean (u32)

| Size | Alignment | WGSL Type |
|------|-----------|-----------|
| 4 bytes | 4-byte | u32 |

WebGPU uses 32-bit booleans. 0 = false, non-zero = true.

────────────────────────────────────────────────────────────────────────────────
                                                       // schema // instances
────────────────────────────────────────────────────────────────────────────────

## Schema Atom Instances

### UnitInterval

| Size | Alignment | WGSL Type | Normalization |
|------|-----------|-----------|---------------|
| 4 bytes | 4-byte | f32 | Native [0,1] |

### Vec2 Number

| Size | Alignment | WGSL Type |
|------|-----------|-----------|
| 8 bytes | 8-byte | vec2<f32> |

### Vec3 Number

| Size | Alignment | WGSL Type | Notes |
|------|-----------|-----------|-------|
| 12 bytes | **16-byte** | vec3<f32> | WebGPU spec quirk |

### Vec4 Number

| Size | Alignment | WGSL Type |
|------|-----------|-----------|
| 16 bytes | 16-byte | vec4<f32> |

### Point2D

| Size | Alignment | WGSL Type |
|------|-----------|-----------|
| 8 bytes | 8-byte | vec2<f32> |

### Size2D Number

| Size | Alignment | WGSL Type | Components |
|------|-----------|-----------|------------|
| 8 bytes | 8-byte | vec2<f32> | x=width, y=height |

────────────────────────────────────────────────────────────────────────────────
                                                         // color // instances
────────────────────────────────────────────────────────────────────────────────

## Color Type Instances

All color types normalize channel values to [0,1] for GPU representation.

### Channel

| Size | Alignment | WGSL Type | Normalization |
|------|-----------|-----------|---------------|
| 4 bytes | 4-byte | f32 | 0-255 -> 0.0-1.0 |

### Opacity

| Size | Alignment | WGSL Type | Normalization |
|------|-----------|-----------|---------------|
| 4 bytes | 4-byte | f32 | 0-100 -> 0.0-1.0 |

### Hue

| Size | Alignment | WGSL Type | Normalization |
|------|-----------|-----------|---------------|
| 4 bytes | 4-byte | f32 | 0-359 degrees -> 0.0-1.0 |

Shaders multiply by 360.0 or 2pi to get degrees/radians.

### Saturation

| Size | Alignment | WGSL Type | Normalization |
|------|-----------|-----------|---------------|
| 4 bytes | 4-byte | f32 | 0-100% -> 0.0-1.0 |

### Lightness

| Size | Alignment | WGSL Type | Normalization |
|------|-----------|-----------|---------------|
| 4 bytes | 4-byte | f32 | 0-100% -> 0.0-1.0 |

### SRGB (RGB without alpha)

| Size | Alignment | WGSL Type | Normalization |
|------|-----------|-----------|---------------|
| 12 bytes | **16-byte** | vec3<f32> | Channels 0-255 -> 0.0-1.0 |

### SRGBA (RGB with alpha)

| Size | Alignment | WGSL Type | Normalization |
|------|-----------|-----------|---------------|
| 16 bytes | 16-byte | vec4<f32> | Channels + opacity normalized |

### RGB

| Size | Alignment | WGSL Type | Normalization |
|------|-----------|-----------|---------------|
| 12 bytes | **16-byte** | vec3<f32> | Channels 0-255 -> 0.0-1.0 |

### RGBA

| Size | Alignment | WGSL Type | Normalization |
|------|-----------|-----------|---------------|
| 16 bytes | 16-byte | vec4<f32> | Channels + opacity normalized |

### HSL

| Size | Alignment | WGSL Type | Normalization |
|------|-----------|-----------|---------------|
| 12 bytes | **16-byte** | vec3<f32> | H/360, S/100, L/100 |

Shaders can convert to RGB using standard HSL->RGB algorithm.

### HSLA

| Size | Alignment | WGSL Type | Normalization |
|------|-----------|-----------|---------------|
| 16 bytes | 16-byte | vec4<f32> | H/360, S/100, L/100, A/100 |

────────────────────────────────────────────────────────────────────────────────
                                                       // geometry // instances
────────────────────────────────────────────────────────────────────────────────

## Geometry Type Instances

### Degrees

| Size | Alignment | WGSL Type | Normalization |
|------|-----------|-----------|---------------|
| 4 bytes | 4-byte | f32 | 0-360 -> 0.0-1.0 |

### Radians

| Size | Alignment | WGSL Type | Normalization |
|------|-----------|-----------|---------------|
| 4 bytes | 4-byte | f32 | 0-2pi -> 0.0-1.0 |

### Turns

| Size | Alignment | WGSL Type | Normalization |
|------|-----------|-----------|---------------|
| 4 bytes | 4-byte | f32 | Native [0,1] |

Turns are the most GPU-native angle representation (one turn = 2pi radians).

### Radius

| Size | Alignment | WGSL Type | Layout |
|------|-----------|-----------|--------|
| 8 bytes | 4-byte | struct | 1 byte tag + 3 padding + 4 bytes value |

**Tags:**
| Tag | Constructor | Value |
|-----|-------------|-------|
| 0 | RadiusNone | ignored (0.0) |
| 1 | RadiusPx | pixels |
| 2 | RadiusPercent | percentage |
| 3 | RadiusRem | rem units |
| 4 | RadiusFull | 9999.0 |

Shaders switch on tag to interpret the value.

────────────────────────────────────────────────────────────────────────────────
                                                      // transform // instances
────────────────────────────────────────────────────────────────────────────────

## Transform Type Instances

### Scale

| Size | Alignment | WGSL Type | Range |
|------|-----------|-----------|-------|
| 8 bytes | 8-byte | vec2<f32> | -10.0 to 10.0, 1.0 = identity |

Negative values indicate flip/mirror on that axis.

### Translate

| Size | Alignment | WGSL Type | Range |
|------|-----------|-----------|-------|
| 8 bytes | 8-byte | vec2<f32> | pixels, unbounded |

### Rotate

| Size | Alignment | WGSL Type | Normalization |
|------|-----------|-----------|---------------|
| 4 bytes | 4-byte | f32 | degrees -> turns [0,1] |

### Skew

| Size | Alignment | WGSL Type | Range |
|------|-----------|-----------|-------|
| 8 bytes | 8-byte | vec2<f32> | -89 to 89 degrees |

### Origin

| Size | Alignment | WGSL Type | Range |
|------|-----------|-----------|-------|
| 8 bytes | 8-byte | vec2<f32> | 0-100 percentage |

### Transform2D (Compound)

| Size | Alignment | WGSL Type |
|------|-----------|-----------|
| 48 bytes | 16-byte | struct |

**Layout:**
| Field | Offset | Size | Type |
|-------|--------|------|------|
| translate | 0 | 8 | vec2<f32> |
| rotate | 8 | 4 | f32 |
| padding | 12 | 4 | - |
| scale | 16 | 8 | vec2<f32> |
| skew | 24 | 8 | vec2<f32> |
| origin | 32 | 8 | vec2<f32> |
| flags | 40 | 4 | u32 |
| padding | 44 | 4 | - |

**Flags bitfield:**
| Bit | Field |
|-----|-------|
| 0 | has translate |
| 1 | has rotate |
| 2 | has scale |
| 3 | has skew |

Missing components use identity values.

────────────────────────────────────────────────────────────────────────────────
                                                       // design // philosophy
────────────────────────────────────────────────────────────────────────────────

## Design Philosophy

### Precision as Physics, Not Hyperparameter

Traditional ML quantization treats precision as a knob to turn. The Landauer
framework recognizes precision as a physical quantity derived from information
content.

**Old way:**
```
config.precision = "fp16"  -- arbitrary choice
```

**Landauer way:**
```
let entropy = measureEntropy activations
let precision = formatForEntropy entropy  -- derived
```

### Thermodynamic Foundations

Landauer's principle establishes that information erasure has physical cost.
This means:

1. **Free boundaries exist** — Bijective transformations cost nothing
2. **Cost is measurable** — Bits erased directly maps to energy
3. **Optimization has limits** — You cannot compress below entropy

### Semantic Type Awareness

Different data types have inherent information content. A pixel needs ~24 bits;
a VAE latent needs ~4 bits. The SemanticType system encodes this knowledge,
allowing agents to select precision without runtime measurement.

### Gauge Invariance

Precision is a "gauge choice" — a matter of representation, not substance.
The same InfoBundle can be materialized at different precisions for different
purposes:

- **Training forward pass**: FP16 (speed)
- **Training backward pass**: FP32 (gradient precision)
- **Inference**: INT8 (deployment efficiency)

The Domain/Boundary system tracks where gauge transformations occur and their
costs.

────────────────────────────────────────────────────────────────────────────────
                                                                   // usage
────────────────────────────────────────────────────────────────────────────────

## Usage Examples

### Entropy-Based Precision Selection

```purescript
import Hydrogen.Schema.GPU.Landauer

-- Measure entropy and derive precision
let measured = entropy 6.5
let precision = naturalPrecision measured  -- 7-bit
let format = formatForEntropy measured     -- BF16

-- Check cost of transition
let cost = landauerCost measured (precisionBits 4)
-- cost = Cost(2.5 bits erased) because 6.5 - 4 = 2.5
```

### Free Boundary Detection

```purescript
-- Source has 4 bits of entropy
let sourceH = entropy 4.0

-- Target can hold 8 bits
let targetB = precisionBits 8

let cost = landauerCost sourceH targetB
-- cost = freeBoundary because 8 >= 4

if isFree cost
  then fusedEpilogue  -- no memory spill needed
  else spillToMemory
```

### Dual Tolerance Precision Selection

```purescript
-- Forward pass needs 8 bits, backward needs 12
let forwardH = entropy 8.0
let backwardH = entropy 12.0
let tolerance = distortionTolerance 1.0 0.5  -- tighter backward tolerance

let precision = effectivePrecision forwardH backwardH tolerance
-- precision considers BOTH requirements
```

### GPU Buffer Serialization

```purescript
import Hydrogen.Schema.GPU.Storable

-- Serialize a color to GPU buffer
let color = srgba 128 64 255 100
let bytes = toBytes color  -- ByteArray[16 bytes]

-- Verify roundtrip
case fromBytes bytes of
  Just recovered -> recovered == color  -- true
  Nothing -> false

-- Check alignment for buffer layout
let align = alignment color  -- align16
let size = byteSize color    -- 16 bytes
```

────────────────────────────────────────────────────────────────────────────────
                                                              // integration
────────────────────────────────────────────────────────────────────────────────

## Integration with Hydrogen

### With Surface/Spatial

GPU types serialize Surface atoms (colors, transforms) and Spatial primitives
(vectors, points) to WebGPU buffers for rendering.

### With Compute/Tensor

Landauer precision guides quantization for ML inference and training, ensuring
precision choices are grounded in information theory.

### With Motion

Animation interpolation can operate at entropy-appropriate precision, with
free boundaries between keyframes when information is preserved.

────────────────────────────────────────────────────────────────────────────────
                                                         // lean4 // proofs
────────────────────────────────────────────────────────────────────────────────

## Lean4 Proof Integration

The GPUStorable roundtrip property is proven in Lean4:

```lean
theorem roundtrip : forall x, deserialize (serialize x) = x
```

This proof ensures that GPU buffer serialization is lossless and deterministic.
At billion-agent scale, this guarantee prevents subtle data corruption from
accumulating across distributed systems.

────────────────────────────────────────────────────────────────────────────────
                                                                // summary
────────────────────────────────────────────────────────────────────────────────

## Summary

The GPU pillar provides:

1. **Landauer framework** — Entropy-based precision selection grounded in
   thermodynamics
2. **GPUStorable typeclass** — Type-safe, deterministic GPU buffer serialization
3. **Semantic types** — Natural entropy bounds for common data types
4. **Domain/Boundary system** — Track precision transitions and their costs

**Key formulas:**
- Natural precision: `b* = ceil(H)`
- Landauer cost: `Cost = max(0, H_source - b_target)`
- Thermal energy: `E = kT ln 2 * bits_erased`
- Effective precision: `b* = max(ceil(H_fwd - eps_fwd), ceil(H_bwd - eps_bwd))`

**Key insight:** Precision is not arbitrary — it is derived from information
content. Free boundaries (zero cost) exist when representations preserve
information. This is not optimization heuristics — it is physics.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                                  // end // gpu
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
