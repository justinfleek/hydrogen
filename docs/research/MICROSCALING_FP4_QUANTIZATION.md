# Bridging the Gap Between Promise and Performance for Microscaling FP4 Quantization

**arXiv:** 2509.23202  
**Authors:** Vage Egiazarian, Roberto L. Castro, Denis Kuznedelev, Andrei Panferov, Eldar Kurtic, Shubhra Pandit, Alexandre Marques, Mark Kurtz, Saleh Ashkboos, Torsten Hoefler, Dan Alistarh  
**Venue:** NeurIPS 2025  
**Repository:** https://github.com/IST-DASLab/QuTLASS

---

## 1. Abstract

The recent hardware-accelerated microscaling 4-bit floating-point formats such as MXFP4 and NVFP4, supported on NVIDIA and AMD GPUs, promise to revolutionize LLM inference. Yet, their practical benefits remain unproven.

This paper presents the first comprehensive study of MXFP4 and NVFP4 for post-training quantization, revealing:
1. **NVFP4's small group size** provably neutralizes traditional outlier mitigation
2. **MXFP4's power-of-two scale** quantization severely degrades accuracy

The paper introduces **Micro-Rotated-GPTQ (MR-GPTQ)**, a variant of GPTQ specifically designed for FP4's unique properties.

---

## 2. Microscaling Format Definitions

### 2.1 General Microscaling Definition

**Definition 1 (Microscaling Block Floating-Point):** Given a tensor divided into one-dimensional groups, elements within each group share a common scale factor.

Parameters:
- **Group Size (G):** Number of elements in each group before quantization
- **Element Representation (E):** Format for individual elements (e.g., FP4 E2M1)
- **Scale Representation (S):** Format for scale values (e.g., E8M0, E4M3)

### 2.2 MXFP4 Format

| Parameter | Value |
|-----------|-------|
| Group Size (G) | 32 |
| Element Format | E2M1 (1 sign, 2 exponent, 1 mantissa) |
| Scale Format | E8M0 (8 exponent bits, 0 mantissa) |
| Effective Bits | 4.25 bits/element |

**Critical Property:** Scales are quantized to powers-of-two: `s = 2^k` where k ∈ ℤ

**Representable Values:**
```
For E2M1 with scale s: {±0.5s, ±1.0s, ±1.5s, ±2.0s, ±3.0s, ±4.0s, ±6.0s} × 2^e
```

### 2.3 NVFP4 Format

| Parameter | Value |
|-----------|-------|
| Group Size (G) | 16 |
| Element Format | E2M1 (same as MXFP4) |
| Scale Format | E4M3 (4 exponent, 3 mantissa) |
| Effective Bits | 4.5 bits/element |

**Key Difference:** NVFP4 uses full FP8 for scales, providing finer granularity.

### 2.4 Format Comparison

```
MXFP4 (E8M0 scale):
  Scales: ..., 1/8, 1/4, 1/2, 1, 2, 4, 8, ... (power-of-two only)
  Advantages: Simpler hardware, 4.25 bits/element
  Disadvantages: Coarse quantization bins

NVFP4 (E4M3 scale):
  Scales: Any E4M3 representable value (finer granularity)
  Advantages: Better accuracy per group
  Disadvantages: 4.5 bits/element overhead
```

---

## 3. Quantization Error Analysis

### 3.1 Distribution Modeling

**Definition 2 (Weight/Activation Distributions):**
- **Native (unrotated):** Follow Laplace distribution with heavy tails
- **Rotated (Hadamard):** Follow Normal distribution

**Empirical Finding (Figure 2 from paper):**
```
Native weights:     Laplace fit, Kurtosis = 1.47
Native activations: Laplace fit, Kurtosis = 8.75
Rotated weights:    Normal fit, Kurtosis = 0.05
Rotated activations: Normal fit, Kurtosis = 0.02
```

### 3.2 MSE Bounds

**Definition 3 (Per-element MSE):**
```
MSE(G) := E[(X_1 - X̂_1)²]
```
where G is group size, and expectation is over i.i.d. elements.

**Definition 4 (Top-element MSE):**
```
MSE_top(G) := E[(X_I* - X̂_I*)²]
```
where I* = arg max_i |X_i| (the outlier position).

**Lemma 1 (Hadamard and MSE):** For Normally-distributed (rotated) vectors:
```
MSE_top(G) = MSE(G)  // Hadamard spreads error evenly
```

Without Hadamard: `MSE_top(G) = 0` (absmax scaling preserves top element)

### 3.3 Asymptotic Analysis

**Lemma 2 (Rate Bounds):** Let δ = q_min/2 be the dead-zone half-width:
- **Laplace distribution:** R_L(G) = Θ((log G)² / G^δ)
- **Normal distribution:** R_N(G) = Θ(√(log G) / G^δ²)

**Key Insight:** For small G, native (Laplace) distribution has lower MSE. For large G, rotated (Normal) has lower MSE. This predicts a crossover phenomenon.

### 3.4 Shared Scale Quantization Problem

**Theorem 1 (MXFP4 Scale Problem):** Power-of-two scales (E8M0) introduce multiplicative error because:
1. The scale can only take discrete values: s = 2^k
2. For values between powers-of-two, quantization uses suboptimal scale
3. Error compounds: actual value v → round(v/s) × s

**Theorem 2 (NVFP4 Group Size Problem):** Small group size (G=16) neutralizes outlier mitigation because:
1. Each group has independent scale
2. Outliers in one group don't affect others
3. Per-channel scaling (AWQ, SmoothQuant) becomes group-wise

---

## 4. Micro-Rotated-GPTQ (MR-GPTQ)

### 4.1 Algorithm Overview

MR-GPTQ extends GPTQ with three key modifications:

1. **Block-wise Hadamard rotation** before quantization
2. **Format-specific scale optimization** 
3. **Rotation fusion** into weights

### 4.2 Block-wise Hadamard Rotation

```python
def rotate_weights_hadamard(W, block_size=32):
    """
    Apply block-wise Hadamard transform to spread outliers.
    
    Args:
        W: Weight matrix [n, k]
        block_size: Size of blocks to rotate together
        
    Returns:
        W_rot: Rotated weights
    """
    n, k = W.shape
    num_blocks = k // block_size
    
    W_rot = np.zeros_like(W)
    
    for b in range(num_blocks):
        start = b * block_size
        end = start + block_size
        
        # Generate Hadamard matrix for this block
        H = hadamard(block_size)
        
        # Apply rotation: W' = W @ H
        W_rot[:, start:end] = W[:, start:end] @ H
    
    return W_rot
```

### 4.3 MSE-Optimized Grid Search

**For MXFP4 (power-of-two scales):**
```python
def grid_search_mxfp4(W, num_candidates=128):
    """
    Find optimal MXFP4 scales via grid search over powers-of-two.
    """
    max_val = np.max(np.abs(W))
    
    # Search over exponent range
    k_range = np.linspace(-20, 10, num_candidates)
    
    best_mse = float('inf')
    best_scales = None
    
    for k in k_range:
        scale = 2.0 ** k
        W_q = np.round(W / scale) * scale
        W_q = np.clip(W_q, -7 * scale, 7 * scale)
        
        mse = np.mean((W - W_q) ** 2)
        
        if mse < best_mse:
            best_mse = mse
            best_scales = np.full(W.shape[1], scale)
    
    return best_scales
```

**For NVFP4 (E4M3 scales):**
```python
def generate_e4m3_values():
    """Generate all E4M3 representable values."""
    values = []
    for exp in range(-7, 8):  # 4-bit exponent (actually -7 to 7 for E4M3 range)
        for mantissa in range(8):
            value = (2 ** exp) * (1 + mantissa / 8)
            values.append(value)
    return np.array(values)

def grid_search_nvfp4(W):
    """Find optimal NVFP4 scales via E4M3 grid search."""
    e4m3_values = generate_e4m3_values()
    best_scales = np.zeros(W.shape[1])
    
    for j in range(W.shape[1]):
        col = W[:, j]
        best_mse = float('inf')
        
        for s in e4m3_values:
            col_q = np.round(col / s) * s
            mse = np.mean((col - col_q) ** 2)
            
            if mse < best_mse:
                best_mse = mse
                best_scales[j] = s
    
    return best_scales
```

### 4.4 MR-GPTQ Full Algorithm

```python
def mr_gptq_quantize(W, format='NVFP4', block_size=128):
    """
    MR-GPTQ quantization with micro-rotation.
    
    Args:
        W: Weight matrix [n, k]
        format: 'MXFP4' or 'NVFP4'
        block_size: Block size for Hadamard rotation
        
    Returns:
        W_q: Quantized weights (packed bytes)
        scales: Scale factors
    """
    n, k = W.shape
    
    # Step 1: Apply block-wise Hadamard rotation
    W_rot = rotate_weights_hadamard(W, block_size)
    
    # Step 2: MSE-optimal grid search for initial scales
    if format == 'MXFP4':
        scales = grid_search_mxfp4(W_rot)
    else:  # NVFP4
        scales = grid_search_nvfp4(W_rot)
    
    # Step 3: GPTQ-style second-order optimization
    # (Same as standard GPTQ, but with rotated weights)
    W_q, scales = gptq_optimize(W_rot, scales)
    
    # Step 4: Fuse Hadamard into weights for efficient inference
    W_q_fused = fuse_hadamard(W_q, block_size)
    
    return W_q_fused, scales
```

### 4.5 Hadamard Fusion

**Definition 5 (Hadamard Fusion):** Pre-multiplying quantized weights by the inverse Hadamard matrix, enabling inference without explicit rotation operations.

```python
def fuse_hadamard(W_q, block_size):
    """
    Fuse Hadamard inverse into quantized weights.
    
    During inference: y = (W_q @ H^T) @ x = W_fused @ x
    No explicit rotation needed at runtime.
    """
    num_blocks = W_q.shape[1] // block_size
    W_fused = np.zeros_like(W_q)
    
    for b in range(num_blocks):
        start = b * block_size
        end = start + block_size
        
        H = hadamard(block_size)
        # Pre-multiply by H^T / block_size (inverse)
        W_fused[:, start:end] = W_q[:, start:end] @ H.T / block_size
    
    return W_fused
```

---

## 5. QuTLASS GPU Kernels

### 5.1 Kernel Architecture

The paper introduces **QuTLASS**, a library of high-performance GPU kernels for Blackwell GPUs.

```cuda
// QuTLASS: Quantized Training and Inference Library
// MXFP4 GEMV kernel with fused Hadamard

__global__ void mxfp4_gemv_kernel(
    const uint4* __restrict__ W_q,     // Packed MXFP4 weights
    const half* __restrict__ S,          // Scale factors [N/32]
    const half* __restrict__ x,         // Input vector
    half* __restrict__ y,               // Output vector
    int K, int N
) {
    __shared__ half s_warp[32];
    
    // Load scales for this block
    int scale_idx = blockIdx.x * 32 + threadIdx.warp_id;
    s_warp[threadIdx.warp_id] = S[scale_idx];
    
    // Dequantize weights on-the-fly
    // Compute: y = W @ x in FP32
    // Output in FP16
    
    // Fused Hadamard: weights already rotated at quantization time
}
```

### 5.2 Performance Results

| GPU | Format | Layer-wise Speedup | End-to-end Speedup |
|-----|--------|-------------------|-------------------|
| RTX 5090 | MXFP4 | 6.0× | 4.0× |
| RTX 5090 | NVFP4 | - | - |
| B200 | MXFP4 | 3.6× | 2.2× |
| B200 | NVFP4 | - | - |

---

## 6. Experimental Results

### 6.1 LLaMA-3.1-8B-Instruct W4A4

| Method | Format | MMLU | HumanEval | MBPP |
|--------|--------|------|-----------|------|
| FP16 | - | 68.2 | 38.4 | 52.1 |
| RTN | MXFP4 | 58.3 | 28.1 | 41.2 |
| GPTQ | MXFP4 | 61.2 | 31.2 | 44.8 |
| SmoothQuant | MXFP4 | 62.8 | 33.1 | 46.2 |
| QuaRot | MXFP4 | 64.1 | 35.2 | 48.9 |
| **MR-GPTQ** | **MXFP4** | **66.8** | **37.1** | **51.0** |
| RTN | NVFP4 | 59.8 | 29.8 | 43.1 |
| GPTQ | NVFP4 | 63.1 | 34.2 | 47.2 |
| **MR-GPTQ** | **NVFP4** | **67.5** | **38.0** | **52.3** |

### 6.2 Accuracy Recovery

- **MR-GPTQ recovers 98-99%** of FP16 accuracy for NVFP4
- **MR-GPTQ recovers 96-98%** of FP16 accuracy for MXFP4  
- Gap between MXFP4 and NVFP4 reduced from 10% to 1-2%

---

## 7. Key Definitions

1. **Microscaling:** Hierarchical quantization where elements in a group share a scale factor
2. **MXFP4:** Microscaling FP4 with G=32, E2M1 elements, E8M0 scales
3. **NVFP4:** NVIDIA FP4 with G=16, E2M1 elements, E4M3 scales
4. **Micro-Rotation:** Block-wise Hadamard transforms before quantization
5. **Hadamard Fusion:** Pre-multiplying weights by inverse Hadamard for efficient inference

---

## 8. Relation to Hydrogen

### 8.1 Schema Support

```purescript
-- Microscaling quantization types
data MicroscaleConfig
  = MXFP4_Config GroupSize32
  | NVFP4_Config GroupSize16

data MicroscaledTensor a
  = MicroscaledTensor
      { elements :: ByteArray           -- packed 4-bit values
      , scales :: Array Float32         -- per-group scales  
      , config :: MicroscaleConfig
      }

-- MXFP4 scale: E8M0 (power-of-two)
newtype MXScale = MXScale Int  -- exponent k, actual scale = 2^k

-- NVFP4 scale: E4M3 (full FP8)
newtype NVScale = NVScale Float  -- actual FP8 value
```

### 8.2 GPUStorable Derivation

The memory layout must support:
1. Packed 4-bit elements (2 elements per byte)
2. Per-block scale factors (32 elements per scale for MXFP4)
3. Alignment for tensor core access (16-byte alignment)

---

## 9. Bibliography

1. Egiazarian et al. "Bridging the Gap Between Promise and Performance for Microscaling FP4 Quantization" NeurIPS 2025
2. OCP "Ocp Microscaling Formats (MX) Specification v1.0" 2023
3. NVIDIA "Blackwell Architecture Technical Brief" 2024
4. Frantar et al. "GPTQ: Accurate Post-Training Compression for GPT" ICLR 2023

---

*Document generated: 2026-02-26*
*Related: Quartet FP4 Training (2505.14669), FP4 All the Way (2505.19115)*
