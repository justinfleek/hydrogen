# Quartet: Native FP4 Training Can Be Optimal for Large Language Models

**arXiv:** 2505.14669  
**Authors:** Roberto L. Castro, Andrei Panferov, Soroush Tabesh, Oliver Sieberling, Jiale Chen, Mahdi Nikdan, Saleh Ashkboos, Dan Alistarh (ISTA, ETH Zürich)  
**Venue:** NeurIPS 2025  
**Repository:** https://github.com/IST-DASLab/Quartet

---

## 1. Abstract

Training large language models directly in low-precision arithmetic offers a way to address computational costs by improving both throughput and energy efficiency. NVIDIA's Blackwell architecture facilitates extremely low-precision operations using FP4 variants, promising substantial efficiency gains. Current algorithms for training LLMs in FP4 precision face significant accuracy degradation and often rely on mixed-precision fallbacks.

This paper systematically investigates hardware-supported FP4 training and introduces **Quartet**, a new approach enabling accurate, end-to-end FP4 training with all major computations (linear layers) in low precision.

---

## 2. Low-Precision Scaling Law

### 2.1 Mathematical Formulation

The key contribution is deriving a scaling law that relates evaluation loss to precision:

```
L(N, D, P_forward, P_backward) = (A(N · eff_N(P_forward))^α + B(D · eff_D(P_backward))^β)^γ + E
```

Where:
- `N` = model parameters
- `D` = training tokens  
- `P_forward` / `P_backward` = precision for forward/backward pass
- `eff_N(P)` = effective model size accounting for precision overhead
- `eff_D(P)` = effective data accounting for gradient noise in low precision
- `A, B, α, β, γ, E` = fitted constants

### 2.2 Efficiency Factors Definition

**Definition 1 (Parameter Efficiency):** The factor `eff_N(P_forward)` represents how much the forward-pass precision reduces the effective parameter count. Lower precision reduces this factor, meaning more actual parameters are needed to achieve the same performance.

**Definition 2 (Data Efficiency):** The factor `eff_D(P_backward)` represents how much backward-pass precision affects data requirements. Lower precision increases data needs by factor `1/eff_D`.

**Definition 3 (Optimal Precision):** Given a computational budget, the optimal precision is the one that maximizes the product of efficiency factors while accounting for hardware speedups.

---

## 3. Four Ingredients of Quartet

### 3.1 Ingredient 1: Scaling Law Comparison Framework

The paper proposes using scaling laws to compare quantized training methods:

> "We say that quantized training method A is superior to method B if it offers both higher parameter efficiency eff_N and higher data efficiency eff_D."

### 3.2 Ingredient 2: Mixed-Precision Inference-Training Trade-offs

The paper analyzes the trade-off between inference cost and training cost:

| Operation | Compute Fraction | Precision Impact |
|-----------|-----------------|------------------|
| Forward Pass | ~33% | Affects inference latency |
| Backward Pass | ~66% | Affects training speed |

**Key insight:** We can train with lower precision on backward (more data) while keeping forward precision higher for inference efficiency.

### 3.3 Ingredient 3: Forward-Backward Error-Bias Trade-off

**Forward Pass Results (Table 2 from paper):**

| Rounding Method | eff_N | MSE |
|----------------|-------|-----|
| Stochastic Rounding AbsMax | 0.42 | 2.77 × 10⁻² |
| Round-to-nearest AbsMax | 0.59 | 1.37 × 10⁻² |
| QuEST (Hadamard + RMSE) | 0.64 | 1.32 × 10⁻² |

**Backward Pass Results:**

| Rounding Method | eff_D | Misalignment (1 - E[1/S]) |
|----------------|-------|---------------------------|
| Stochastic Rounding AbsMax | 0.88 | 0 |
| Round-to-nearest AbsMax | 0.93 | 9.3 × 10⁻³ |
| QuEST (Hadamard + RMSE) | 0.83 | 1.3 × 10⁻² |

**Key Finding:** QuEST has best forward-pass efficiency (lowest MSE), but RTN has best backward-pass efficiency. Quartet combines both.

### 3.4 Ingredient 4: Fast GPU Implementation

The implementation consists of two stages:

**Stage 1: Fused Quantization Kernel**
```
1. Hadamard transform: W_H = W @ H_g (g = 32)
2. Quantization to MXFP4: W_Q = quantize(W_H)
3. Scale calculation: s = compute_scales(W_H)
4. QuEST mask generation: M = compute_mask(W_H)
5. Write to global memory
```

**Stage 2: Dedicated GEMM Kernel**
- Uses Blackwell's `tcgen05.mma` instruction
- Native support for `D = C + (A × SFA) × (B × SFB)`
- Scale factors applied along inner (K) dimension

---

## 4. MXFP4 Format Specification

### 4.1 Format Definition

| Parameter | Value | Description |
|-----------|-------|-------------|
| Group Size (G) | 32 | Elements per scale factor |
| Element Format | E2M1 | 1 sign, 2 exponent, 1 mantissa |
| Scale Format | E8M0 | 8-bit exponent only (power-of-two) |
| Effective Bits | 4.25 | (32×4 + 8) / 32 = 4.25 bits/element |

### 4.2 Representable Values

FP4 E2M1 can represent 15 non-zero values (asymmetric around zero):
```
Positive: {0.5, 1.0, 1.5, 2.0, 3.0, 4.0, 6.0, 8.0, 12.0} × 2^e
Negative: symmetric around zero
Zero: all bits zero
```

### 4.3 Scale Quantization

MXFP4 uses E8M0 (power-of-two scales only):
```
Scale s = 2^k where k ∈ {-127, ..., 127}
```

---

## 5. Quartet Algorithm

### 5.1 Full Forward Pass

```
Algorithm 1: Quartet Forward Pass for Linear Layer

Input: Activations A, Weights W, Group size g
Output: Output O in MXFP4

1. // Forward pass
2. A_H = hadamard_transform(A, g)     // Apply block Hadamard
3. W_H = hadamard_transform(W, g)    
4. A_Q = quantize_to_mxfp4(A_H)      // QuEST quantization
5. W_Q = quantize_to_mxfp4(W_H)
6. O = mxfp4_gemm(A_Q, W_Q)          // MXFP4 matrix multiply
7. O = dequantize(O)

8. // Backward pass
9. grad_O = gradient_from_upstream
10. grad_W_H = hadamard_transform(grad_O @ A_H^T, g)
11. grad_A_H = W_H^T @ grad_O
12. grad_W_Q = rtn_quantize(grad_W_H) // RTN for backward
13. grad_A_Q = rtn_quantize(grad_A_H)
14. grad_W = inverse_hadamard(grad_W_Q)
15. grad_A = inverse_hadamard(grad_A_Q)

16. // Apply QuEST masks
17. grad_W = apply_quest_mask(grad_W, M_W)
18. grad_A = apply_quest_mask(grad_A, M_A)

19. return O, grad_W, grad_A
```

### 5.2 Hadamard Transform

**Definition 4 (Block-wise Hadamard Transform):** Given a vector x ∈ ℝ^g, the Hadamard transform is:
```
H(x) = H_g @ x
```
Where H_g is the g×g Hadamard matrix defined recursively:
```
H_1 = [1]
H_{2n} = [H_n  H_n; H_n  -H_n]
```

The inverse is: `H^{-1} = (1/g) H`

### 5.3 QuEST Quantization

**Definition 5 (QuEST Quantization):** 
1. Apply Hadamard transform to spread outlier influence
2. Compute RMSE-optimal clipping bounds
3. Quantize using round-to-nearest with learned scales

---

## 6. Experimental Results

### 6.1 Validation Loss (C4 Dataset, 30M parameters)

| Method | D/N=25× | D/N=50× | D/N=100× | D/N=200× | eff_N | eff_D |
|--------|---------|---------|----------|----------|-------|-------|
| LUQ-INT4 | 3.73 | 3.68 | 3.66 | 3.43 | 0.49 | 0.15 |
| LUQ-FP4 | 4.81 | 4.91 | 4.88 | 4.84 | 0.01 | 0.07 |
| JetFire-FP4 | 7.03 | 6.94 | 6.76 | 6.62 | Unstable | Unstable |
| HALO-FP4 | 6.65 | 7.04 | 6.55 | 6.50 | Unstable | Unstable |
| LSS-INT4 | NaN | 3.40 | NaN | NaN | Unstable | Unstable |
| **Quartet** | **3.49** | **3.38** | **3.29** | **3.24** | **0.65** | **0.95** |

### 6.2 Speedup Results (RTX 5090)

| Operation | vs FP8 | vs BF16 |
|-----------|--------|---------|
| Forward Pass | 2.0× | 4.0× |
| Backward Pass | 1.5× | 2.6× |
| Overall Training | 1.6× | 2.9× |

---

## 7. Relation to Hydrogen

### 7.1 Schema Implications

```purescript
-- Quantized tensor with block scaling
data QuantizedTensor (format :: Type) where
  QuantizedTensor ::
    { elements :: ByteArray       -- packed 4-bit values
    , scales :: Array Float32    -- per-block scale factors (E8M0)
    , format :: format           -- format metadata
    } -> QuantizedTensor format

-- Supported FP4 formats
data FP4Format
  = MXFP4 GroupSize32           -- Microscaling 4-bit (Quartet)
  | NVFP4 GroupSize16           -- NVIDIA 4-bit
  | FP4_E2M1                    -- Vanilla 4-bit float

-- MXFP4 scale: power-of-two
newtype MXScale = MXScale Int  -- stores exponent k, scale = 2^k

-- GPUStorable requires memory layout optimization
```

### 7.2 Error Bound Derivation

From the scaling law, for forward-pass precision P:
```
Loss gap ≤ f(1 - eff_N(P))
```

For FP4 with Quartet: `eff_N = 0.65`, so the loss gap is compensated by 1.54× parameter scaling.

---

## 8. Key Definitions from Paper

1. **MXFP4:** Microscaling FP4 format with G=32, E2M1 elements, E8M0 scales
2. **Parameter Efficiency (eff_N):** Factor relating forward precision to effective parameters
3. **Data Efficiency (eff_D):** Factor relating backward precision to effective data
4. **QuEST:** Quantization by minimizing mean-squared error with Hadamard rotation
5. **Block-wise Hadamard Transform:** Applying Hadamard transform at group granularity

---

## 9. Bibliography

1. Castro et al. "Quartet: Native FP4 Training Can Be Optimal for Large Language Models" NeurIPS 2025
2. NVIDIA "Blackwell Architecture Technical Brief" 2024
3. Open Compute Project "OCP Microscaling Formats (MX) Specification v1.0" 2023
4. Panferov et al. "QuEST: Stable training of LLMs with 1-bit weights and activations" 2025
5. NVIDIA "CUTLASS 3.9" 2025

---

*Document generated: 2026-02-26*
*See also: Microscaling FP4 (2509.23202), FP4 All the Way (2505.19115)*
