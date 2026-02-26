# The Only Thing That's Difficult is To Forget Precisely

**Source**: Anonymous, December 2025
**Domain**: Thermodynamics of Computation, Neural Network Quantization, Information Theory

---

## Abstract

Precision is not a hyperparameter to be optimized — it is a **physical quantity
to be measured**. Drawing on Landauer's principle: the computational cost of
precision transitions is determined by the mismatch between representation
capacity and actual information content.

**Key insight**: Precision boundaries are computationally FREE when they satisfy
a codebook injectivity condition (bijective on realized support). Such bijective
remaps are **gauge symmetries** that conserve task information.

**The epilogue** (fused post-accumulator operations) is the last reversible
place to change gauges. Accumulators hold highest-SNR representation; spilling
to memory forces irreversible double-rounding.

**The only costly operation is forgetting — and the only difficult problem is
forgetting precisely the right amount.**

## 1. Core Insight: Precision as Physical Quantity

The dominant paradigm treats precision as resource to minimize subject to
accuracy constraints. **This is backwards.**

```
WRONG: Search over bit-widths → measure accuracy → accept/reject
RIGHT: Measure information content → precision IS determined
```

Precision is not chosen. It is determined by the information content of
activations at each point in the computation graph. The practitioner's task
is not optimization but **measurement**.

## 2. Landauer's Principle

### 2.1 Information Erasure Cost

Landauer (1961): Erasing one bit of information requires dissipating at least
**kT ln 2 joules** of energy.

```
E_min = kT ln 2 · (H_in - H_out)

where:
  k = Boltzmann's constant
  T = temperature
  H_in = input entropy
  H_out = output entropy
```

**Crucially**: If H_out = H_in, the operation is thermodynamically reversible
and can be performed at **zero energy cost**. This includes:
- Bijective mappings
- Any transformation preserving information content (even if representation changes)

### 2.2 Operational Natural Precision

**Definition**: Given tolerance ε, the natural precision at site v is:

```
b*_v(ε) = min{ b ∈ ℕ : E[D(φ_v(x), φ_v(Q_b(x)))] ≤ ε }

where:
  φ_v = subnetwork from site v to outputs
  Q_b = quantizer with b bits
  D   = task-relevant distortion (output KL, perceptual metric, loss increase)
```

This is the **rate-distortion view**: b*_v(ε) is the empirical rate (bits per
element) needed to stay within tolerated distortion for the task.

**Physical interpretation**:
- b < b*: Many-to-one mapping erases information → exceeds allowed distortion
- b ≥ b*: No additional logical erasure required

### 2.3 Dual Sensitivity Flows

Two entropy flows jointly determine precision requirements:

**Forward sensitivity (Shannon)**: How much does quantization affect outputs?
```
Δ→_v(b) = E[D(φ_v(x), φ_v(Q_b(x)))]
```

**Backward sensitivity (Gibbs)**: How much does quantization affect gradients?
```
Δ←_v(b) = E[||∇_a L(x) - Q_b(∇_a L(x))||²]
```

**Effective precision under dual criteria**:
```
b*_v = min{ b : Δ→_v(b) ≤ ε_fwd AND Δ←_v(b) ≤ ε_bwd }
```

## 3. Gauge Symmetries and Epilogues

### 3.1 Codebook Injectivity

**Claim**: A fused epilogue mapping φ is lossless on the realized distribution
IFF the restriction φ|S: S → C_b2 is **injective**.

```
Let:
  Q_b1 produce codes in C_b1
  S ⊆ C_b1 = set of codes actually realized (post-accumulator)
  φ = scale → bias → activation → round to C_b2

Condition for zero Landauer cost:
  |S| ≤ 2^b2 AND per-channel parameters place each s ∈ S into distinct Q_b2 bin
```

**In practice**: S is often much smaller than C_b1 over calibration data, making
injective remaps feasible even when b2 < b1.

### 3.2 Why Epilogues Matter

The epilogue is **the last reversible place to change gauges**.

**Wire energy dominates compute**: Moving 32-bit word to DRAM costs orders of
magnitude more than an FMA. For M×N GEMM with FP32 accumulators, fusing epilogue
avoids 8MN bytes of memory traffic.

**Accumulators are highest-SNR representation**: The FP32 accumulator holds the
most precise value you will ever have for that output. In-register, you can:
1. Apply bijective remap (scale, bias, activation)
2. Round ONCE to target codebook

**Double rounding is irreversible erasure**: Store (implicit round) → reload →
round again = information destroyed not by necessity but by poor scheduling.

### 3.3 The Correct Order

## 4. Information-Theoretic IR

### 4.1 Information Bundles

### 4.2 Domains and Boundaries

### 4.3 Compilation as Physics

## 5. Unifying Existing Methods

## 6. Hydrogen Relevance

---

*Synthesized for the Hydrogen project — precision as measured entropy, not optimized hyperparameter*
