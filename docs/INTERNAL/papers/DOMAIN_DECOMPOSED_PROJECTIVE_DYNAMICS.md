# High-performance CPU Cloth Simulation Using Domain-decomposed Projective Dynamics

**Authors**: Zixuan Lu, Ziheng Liu, Lei Lan, Huamin Wang, et al. (Utah, Style3D, UCLA)
**Venue**: ACM SIGGRAPH 2025
**Domain**: Cloth Simulation / Parallel Computing / Projective Dynamics

────────────────────────────────────────────────────────────────────────────────

## Abstract

CPU-based high-performance cloth simulation using domain decomposition:
- 300-400ms per frame for high-resolution garments
- Parallel scheme optimized for multicore CPU architecture
- Domain-decomposed projective dynamics pipeline
- 10x+ faster than existing CPU simulators

────────────────────────────────────────────────────────────────────────────────

## Key Concepts for Paint Layer Simulation

### 1. Projective Dynamics (PD)

Split optimization into local and global steps:

**Local Step** (parallelizable per constraint):
```
argmin_{y_i} (w_i/2) ||A_i S_i x - B_i y_i||²  s.t. C_i(y_i) = 0
```

**Global Step** (linear solve):
```
K x = b
K = M/h² + Σ_i w_i S_i^T A_i^T A_i S_i
```

### 2. Domain Decomposition

Divide cloth into independent domains with shared boundary DOFs:

```
Ω = Ω¹ ∪ Ω² ∪ ... ∪ Ω^D

Interface constraint: x^j_D = x^k_D for all adjacent domains
```

**Key insight**: Solve each domain in parallel, then reconcile at boundaries.

### 3. Primal-Dual Formulation

Convert to system with dual variables (Lagrange multipliers) at interfaces:

```
[ G_RR   G_RC  ] [ λ   ]   [ b*_R  ]
[ G_RC^T -G_CC ] [ x_C ] = [ -b*_C ]
```

Where:
- `λ` = constraint forces at duplicate DOFs
- `x_C` = corner DOFs (small, shared between domains)
- `x_R` = remainder DOFs (large, per-domain)

### 4. Parallelization Strategy

1. **Pre-factorize** domain matrices K^j_RR (constant if no topology change)
2. **Solve corner DOFs** x_C via small condensed system
3. **Solve dual variables** λ
4. **Solve remainder DOFs** x^j_R in parallel per domain

────────────────────────────────────────────────────────────────────────────────

## Relevance to Paint Canvas

### Paint Layer as Deformable Surface

Stacked paint can be modeled as a thin deformable layer:
- **Bending constraints**: Resist curling at edges
- **Stretching constraints**: Paint film stretches/tears
- **Attachment constraints**: Paint adheres to canvas

### Domain Decomposition for Large Canvas

For high-resolution canvas (4K+), decompose into tiles:
- Each tile simulated independently
- Boundary conditions at tile edges
- Parallel processing across CPU cores

### Toppling as Constraint Violation

When paint height exceeds stability:
- PD constraints become unsatisfiable
- System "projects" to stable configuration (topple/flow)
- Natural emergence of paint collapse behavior

────────────────────────────────────────────────────────────────────────────────

## Implementation for Hydrogen

```purescript
-- Domain decomposition for canvas
type CanvasDomain =
  { region :: Rect Int              -- Tile bounds
  , interiorDOFs :: Array Int       -- DOFs owned by this domain
  , boundaryDOFs :: Array Int       -- DOFs shared with neighbors
  , localMatrix :: SparseMatrix     -- K^j_RR pre-factorized
  }

-- Parallel solve across domains
type DomainSolveResult =
  { domainId :: Int
  , positions :: Array Vec3         -- Updated paint positions
  , boundaryForces :: Array Vec3    -- Forces at boundaries
  }

-- PD iteration
projectiveDynamicsStep :: CanvasState -> DeltaTime -> CanvasState
projectiveDynamicsStep state dt =
  let
    -- Local step: project constraints in parallel
    localProjections = parMap projectLocalConstraints state.domains
    
    -- Global step: solve for corner DOFs
    cornerDOFs = solveCornerSystem state.cornerMatrix localProjections
    
    -- Solve remainder in parallel per domain
    updatedDomains = parMap (solveDomain cornerDOFs) state.domains
  in
    state { domains = updatedDomains }
```

────────────────────────────────────────────────────────────────────────────────

## Key Algorithms

### Algorithm: Domain-Decomposed Global Solve

```python
def domain_decomposed_solve(domains, b):
    # Step 1: Compute corner DOFs
    b_star_R = sum(S_D @ K_RR_inv @ b_R for domain in domains)
    b_star_C = b_C - sum(S_C.T @ K_RC.T @ K_RR_inv @ b_R for domain in domains)
    
    x_C = solve(G_star_CC, b_star_C - G_RC.T @ G_RR_inv @ b_star_R)
    
    # Step 2: Compute dual variables
    lambda_ = solve(G_RR, b_star_R - G_RC @ x_C)
    
    # Step 3: Solve remainder DOFs in parallel
    for domain in parallel(domains):
        x_R[domain] = K_RR_inv @ (b_R - S_D.T @ lambda_ - K_RC @ S_C @ x_C)
    
    return x_R, x_C
```

────────────────────────────────────────────────────────────────────────────────
                                                                     — 2026-03-01
