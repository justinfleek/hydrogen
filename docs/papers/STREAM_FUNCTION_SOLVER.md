━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                 // stream // function // solver
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

**Title**: A Stream Function Solver for Liquid Simulations
**Authors**: Ryoichi Ando (IST Austria), Nils Thuerey (TU München), 
             Chris Wojtan (IST Austria)
**Venue**: ACM SIGGRAPH / Transactions on Graphics
**Year**: 2015

────────────────────────────────────────────────────────────────────────────────
                                                                     // abstract
────────────────────────────────────────────────────────────────────────────────

## Summary

Liquid simulation technique that enforces incompressibility using a **stream
function solve** instead of pressure projection.

**Key Innovation**: Novel boundary conditions for free surfaces that enable
stream function approach to liquid simulation (previously only used for
single-phase flows like smoke).

**Benefits**:
1. Resulting flow is **guaranteed divergence-free** regardless of solve accuracy
2. Free-surface boundary conditions guarantee divergence-free motion in 
   **un-simulated air phase**
3. Enables **two-phase flow simulation by computing only single phase**
4. Complex bubble interactions without explicitly solving gas phase

────────────────────────────────────────────────────────────────────────────────
                                                                // navier-stokes
────────────────────────────────────────────────────────────────────────────────

## Background: Navier-Stokes Equations

Inviscid, incompressible Navier-Stokes:

```
Du/Dt = -(1/ρ)∇p + g     (momentum evolution)

∇·u = 0                   (mass conservation / incompressibility)
```

Where:
- u = fluid velocity field
- t = time
- ρ = fluid density
- p = fluid pressure
- g = body acceleration (gravity)

### Traditional Pressure Projection

Standard approach: find pressure p whose gradient projects velocity into
divergence-free state.

**Kinetic energy minimization**:
```
minimize  ∫_Ω (1/2)ρ||u* - (Δt/ρ)∇p||² dV
    p
```

Yields Poisson equation:
```
∇·((Δt/ρ)∇p) = ∇·u*
```

**Problems with pressure projection**:
1. p=0 at free surface doesn't enforce air incompressibility → collapsing bubbles
2. Two-phase simulation requires delicate interface treatment + extra computation
3. Iterative solvers only approximate incompressibility → volume drift

────────────────────────────────────────────────────────────────────────────────
                                                          // stream // function
────────────────────────────────────────────────────────────────────────────────

## Stream Function Approach

### Helmholtz-Hodge Decomposition

Any velocity field can be decomposed:
```
u* = ∇Θ + ∇×Ψ + γ
```

Where:
- ∇Θ = gradient of scalar field (curl-free component)
- ∇×Ψ = curl of vector field Ψ (divergence-free component)
- γ = harmonic vector field (neither curl nor gradient)

**Key insight**: Removing the gradient component gives divergence-free field:
```
u = ∇×Ψ + γ
```

Instead of solving for pressure and subtracting, **solve directly for Ψ**.

### Stream Function vs Vorticity

```
Vorticity:        ω = ∇×u      (curl OF velocity)
Stream Function:  u = ∇×Ψ      (velocity IS curl of stream function)
```

Both are vector-valued but have different content. Stream function doesn't
have obvious physical meaning but guarantees divergence-free velocity.

### Derivation

Starting from time-splitting:
```
u = u* - (Δt/ρ)∇p
```

Multiply by ρ, substitute u = ∇×Ψ, take curl (removes p):
```
∇×(ρ∇×Ψ) = ∇×(ρu*)
```

Equivalent to kinetic energy minimization:
```
minimize  ∫_Ω (1/2)ρ||u* - ∇×Ψ||² dV
    Ψ
```

### Removing Null Space

The curl operator has non-trivial nullspace: ∇×(Ψ + ∇φ) = ∇×Ψ

Add divergence regularizer to pin down unique solution:
```
minimize  ∫_Ω (1/2)ρ||u* - ∇×Ψ||² dV + (1/2)ρ(∇·Ψ)² dV
    Ψ
```

This acts exactly on nullspace, so solution still optimally solves original.

### Discretized System

```
([∇×]ᵀ[ρ][V][∇×] + [∇·]ᵀ[ρ][V][∇·])[Ψ] = [∇×]ᵀ[ρ][V][u*]
```

Using identity [∇×]ᵀ[∇×] + [∇·]ᵀ[∇·] = [∇²] (vector Laplacian):

```
([∇²] + [∇×]ᵀ[Δρ][∇×] + [∇·]ᵀ[Δρ][∇·])[Ψ] = [∇×]ᵀ[ρ][u*]
```

Where [Δρ] = deviation from liquid density.

**Critical insight**: If ρ_air = 0 (Δρ = -1 in air), matrix entries 
**completely disappear** outside liquid! Air is automatically divergence-free.

────────────────────────────────────────────────────────────────────────────────
                                                     // boundary // conditions
────────────────────────────────────────────────────────────────────────────────

## Boundary Conditions

### Liquid-Air Interface

**No special treatment needed!** By setting ρ = 0 in air domain, system matrix
automatically incorporates correct boundary condition.

Setting ρ_air = 0 corresponds to Atwood ratio = 1:
```
Atwood = (ρ_liquid - ρ_air) / (ρ_liquid + ρ_air) = 1
```

**Unique property**: Most methods become unstable as Atwood → 1, but this
method becomes **more stable and computationally simpler**.

Surface tension: Add force σH to u* at interface (σ = strength, H = mean curvature).

### Static Solid Boundaries

Set stream function equal to gradient of scalar potential:
```
Ψ = ∇φ̂
```

Then: ∇×Ψ = ∇×(∇φ̂) = 0

**Enforces u = 0 at solid boundary by construction.**

φ̂ contains degrees of freedom along solid surface.

### Rigid Body Coupling (Two-Way)

Rigid body velocity at point x:
```
ů = ω × x_rel + u_c
```

Where:
- x_c = center of mass
- u_c = translational velocity  
- ω = angular velocity
- x_rel = x - x_c

Stream function within solid that satisfies ∇×Ψ̆ = ů:

```
Ψ̆ = -(1/2) diag([y² + z², z² + x², x² + y²]) ω 
   + [[0, 0, y], [z, 0, 0], [0, x, 0]] u_c 
   + ∇φ̂
```

Degrees of freedom: scalar field φ̂ plus spatial constants ω and u_c.

**Monolithically coupled** (vs weakly coupled in prior work).

### Limitations

Boundary motion must be representable as stream function (volume-conserving).
Non-volume-conserving deformations require future research.

────────────────────────────────────────────────────────────────────────────────
                                                          // discretization
────────────────────────────────────────────────────────────────────────────────

## Discretization

### Grid Layout (Consistent with Discrete Exterior Calculus)

```
┌─────────────────────────────────────────────────────────────┐
│  Ψ components:  on cell EDGES    (1-forms)                  │
│  u components:  on cell FACES    (2-forms / fluxes)         │
│  φ̂ (scalar):    on VERTICES      (0-forms)                  │
└─────────────────────────────────────────────────────────────┘
```

### Curl Operator [∇×]

Rectangular matrix mapping edges to faces.

Y component of curl: ∂Ψx/∂z - ∂Ψz/∂x

(Similar for x and z components)

### Divergence Operator [∇·]

Rectangular matrix mapping edges to vertices.
Sums vector components on oriented edges adjacent to each vertex.

### Volume/Area Fractions

- **Liquid volume fraction**: stored at cell centers (normalize liquid = 1, air = 0)
- **Solid area fraction**: computed via "marching squares" contour extraction
- Solid boundary condition activated when solid fraction > 0.99
- Truncate fractions < 0.01 to zero

────────────────────────────────────────────────────────────────────────────────
                                                             // algorithm
────────────────────────────────────────────────────────────────────────────────

## Algorithm

### Tolerating Convergence Errors

Reformulate as **offsets** from previous time step:

```
[Ψ] = [Z][[ΔΨ̂], [Δφ̂]]ᵀ + [Ψ_{t-Δt}]
```

Where [Z] maps liquid regions to Ψ̂ and solid regions to gradient of φ̂.

**Benefits**:
1. Avoids spurious damping from early termination
2. Velocity u = ∇×Ψ is divergence-free **by construction**, even with errors

### Matrix Assembly

**Pre-computed (once, or when solids change)**:

[P] = solid boundary encoding:
```
[P] = [Z]ᵀ[∇×]ᵀ[1/A][∇×][Z] + [Z]ᵀ[∇·]ᵀ[1/A][∇·][Z]
```

Where [1/A] = diagonal matrix of reciprocal liquid area.
Away from boundaries, [P] = standard Laplacian [∇²].

[B] = [Z]ᵀ[∇×]ᵀ (for RHS assembly)

**Per time step**:

[Q] = density jump encoding:
```
[Q] = [Z]ᵀ[∇×]ᵀ[Δρ/A][∇×][Z] + [Z]ᵀ[∇·]ᵀ[Δρ/A][∇·][Z]
```

[Q] is non-zero **only in narrow band** around liquid-air interface.

[K] = [P] + [Q]

### Linear System

```
[K][[ΔΨ̂], [Δφ̂]]ᵀ = [B][ρ][u*] - [K][[Ψ̂_{t-Δt}], [φ̂_{t-Δt}]]ᵀ
```

Solve with **Preconditioned Conjugate Gradient (PCG)**.
MIC(0) preconditioner with τ = 0.97, σ = 1.0.

### Algorithm Pseudocode

```
STREAM_FUNCTION_PROJECTION(u*, θF, θS):
  
  if first_call:
    precompute [Z] from θS
    precompute [P]  // Eq. 17
    precompute [B] = [Z]ᵀ[∇×]ᵀ
    set [Ψ̂_{t-Δt}], [φ̂_{t-Δt}] = 0
  
  compute [ρ], [Δρ] from θF (fluid level set)
  compute [Q]  // Eq. 18
  compute [K] = [P] + [Q]
  
  assemble linear system
  solve with PCG
  
  [Ψ̂_t], [φ̂_t] = [ΔΨ̂], [Δφ̂] + [Ψ̂_{t-Δt}], [φ̂_{t-Δt}]
  [u] = [∇×][Z][[Ψ̂_t], [φ̂_t]]ᵀ
  
  return [u]
```

────────────────────────────────────────────────────────────────────────────────
                                                                   // results
────────────────────────────────────────────────────────────────────────────────

## Results

### Performance

- Resolution 256×256×128: 54 sec/timestep, 3.9 min/frame
- Resolution 128×256×128: 18-52 sec/timestep, 1.5-1.9 min/frame
- Resolution 256×128×64: 49 sec/timestep, 1.5 min/frame

PCG residual tolerance: ||r||₂/||r₀||₂ < 10⁻⁴

### Comparison with Pressure Projection

Stream function projection is **5.6× slower** than single-phase pressure projection.
Whole timestep is **~3× slower** on average.

However, compared to **two-phase solvers**:
- Setting ρ_air = 0 makes two-phase methods unstable
- Large density jumps require smaller timesteps
- Air domain requires memory/computation

### Key Demonstrations

1. **Glugging container**: Violent splashes from air moving opposite to liquid
   (without explicitly simulating second phase)

2. **Bubble rising**: Complex deformation and breakup captured by
   divergence-free motion in region around liquid

3. **Rigid body coupling**: Non-grid-aligned boundaries, two-way coupled
   rigid body, bubbles — all strongly coupled

4. **Convergence error tolerance**: Less accurate solve = less accurate motion,
   but **still divergence-free**

────────────────────────────────────────────────────────────────────────────────
                                                                // limitations
────────────────────────────────────────────────────────────────────────────────

## Limitations

1. **3× more unknowns** than pressure solver (vector vs scalar Poisson)
2. Components **strongly coupled** at boundaries (can't split into 3 scalar solves)
3. Boundary motion must be **volume-conserving** (representable as stream function)
4. **No inflow/outflow** boundary conditions yet (but should be possible if
   total flux integrates to zero)
5. **Compressible flows** require additional gradient term treatment

────────────────────────────────────────────────────────────────────────────────
                                                      // implementation // notes
────────────────────────────────────────────────────────────────────────────────

## Implementation Notes for Hydrogen

### Relevant Schema Modules

1. **Vector Fields on Staggered Grids**
   - Ψ on edges: `Hydrogen.Schema.Geometry.EdgeField`
   - u on faces: `Hydrogen.Schema.Geometry.FaceField`
   - φ on vertices: `Hydrogen.Schema.Geometry.VertexField`

2. **Differential Operators**
   - Curl [∇×]: `Hydrogen.Schema.Physics.Curl`
   - Divergence [∇·]: `Hydrogen.Schema.Physics.Divergence`
   - Laplacian [∇²]: `Hydrogen.Schema.Physics.Laplacian`

3. **Level Set / Distance Functions**
   - Fluid surface: `Hydrogen.Schema.Geometry.LevelSet`
   - Solid surface: `Hydrogen.Schema.Geometry.SDF`

4. **Linear Algebra**
   - Sparse matrices: `Hydrogen.Schema.Compute.SparseMatrix`
   - PCG solver: `Hydrogen.Schema.Compute.ConjugateGradient`

### Key Data Structures

```purescript
type StreamFunctionState =
  { psi :: EdgeField Number        -- Stream function on edges
  , phi :: VertexField Number      -- Scalar potential on vertices (solids)
  , fluidLevelSet :: CellField Number
  , solidSDF :: VertexField Number
  }

type StreamFunctionMatrices =
  { z :: SparseMatrix              -- Boundary mapping
  , p :: SparseMatrix              -- Solid-encoded Laplacian (precomputed)
  , b :: SparseMatrix              -- RHS assembly (precomputed)
  }
```

### Discrete Exterior Calculus Connection

This discretization aligns with DEC:
- 0-forms (scalars) on vertices
- 1-forms (Ψ) on edges  
- 2-forms (fluxes u) on faces

Operators [∇×] and [∇·] match DEC operators on regular grids.

────────────────────────────────────────────────────────────────────────────────
                                                             // full-attribution
────────────────────────────────────────────────────────────────────────────────

## Full Attribution

### This Paper

**A Stream Function Solver for Liquid Simulations**

Ryoichi Ando¹, Nils Thuerey², Chris Wojtan¹

¹ IST Austria
² Technische Universität München

ACM Transactions on Graphics (Proceedings of SIGGRAPH)
CR Categories: I.3.7 [Computer Graphics]: Three-Dimensional Graphics 
and Realism—Animation

### Acknowledgements (from paper)

- JSPS Postdoctoral Fellowship for Research Abroad (Ryoichi Ando)
- ERC-2014-StG-637014 realFlow
- ERC-2014-StG-638176 BigSplash
- Reiji Tsuruno (computational resources)
- Keenan Crane (discussions about Hodge decomposition)
- Florian Ferstl (discussions about FLIP)

### Key References Cited

**Stable Fluids**
Jos Stam.
"Stable Fluids."
SIGGRAPH 1999, pp. 121-128.

**MAC Grid**
Francis H. Harlow, J. Eddie Welch.
"Numerical Calculation of Time-Dependent Viscous Incompressible Flow 
of Fluid with Free Surface."
Physics of Fluids 8(12), 1965, pp. 2182-2189.

**Fast Variational Framework (Solid-Fluid Coupling)**
Christopher Batty, Florence Bertails, Robert Bridson.
"A Fast Variational Framework for Accurate Solid-Fluid Coupling."
ACM Transactions on Graphics 26(3), 2007.

**Circulation-Preserving Simplicial Fluids**
Sharif Elcott, Yiying Tong, Eva Kanso, Peter Schröder, Mathieu Desbrun.
"Stable, Circulation-Preserving, Simplicial Fluids."
ACM Transactions on Graphics (TOG) 26(1), 2007.

**FLIP Method**
Robert Bridson.
"Fluid Simulation for Computer Graphics."
AK Peters/CRC Press, 2008.

**MultiFLIP (Two-Phase)**
Landon Boyd, Robert Bridson.
"MultiFLIP for Energetic Two-Phase Fluid Simulation."
ACM Transactions on Graphics 31(2), 2012.

**Narrow-Band FLIP**
Nuttapong Chentanez, Matthias Müller, Tae-Yong Kim.
"Coupling 3D Eulerian, Heightfield and Particle Methods for Interactive 
Simulation of Large Scale Liquid Phenomena."
Eurographics/ACM SIGGRAPH Symposium on Computer Animation, 2014.

**Discrete Exterior Calculus**
Fernando de Goes, Keenan Crane, Mathieu Desbrun, Peter Schröder, et al.
"Digital Geometry Processing with Discrete Exterior Calculus."
ACM SIGGRAPH 2013 Courses.

**Curl-Noise**
Robert Bridson, Jim Houriham, Marcus Nordenstam.
"Curl-Noise for Procedural Fluid Flow."
ACM Transactions on Graphics (TOG) 26(3), 2007.

**Vortex Methods**
Andrew Selle, Nick Rasmussen, Ronald Fedkiw.
"A Vortex Particle Method for Smoke, Water and Explosions."
ACM Transactions on Graphics 24(3), 2005, pp. 910-914.

**Rigid-Fluid Coupling**
Mark Carlson, Peter J. Mucha, Greg Turk.
"Rigid Fluid: Animating the Interplay Between Rigid Bodies and Fluid."
ACM SIGGRAPH 2004, pp. 377-384.

**Ghost Fluid Method**
Frédéric Gibou, Ronald P. Fedkiw, Li-Tien Cheng, Myungjoo Kang.
"A Second-Order-Accurate Symmetric Discretization of the Poisson 
Equation on Irregular Domains."
Journal of Computational Physics 176(1), 2002, pp. 205-227.

**Marching Cubes**
William E. Lorensen, Harvey E. Cline.
"Marching Cubes: A High Resolution 3D Surface Construction Algorithm."
SIGGRAPH 1987, pp. 163-169.

────────────────────────────────────────────────────────────────────────────────

                                                         — extracted 2026-02-26
