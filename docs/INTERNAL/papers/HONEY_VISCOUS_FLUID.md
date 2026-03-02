# A Geometrically Consistent Viscous Fluid Solver with Two-Way Fluid-Solid Coupling

**Authors**: Tetsuya Takahashi, Ming C. Lin (UNC Chapel Hill, UMD)
**Venue**: EUROGRAPHICS 2019
**Domain**: Viscous Fluid Simulation / Two-Way Coupling

────────────────────────────────────────────────────────────────────────────────

## Abstract

Grid-based fluid solver for viscous materials (honey, paint, chocolate) with:
- Implicit viscosity integration as minimization problem
- Geometrically consistent volume fractions for sub-grid details
- Two-way fluid-solid coupling via variational principle
- Position-correction for uniform particle distributions

────────────────────────────────────────────────────────────────────────────────

## Key Concepts for Wet Media Paint Simulation

### 1. Viscosity as Minimization Problem

Instead of solving viscosity forces directly, formulate as energy minimization:

```
s = argmin_s (
    (1/2) ||(PWu_F Wu_L)^(1/2) (u* - Δt P^(-1) Wu_L^(-1) D^T Ws_L s)||²
    + (Δt/4) N^(-1) ||(Ws_F Ws_L)^(1/2) s||²
)
```

Where:
- `s` = viscous stress tensor
- `P` = density matrix
- `D` = discrete finite-difference operator
- `N` = dynamic viscosity matrix
- `W` = volume fraction matrices

### 2. Volume Fractions for Sub-Grid Details

**Problem**: Independent volume estimation causes dangling artifacts.

**Solution**: Use double-resolution grid for consistent volume estimation:
- Simulation grid: SDF defined on grid nodes
- Double-resolution grid: Ensures volumes consistently contribute to u- and v-cells

### 3. Two-Way Fluid-Solid Coupling

Monolithically couple viscous fluid and rigid body dynamics:

```
minimize_s (
    fluid_inertia_term + 
    viscous_stress_term + 
    (1/2) ||M^(1/2) (V_t + Δt M^(-1) Wu_S J Ws_L s)||²
)
```

**Key insight**: Solid objects in honey can stand upright because viscosity
forces support them — one-way or weak coupling fails to capture this.

### 4. Position Correction via Density Constraints

Prevent particle clustering/gaps with iterative position correction:

```
x^(l+1)_i = x^l_i + α_i Δx^l_i
α_i = clamp(φ(x_i)/θ, α_min, α_max)
```

Where:
- `α_i` = scaling factor based on distance to solid boundaries
- Particles farther from boundaries can move more

────────────────────────────────────────────────────────────────────────────────

## Relevance to Wet Media Canvas

### Paint Stacking (Z-Depth)

This paper's **two-way coupling** is essential for:
- **Paint pileup**: Thick paint blobs supporting themselves
- **Toppling physics**: When paint height exceeds stability threshold
- **Brush interaction**: Pushing through existing paint

### Viscosity Parameters

| Material | η (kg/(s·m)) | Behavior |
|----------|--------------|----------|
| Water | 10^0 | Flows freely |
| Oil paint | 10^2 | Slow flow |
| Honey | 10^3 | Very slow, supports weight |
| Impasto | 10^4+ | Barely flows, holds shape |

### Implementation for Hydrogen

```purescript
-- Z-depth tracking per canvas cell
type CanvasCell =
  { wetness :: Wetness
  , pigmentColor :: Color
  , paintHeight :: PaintHeight      -- NEW: z-depth in pixels
  , viscosity :: Viscosity
  , lastUpdate :: Timestamp
  }

-- Height threshold for toppling
topplingThreshold :: PaintHeight -> Viscosity -> Boolean
topplingThreshold height visc =
  let
    h = unwrapPaintHeight height
    v = unwrapViscosity visc
    -- Higher viscosity = more stable
    maxStableHeight = 10.0 + (v * 0.5)
  in
    h > maxStableHeight
```

────────────────────────────────────────────────────────────────────────────────

## Algorithms

### Algorithm 1: Viscous Fluid Step

```python
def viscous_fluid_step(particles, grid, solids, dt):
    # 1. Advect particles
    for p in particles:
        p.position += dt * p.velocity
    
    # 2. Transfer to grid (PIC/FLIP)
    grid.transfer_particles_to_grid(particles)
    
    # 3. Compute volume fractions (geometrically consistent)
    Wu_F, Wu_L = compute_fluid_fractions(grid)
    Ws_F, Ws_L = compute_stress_fractions(grid)
    Wu_S = compute_solid_fractions(grid, solids)
    
    # 4. Solve viscosity (SPD linear system)
    s = solve_viscosity(grid.velocity, Wu_F, Wu_L, Ws_F, Ws_L, Wu_S, solids)
    
    # 5. Update velocity from stress
    grid.velocity = update_velocity_from_stress(s, grid.velocity)
    
    # 6. Pressure projection (divergence-free)
    grid.velocity = pressure_solve(grid.velocity)
    
    # 7. Transfer back to particles
    transfer_grid_to_particles(grid, particles)
    
    # 8. Position correction (density constraints)
    correct_particle_positions(particles, grid)
    
    return particles, grid
```

────────────────────────────────────────────────────────────────────────────────
                                                                     — 2026-03-01
