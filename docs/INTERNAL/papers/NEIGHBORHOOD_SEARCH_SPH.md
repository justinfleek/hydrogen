# Fast Octree Neighborhood Search for SPH Simulations

**Authors**: José Antonio Fernández-Fernández, Lukas Westhofen, Fabian Löschner, 
Stefan Rhys Jeske, Andreas Longva, Jan Bender (RWTH Aachen University)
**Venue**: ACM SIGGRAPH Asia 2022
**Domain**: Neighborhood Search / SPH Simulation / Parallel Computing

────────────────────────────────────────────────────────────────────────────────

## Abstract

Octree-based neighborhood search for SPH simulation achieving:
- **1.9x speedup** over state-of-the-art uniform grid methods
- Fixed-radius AND multi-resolution support (radius ratio up to 3x)
- Only 5-10% of total simulation time spent on neighborhood search
- Optimized for modern CPU vectorization and pipelining

**Key insight**: By permitting MORE distance comparisons than strictly necessary,
the time spent on managing the acceleration structure is reduced, yielding net
positive speedup. Counterintuitive but empirically validated.

────────────────────────────────────────────────────────────────────────────────

## Core Concepts

### 1. The Neighborhood Problem in SPH

For each particle i, find all neighbors within support radius r:

```
N_i = { j | ||x_i - x_j||_2 ≤ r }
```

This is the bottleneck for SPH. Naive O(n²) is intractable for large simulations.

### 2. Why Uniform Grids Are Suboptimal

Traditional approach: place particles in grid with cell size = support radius.

**Problems:**
- Small cell size → large number of cells → structure management overhead
- Few particles per cell → poor vectorization/pipelining utilization
- Imbalanced computational tasks across cells

### 3. Octree with Larger Cells

**Solution:** Use larger cells, aggregate into octree clusters.

```
Traditional: cell_size = support_radius (minimal comparisons, high overhead)
Octree:      cell_size > support_radius (more comparisons, lower overhead)
```

The octree ensures balanced computational tasks:
- Each leaf node has approximately same number of particles
- Benefits parallelism
- Maximizes brute-force throughput

### 4. Cluster-Based Leaf Nodes

Octree leaf nodes contain clusters of cells, not individual particles:

```
┌─────────────────────────────────────┐
│          Octree Root                │
├──────────┬──────────┬───────────────┤
│  Branch  │  Branch  │    Branch     │
├────┬─────┼────┬─────┼─────┬─────────┤
│Leaf│Leaf │Leaf│Leaf │Leaf │  Leaf   │
│ ~N │ ~N  │ ~N │ ~N  │ ~N  │   ~N    │
└────┴─────┴────┴─────┴─────┴─────────┘

Each leaf: approximately N particles (balanced workload)
```

### 5. Multi-Resolution Support

Unlike fixed-radius methods, octree naturally handles variable support radii:

```
Particle type A: radius = r
Particle type B: radius = 2r  
Particle type C: radius = 3r

Octree adapts cell clustering based on local density/radius requirements
```

────────────────────────────────────────────────────────────────────────────────

## Algorithm Overview

### Phase 1: Build Octree

```python
def build_octree(particles, target_particles_per_leaf):
    root = create_root_node(bounding_box(particles))
    
    def subdivide(node):
        if len(node.particles) <= target_particles_per_leaf:
            return  # This is a leaf
        
        # Split into 8 children (octants) / 4 children (quadrants for 2D)
        for child_idx in range(num_children):
            child = create_child(node, child_idx)
            child.particles = filter_to_child(node.particles, child_idx)
            subdivide(child)
    
    subdivide(root)
    return root
```

**Complexity:** O(n log n) build time

### Phase 2: Query Neighbors

```python
def query_neighbors(octree, particle_i, radius):
    neighbors = []
    
    def traverse(node):
        if not intersects_sphere(node.bounds, particle_i.pos, radius):
            return
        
        if is_leaf(node):
            # Brute force within leaf (vectorized)
            for p in node.particles:
                if distance_sq(particle_i.pos, p.pos) <= radius * radius:
                    neighbors.append(p)
        else:
            for child in node.children:
                traverse(child)
    
    traverse(octree.root)
    return neighbors
```

**Complexity:** O(k) where k = average neighbors (typically 30-50)

### Phase 3: Vectorized Distance Comparisons

Key optimization: brute-force stage uses SIMD:

```c
// Process 8 particles at once (AVX-256)
__m256 dx = _mm256_sub_ps(xi, xj_8);
__m256 dy = _mm256_sub_ps(yi, yj_8);
__m256 dz = _mm256_sub_ps(zi, zj_8);
__m256 dist_sq = _mm256_add_ps(
    _mm256_mul_ps(dx, dx),
    _mm256_add_ps(_mm256_mul_ps(dy, dy), _mm256_mul_ps(dz, dz))
);
__m256 mask = _mm256_cmp_ps(dist_sq, radius_sq, _CMP_LE_OQ);
```

────────────────────────────────────────────────────────────────────────────────

## Performance Analysis

### Benchmark Results (from paper)

| Scene | Particles | Uniform Grid | Octree | Speedup |
|-------|-----------|--------------|--------|---------|
| Dam break | 2M | 45ms | 28ms | 1.6x |
| Double dam | 4M | 112ms | 62ms | 1.8x |
| Fluid-solid | 5.6M | 156ms | 82ms | 1.9x |
| Swinging box | 5.6M | 148ms | 78ms | 1.9x |

### Why It's Faster

1. **Fewer cells to manage**: Larger cells = less structure overhead
2. **Balanced parallelism**: Each leaf ≈ same particle count
3. **Better vectorization**: Brute-force on batched particles
4. **Cache locality**: Clustered particles stay in cache

### Time Breakdown

```
Total simulation step: 100%
├── Neighborhood search: 5-10%
│   ├── Octree build: ~30% of search
│   ├── Traversal: ~20% of search
│   └── Distance comparisons: ~50% of search
├── Pressure solve: 40-50%
├── Force computation: 20-30%
└── Integration: 5-10%
```

────────────────────────────────────────────────────────────────────────────────

## Connection to Landauer Precision

The counterintuitive insight — **more comparisons can be faster** — connects
to Landauer's principle:

```
Landauer: The cost is in FORGETTING (information erasure)
          Not in PROCESSING (reversible computation)

Octree:   The cost is in STRUCTURE MANAGEMENT (memory traffic)
          Not in COMPARISONS (arithmetic in registers)
```

**Both papers say the same thing**: Optimize for what's actually expensive
(memory, information erasure), not what seems expensive (computation, comparisons).

### Gauge Symmetry Interpretation

The octree's larger cells are a **gauge choice**:
- Same information (particle positions) represented differently
- Bijective mapping between representations
- Zero Landauer cost for the transformation

The "extra" comparisons are **reversible operations** (no information erased),
while the uniform grid's structure overhead involves **memory traffic** (costly).

────────────────────────────────────────────────────────────────────────────────

## Connection to Domain Decomposition

The octree provides natural **domain decomposition** for parallel simulation:

```
Octree Structure          Domain Decomposition
───────────────          ────────────────────
Leaf nodes          →    Independent domains (parallel solve)
Branch boundaries   →    Interface DOFs (boundary reconciliation)
Root               →    Global coordination
```

**For projective dynamics**:
- Each octree leaf = one computational domain
- Particles within leaf = interior DOFs (solved in parallel)
- Particles at leaf boundaries = shared DOFs (reconciled after)

This maps directly to the DOMAIN_DECOMPOSED_PROJECTIVE_DYNAMICS paper's
architecture.

────────────────────────────────────────────────────────────────────────────────

## Relevance to Wet Media Canvas

### Pigment Particle Simulation

Paint pigments are particles. For realistic wet-in-wet effects:
- Pigment particles interact within smoothing radius
- Density affects color intensity
- Neighbors determine diffusion/mixing

### Variable Particle Sizes

Different media have different particle densities:
- Watercolor: small, many particles (fine detail)
- Oil paint: larger, fewer particles (thick strokes)
- Impasto: very large, viscous particles

Octree handles mixed-media canvas naturally.

### Scale Invariance

Same algorithm works for:
- 100 particles (single brush stroke)
- 10 million particles (full canvas simulation)

────────────────────────────────────────────────────────────────────────────────

## Implementation in Hydrogen

The `Hydrogen.Schema.Physics.Fluid.Neighborhood` module implements these concepts:

### Data Structures

```purescript
-- Spatial bounds for octree nodes
type SpatialBounds =
  { minX :: Number, maxX :: Number
  , minY :: Number, maxY :: Number
  }

-- Octree node (leaf or branch)
data OctreeNode
  = OctreeLeaf
      { bounds :: SpatialBounds
      , particles :: Array Int
      , depth :: Int
      }
  | OctreeBranch
      { bounds :: SpatialBounds
      , children :: Array OctreeNode
      , depth :: Int
      }

-- Configuration
type OctreeConfig =
  { maxParticles :: Int     -- Target particles per leaf (~64 optimal)
  , maxDepth :: Int         -- Prevent infinite subdivision
  }
```

### Key Functions

```purescript
-- Build octree from particles
mkOctree :: SpatialBounds -> OctreeConfig -> Octree

-- Insert particle
octreeInsert :: Octree -> Int -> Number -> Number -> Octree

-- Query neighbors within radius
octreeQuery :: Octree -> Number -> Number -> Number -> Array Int

-- Distance utilities
pointDistance :: Number -> Number -> Number -> Number -> Number
pointDistanceSq :: Number -> Number -> Number -> Number -> Number
boundsDistanceToPoint :: SpatialBounds -> Number -> Number -> Number
```

### Search Strategy Selection

```purescript
-- Automatic strategy selection based on particle count and density
chooseStrategy :: Int -> Number -> SearchStrategy
chooseStrategy particleCount densityVariance
  | particleCount < 100 = StrategyBruteForce
  | densityVariance > 0.5 = StrategyOctree      -- Variable density → octree
  | particleCount > 100000 = StrategyHashGrid   -- Very large → hash grid
  | otherwise = StrategyUniformGrid             -- Default
```

### Complexity Guarantees

| Operation | Complexity | Notes |
|-----------|------------|-------|
| Build | O(n log n) | One-time per frame |
| Insert | O(log n) | Amortized |
| Query | O(log n + k) | k = neighbors found |
| Rebuild | O(n log n) | When topology changes |

────────────────────────────────────────────────────────────────────────────────

## Key Takeaways for AI Agents

1. **Counterintuitive optimization**: More comparisons can be faster if structure
   overhead is reduced. Don't assume minimal comparisons = optimal.

2. **Balanced workloads matter**: Uniform grids create imbalanced tasks. Octrees
   adapt to particle distribution.

3. **Vectorization is critical**: Modern CPUs achieve high throughput on batched
   distance comparisons. Design for SIMD.

4. **Multi-resolution is natural**: Octrees handle variable radii without special
   cases. Important for mixed-media simulation.

5. **5-10% of simulation time**: Neighborhood search should not dominate. If it
   does, the acceleration structure is wrong.

6. **Domain decomposition emerges**: Octree leaves naturally partition space for
   parallel computation. Use this for projective dynamics.

────────────────────────────────────────────────────────────────────────────────
                                                                     — 2026-03-01
