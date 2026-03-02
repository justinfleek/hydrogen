━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                               // 16 // physics
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Physics Pillar

Forces, collision detection, fluid simulation, projective dynamics, and haptic
feedback for physics-based UI and realistic motion.

────────────────────────────────────────────────────────────────────────────────
                                                                    // overview
────────────────────────────────────────────────────────────────────────────────

## Implementation

- **Location**: `src/Hydrogen/Schema/Physics/`
- **Files**: 24 modules
- **Lines**: 8,647 total
- **Key features**: Conservative/dissipative forces, collision detection with
  bounding volumes, SPH fluid simulation, projective dynamics for cloth/soft
  body, domain decomposition for parallel solving, haptic force feedback

## Purpose

Physics provides bounded, deterministic primitives for:
- Force vectors and force fields (gravity, spring, drag, friction)
- Collision volumes (AABB, circle, capsule, OBB) with narrow-phase detection
- Collision response (bounce, slide, stick) with layer filtering
- SPH fluid simulation with kernel functions and neighbor search
- Grid-based Eulerian fluid solver (Navier-Stokes)
- Projective dynamics for deformable objects (cloth, soft body)
- Domain decomposition for parallel simulation
- Haptic force feedback for tactile interfaces

## Research Foundation

This pillar implements algorithms from peer-reviewed research:

- **SPH Kernels**: Poly6, Spiky, Viscosity kernels (Müller et al. 2003)
- **Neighbor Search**: Octree and hash grid (SIGGRAPH Asia 2022)
- **Projective Dynamics**: Local-global optimization (Bouaziz et al. 2014)
- **Domain Decomposition**: SIGGRAPH 2025 parallel projective dynamics
- **Fluid Viscosity**: EUROGRAPHICS 2019 viscous fluid dynamics

## Module Structure

```
src/Hydrogen/Schema/Physics/
├── Force.purs                 # Leader: re-exports Force/*
│   ├── Force/Types.purs       # Force2D vector type
│   ├── Force/Conservative.purs # Gravity, spring, point forces
│   ├── Force/Dissipative.purs # Drag, friction, damping
│   ├── Force/Fields.purs      # Force field composition
│   └── Force/Internal.purs    # Internal helpers
├── Collision.purs             # Leader: re-exports Collision/*
│   ├── Collision/Point.purs   # 2D point primitives
│   ├── Collision/Volumes.purs # AABB, Circle, Capsule, OBB
│   ├── Collision/Contact.purs # Contact point, normal, depth
│   ├── Collision/Detection.purs # Narrow-phase algorithms
│   ├── Collision/Response.purs # Bounce, slide, stick
│   ├── Collision/Layers.purs  # Layer filtering system
│   ├── Collision/State.purs   # Collision state tracking
│   └── Collision/Internal.purs # Internal helpers
├── Fluid.purs                 # Leader: re-exports Fluid/*
│   ├── Fluid/Core.purs        # Graded effects, AST, constraints
│   ├── Fluid/Solver.purs      # Grid-based Eulerian solver
│   ├── Fluid/Particle.purs    # SPH Lagrangian simulation
│   ├── Fluid/Intent.purs      # Semantic mapping for AI
│   └── Fluid/Neighborhood.purs # Spatial data structures
├── Projective/Core.purs       # Projective dynamics solver
├── Projective/Domain.purs     # Domain decomposition
└── Haptic/Force.purs          # Haptic force feedback
```

────────────────────────────────────────────────────────────────────────────────
                                                                // force // atoms
────────────────────────────────────────────────────────────────────────────────

## Force2D

2D force vector with bounded components to prevent numerical instability.

| Field | Type | Min | Max | Behavior | Notes |
|-------|------|-----|-----|----------|-------|
| x | Number | -10000.0 | 10000.0 | clamps | X component |
| y | Number | -10000.0 | 10000.0 | clamps | Y component |

**Operations:**
```purescript
forceZero      :: Force2D                           -- Zero force
forceUp        :: Force2D                           -- (0, -1)
forceDown      :: Force2D                           -- (0, 1)
forceLeft      :: Force2D                           -- (-1, 0)
forceRight     :: Force2D                           -- (1, 0)
forceMagnitude :: Force2D -> Number                 -- |F|
forceDirection :: Force2D -> Number                 -- atan2(y, x)
forceNormalize :: Force2D -> Force2D               -- F / |F|
forceScale     :: Number -> Force2D -> Force2D     -- scalar × F
forceAdd       :: Force2D -> Force2D -> Force2D    -- F₁ + F₂
forceSubtract  :: Force2D -> Force2D -> Force2D    -- F₁ - F₂
forceDot       :: Force2D -> Force2D -> Number     -- F₁ · F₂
forceClamp     :: Number -> Force2D -> Force2D     -- Clamp magnitude
```

**ForceType Enum:**

| Constructor | Description |
|-------------|-------------|
| `Conservative` | Path-independent, has potential energy (gravity, spring) |
| `NonConservative` | Path-dependent, dissipates energy (drag, friction) |

────────────────────────────────────────────────────────────────────────────────
                                                       // conservative // forces
────────────────────────────────────────────────────────────────────────────────

## Gravity

Constant force in a fixed direction. Used for UI weight simulation.

| Field | Type | Min | Max | Behavior | Notes |
|-------|------|-----|-----|----------|-------|
| magnitude | Number | 0.0 | 1000.0 | clamps | Acceleration (m/s²) |
| direction | Force2D | — | — | normalized | Unit vector |

**Presets:**

| Name | Magnitude | Description |
|------|-----------|-------------|
| `gravityEarth` | 9.8 | Earth gravity (heavy UI feel) |
| `gravityMoon` | 1.62 | Moon gravity (floaty feel) |
| `gravityLight` | 2.0 | Light gravity (subtle effects) |
| `gravityHeavy` | 20.0 | Heavy gravity (weighty feel) |
| `gravityZero` | 0.0 | No gravity |

**The Math:**
```
F_gravity = m × g × direction_unit_vector
```

## SpringForce (Hooke's Law)

Proportional to displacement from rest position. Creates oscillatory motion.

| Field | Type | Min | Max | Behavior | Notes |
|-------|------|-----|-----|----------|-------|
| stiffness | Number | 0.0 | 10000.0 | clamps | Spring constant k |
| restLength | Number | 0.0 | 10000.0 | clamps | Natural length |

**Presets:**

| Name | Stiffness | Description |
|------|-----------|-------------|
| `springForceDefault` | 100.0 | Moderate stiffness |
| `springForceSoft` | 30.0 | Low stiffness, slow oscillation |
| `springForceStiff` | 300.0 | High stiffness, fast oscillation |

**The Math (Hooke's Law):**
```
F_spring = -k × (|displacement| - restLength) × direction
```

**Potential Energy:**
```
U = ½ × k × (displacement - restLength)²
```

## PointForce (Attraction/Repulsion)

Force from a point source with distance falloff. Used for magnetic UI elements,
particle effects, snap-to-point behavior.

| Field | Type | Min | Max | Behavior | Notes |
|-------|------|-----|-----|----------|-------|
| strength | Number | -10000.0 | 10000.0 | clamps | Positive = attract |
| falloff | Number | 0.0 | 4.0 | clamps | Distance exponent |
| minDistance | Number | — | — | fixed 1.0 | Prevents infinite force |

**Factory Functions:**
- `attractiveForce strength` — Pulls toward point (positive strength)
- `repulsiveForce strength` — Pushes away from point (negative strength)

**The Math (Inverse Power Law):**
```
F_point = (strength / distance^falloff) × direction
```

Where falloff = 2 gives inverse-square law (Coulomb/gravity).

────────────────────────────────────────────────────────────────────────────────
                                                       // dissipative // forces
────────────────────────────────────────────────────────────────────────────────

## DragForce

Proportional to velocity. Opposes motion, slowing objects down.

| Field | Type | Min | Max | Behavior | Notes |
|-------|------|-----|-----|----------|-------|
| coefficient | Number | 0.0 | 100.0 | clamps | Drag coefficient c |

**Presets:**

| Name | Coefficient | Description |
|------|-------------|-------------|
| `dragForceLight` | 0.5 | Minimal resistance |
| `dragForceMedium` | 2.0 | Balanced |
| `dragForceHeavy` | 8.0 | Strong resistance |

**The Math (Linear Drag):**
```
F_drag = -c × velocity
```

## FrictionForce

Opposes motion at contact surfaces. Has static and kinetic regimes.

| Field | Type | Min | Max | Behavior | Notes |
|-------|------|-----|-----|----------|-------|
| staticCoeff | Number | 0.0 | 2.0 | clamps | μs (prevents motion) |
| kineticCoeff | Number | 0.0 | 2.0 | clamps | μk (during motion) |

**Presets:**

| Name | Static | Kinetic | Description |
|------|--------|---------|-------------|
| `frictionIce` | 0.1 | 0.03 | Very slippery |
| `frictionRubber` | 1.0 | 0.8 | High grip |

**The Math:**
```
F_friction = -μk × |F_normal| × velocity_direction
```

## DampingForce

Viscous resistance for oscillation control. Critical damping returns to
equilibrium fastest without overshooting.

| Field | Type | Min | Max | Behavior | Notes |
|-------|------|-----|-----|----------|-------|
| coefficient | Number | 0.0 | 1000.0 | clamps | Damping coefficient |

**Presets:**

| Name | Coefficient | Description |
|------|-------------|-------------|
| `dampingLight` | 5.0 | Underdamped (bouncy) |
| `dampingCritical` | 20.0 | Critical (no overshoot) |
| `dampingHeavy` | 50.0 | Overdamped (sluggish) |

**The Math:**
```
F_damping = -c × velocity
```

**Critical Damping Condition:**
```
c_critical = 2 × √(k × m)
```

────────────────────────────────────────────────────────────────────────────────
                                                             // force // fields
────────────────────────────────────────────────────────────────────────────────

## ForceField

Spatial distribution of forces. Composable for complex force environments.

**ForceField Sum Type:**

| Constructor | Description |
|-------------|-------------|
| `EmptyField` | No forces |
| `UniformField Force2D` | Same force everywhere |
| `CompositeField (Array ForceField)` | Multiple combined fields |

**Operations:**
```purescript
emptyField      :: ForceField                              -- No forces
uniformField    :: Force2D -> ForceField                   -- Constant force
addForceToField :: ForceField -> ForceField -> ForceField  -- Combine
fieldForceAt    :: ForceField -> Force2D -> Force2D        -- Evaluate at point
fieldContains   :: ForceField -> Boolean                   -- Has any force?
```

**Force Application:**
```purescript
applyForce            :: Force2D -> Number -> Force2D      -- a = F/m
netForce              :: Array Force2D -> Force2D          -- Sum all forces
accelerationFromForce :: Force2D -> Number -> Force2D      -- F/m
```

────────────────────────────────────────────────────────────────────────────────
                                                           // collision // atoms
────────────────────────────────────────────────────────────────────────────────

## Point2D

2D point for collision geometry (local definition to avoid circular deps).

| Field | Type | Description |
|-------|------|-------------|
| x | Number | X coordinate |
| y | Number | Y coordinate |

**Operations:**
```purescript
point2D        :: Number -> Number -> Point2D
origin2D       :: Point2D                            -- (0, 0)
distance       :: Point2D -> Point2D -> Number       -- Euclidean distance
distanceSquared :: Point2D -> Point2D -> Number      -- Faster (no sqrt)
midpoint       :: Point2D -> Point2D -> Point2D
offsetPoint    :: Point2D -> Number -> Number -> Point2D
normalizePoint :: Point2D -> Point2D                 -- Unit length
negatePoint    :: Point2D -> Point2D
```

────────────────────────────────────────────────────────────────────────────────
                                                        // collision // volumes
────────────────────────────────────────────────────────────────────────────────

## AABB (Axis-Aligned Bounding Box)

Fastest collision primitive. Edges parallel to coordinate axes — no rotation.

| Field | Type | Description |
|-------|------|-------------|
| minX | Number | Left edge |
| minY | Number | Top edge |
| maxX | Number | Right edge |
| maxY | Number | Bottom edge |

**Operations:**
```purescript
aabb           :: Number -> Number -> Number -> Number -> AABB
aabbFromPoints :: Point2D -> Point2D -> AABB
aabbCenter     :: AABB -> Point2D
aabbSize       :: AABB -> { width :: Number, height :: Number }
aabbHalfSize   :: AABB -> { hx :: Number, hy :: Number }
aabbContains   :: AABB -> Point2D -> Boolean
aabbExpand     :: Number -> AABB -> AABB
aabbMerge      :: AABB -> AABB -> AABB
```

## BoundingCircle

Rotationally invariant — rotation doesn't change the bounds.

| Field | Type | Min | Max | Behavior | Notes |
|-------|------|-----|-----|----------|-------|
| center | Point2D | — | — | — | Circle center |
| radius | Number | 0.0 | 100000.0 | clamps | Circle radius |

**Operations:**
```purescript
boundingCircle :: Point2D -> Number -> BoundingCircle
circleContains :: BoundingCircle -> Point2D -> Boolean
circleExpand   :: Number -> BoundingCircle -> BoundingCircle
circleMerge    :: BoundingCircle -> BoundingCircle -> BoundingCircle
```

## BoundingCapsule (Stadium)

Two circles connected by a rectangle. Good for elongated moving objects
(characters, bullets, swept collision).

| Field | Type | Min | Max | Behavior | Notes |
|-------|------|-----|-----|----------|-------|
| pointA | Point2D | — | — | — | First endpoint |
| pointB | Point2D | — | — | — | Second endpoint |
| radius | Number | 0.0 | 100000.0 | clamps | Capsule thickness |

**Operations:**
```purescript
boundingCapsule       :: Point2D -> Point2D -> Number -> BoundingCapsule
capsuleContains       :: BoundingCapsule -> Point2D -> Boolean
pointToSegmentDistance :: Point2D -> Point2D -> Point2D -> Number
```

## OBB (Oriented Bounding Box)

Like AABB but can be rotated. Tighter fit for rotated objects.

| Field | Type | Min | Max | Behavior | Notes |
|-------|------|-----|-----|----------|-------|
| center | Point2D | — | — | — | Box center |
| halfWidth | Number | 0.0 | 100000.0 | clamps | Half-width (local X) |
| halfHeight | Number | 0.0 | 100000.0 | clamps | Half-height (local Y) |
| rotation | Number | — | — | radians | Rotation angle |

**Operations:**
```purescript
obb         :: Point2D -> Number -> Number -> Number -> OBB
obbCorners  :: OBB -> { tl, tr, bl, br :: Point2D }
obbContains :: OBB -> Point2D -> Boolean
```

────────────────────────────────────────────────────────────────────────────────
                                                        // collision // contact
────────────────────────────────────────────────────────────────────────────────

## Contact

Result of collision detection. Contains everything needed for resolution.

**Contact Sum Type:**

| Constructor | Description |
|-------------|-------------|
| `NoContact` | No collision detected |
| `Contact { point, normal, depth }` | Collision with details |

| Field | Type | Behavior | Notes |
|-------|------|----------|-------|
| point | Point2D | — | Contact point (on first object) |
| normal | Point2D | normalized | Points from first to second object |
| depth | Number | clamps [0, 10000] | Penetration depth |

**Operations:**
```purescript
contact       :: Point2D -> Point2D -> Number -> Contact
noContact     :: Contact
hasContact    :: Contact -> Boolean
contactPoint  :: Contact -> Point2D
contactNormal :: Contact -> Point2D
contactDepth  :: Contact -> Number
flipContact   :: Contact -> Contact    -- Swap object order
```

────────────────────────────────────────────────────────────────────────────────
                                                      // collision // detection
────────────────────────────────────────────────────────────────────────────────

## Detection Algorithms

Narrow-phase collision detection for pairs of bounding volumes.

### AABB Detection

```purescript
aabbVsAABB   :: AABB -> AABB -> Contact           -- Box vs Box
aabbVsPoint  :: AABB -> Point2D -> Contact        -- Box vs Point
aabbVsCircle :: AABB -> BoundingCircle -> Contact -- Box vs Circle
```

**AABB vs AABB Algorithm:**
1. Check separation on each axis (SAT)
2. Calculate overlap on X and Y axes
3. Contact normal is along minimum overlap axis
4. Contact point is at edge intersection

### Circle Detection

```purescript
circleVsCircle :: BoundingCircle -> BoundingCircle -> Contact
circleVsPoint  :: BoundingCircle -> Point2D -> Contact
circleVsAABB   :: BoundingCircle -> AABB -> Contact
```

**Circle vs Circle Algorithm:**
1. Calculate distance between centers
2. Compare to sum of radii
3. Contact normal is center-to-center direction
4. Contact point is on surface of first circle

### Capsule Detection

```purescript
capsuleVsPoint   :: BoundingCapsule -> Point2D -> Contact
capsuleVsCapsule :: BoundingCapsule -> BoundingCapsule -> Contact
```

**Point to Segment Distance:**
Used for capsule collision. Projects point onto line segment, returns distance
to closest point on segment.

```purescript
pointToSegmentDistance :: Point2D -> Point2D -> Point2D -> Number
segmentSegmentDistance :: Point2D -> Point2D -> Point2D -> Point2D -> Number
```

────────────────────────────────────────────────────────────────────────────────
                                                       // collision // response
────────────────────────────────────────────────────────────────────────────────

## CollisionResponse

What happens when two objects collide.

**CollisionResponse Sum Type:**

| Constructor | Description |
|-------------|-------------|
| `ResponseNone` | Pass through (no physics) |
| `ResponseBounce { restitution }` | Elastic bounce (0=inelastic, 1=perfect) |
| `ResponseSlide { friction }` | Slide along surface |
| `ResponseStick` | Adhere to surface |
| `ResponseCustom { id }` | Application-specific |

**Factory Functions:**
```purescript
responseNone   :: CollisionResponse
responseBounce :: Number -> CollisionResponse  -- restitution 0-1
responseSlide  :: Number -> CollisionResponse  -- friction 0-2
responseStick  :: CollisionResponse
```

**Response Calculations:**

```purescript
-- Calculate position offset to resolve overlap
resolveOverlap :: Contact -> { dx :: Number, dy :: Number }

-- Reflect velocity around contact normal with restitution
calculateBounce :: { vx, vy } -> Contact -> Number -> { vx, vy }

-- Project velocity onto surface tangent with friction
calculateSlide :: { vx, vy } -> Contact -> Number -> { vx, vy }
```

**Bounce Formula:**
```
v' = v - (1 + e) × (v · n) × n
```
Where e = restitution coefficient.

**Slide Formula:**
```
v_tangent = v - (v · n) × n
v' = v_tangent × (1 - μ)
```
Where μ = friction coefficient.

────────────────────────────────────────────────────────────────────────────────
                                                         // collision // layers
────────────────────────────────────────────────────────────────────────────────

## Collision Layers

Filter which objects can collide with each other.

**CollisionLayer** — Which layer an object belongs to (bit flag).

**CollisionMask** — Which layers an object can collide with.

**Operations:**
```purescript
layerCollides :: CollisionLayer -> CollisionMask -> Boolean
allLayers     :: CollisionMask    -- Collides with everything
noLayers      :: CollisionMask    -- Collides with nothing
```

**Use Cases:**
- Player layer: collides with environment and enemies
- Enemy layer: collides with player and environment
- Projectile layer: collides with enemies only
- UI layer: pass-through (no collision)

────────────────────────────────────────────────────────────────────────────────
                                                          // collision // state
────────────────────────────────────────────────────────────────────────────────

## CollisionState

Tracks collision phase over time for event-based behavior.

**CollisionState Enum:**

| Constructor | Description |
|-------------|-------------|
| `NotColliding` | Objects are separated |
| `Colliding` | Objects are overlapping |
| `Separating` | Were colliding, now separating (trigger OnExit) |
| `Resting` | Stable contact, not moving relative |
| `Sliding` | In contact, sliding past each other |
| `Rolling` | One object rolling on another |

**Queries:**
```purescript
isColliding  :: CollisionState -> Boolean  -- Any active contact
isSeparating :: CollisionState -> Boolean  -- Just ended contact
isResting    :: CollisionState -> Boolean  -- Stable, non-moving
```

────────────────────────────────────────────────────────────────────────────────
                                                              // fluid // graded
────────────────────────────────────────────────────────────────────────────────

## FluidEffect (Graded Monad)

What a fluid simulation CAN DO. Tracks capabilities at the type level.

**FluidEffect Sum Type:**

| Constructor | Description |
|-------------|-------------|
| `EffectNone` | Pure computation, no side effects |
| `EffectEmit` | Can emit new particles |
| `EffectForce` | Can apply forces |
| `EffectTransfer` | Can transfer mass between cells |
| `EffectTopology` | Can modify connectivity |
| `EffectRender` | Can produce render output |
| `EffectComposite (Array FluidEffect)` | Multiple combined effects |

**Monoid Instance:**
```purescript
effectCombine :: FluidEffect -> FluidEffect -> FluidEffect  -- E₁ ⊗ E₂
effectNone    :: FluidEffect                                 -- Identity
effectAll     :: FluidEffect                                 -- All effects
```

## FluidCoEffect (Resource Requirements)

What a fluid simulation NEEDS (dependencies).

**FluidCoEffect Sum Type:**

| Constructor | Description |
|-------------|-------------|
| `CoEffectNone` | No special requirements |
| `CoEffectNeighbors` | Needs spatial neighbor lookup |
| `CoEffectGrid` | Needs Eulerian grid |
| `CoEffectGPU` | Benefits from GPU acceleration |
| `CoEffectMemory Int` | Memory bound (bytes) |
| `CoEffectBandwidth Int` | Bandwidth bound (bytes/sec) |
| `CoEffectComposite (Array FluidCoEffect)` | Multiple requirements |

────────────────────────────────────────────────────────────────────────────────
                                                                // fluid // ast
────────────────────────────────────────────────────────────────────────────────

## FluidExpr (Simulation AST)

Fluid simulation as pure data. Every expression carries effect grade and
co-effect requirements, enabling static analysis and optimization.

**FluidExpr Sum Type:**

| Constructor | Description |
|-------------|-------------|
| `FluidPure Number` | Pure value |
| `FluidParticleOp ParticleOp` | SPH particle operation |
| `FluidSolverOp SolverOp` | Grid solver operation |
| `FluidSeq FluidExpr FluidExpr` | Sequential (then) |
| `FluidPar FluidExpr FluidExpr` | Parallel (independent) |
| `FluidIf FluidExpr FluidExpr FluidExpr` | Conditional |
| `FluidLoop Int FluidExpr` | Bounded iteration |
| `FluidAnnotate FluidEffect FluidExpr` | Effect annotation |

**ParticleOp Enum:**

| Constructor | Effect | CoEffect | Description |
|-------------|--------|----------|-------------|
| `OpEmitParticle` | Emit | Memory(64) | Create particle |
| `OpRemoveParticle` | Topology | None | Delete particle |
| `OpMoveParticle` | None | None | Update position |
| `OpAccelerate` | Force | None | Apply acceleration |
| `OpComputeDensity` | None | Neighbors | SPH density |
| `OpComputePressure` | None | None | SPH pressure |
| `OpComputeViscosity` | Force | Neighbors | Viscosity force |
| `OpFindNeighbors` | None | GPU | Neighbor search |

**SolverOp Enum:**

| Constructor | Effect | CoEffect | Description |
|-------------|--------|----------|-------------|
| `OpAdvect` | None | Grid | Semi-Lagrangian advection |
| `OpDiffuse` | None | Grid | Viscosity diffusion |
| `OpProject` | None | Grid | Pressure projection |
| `OpApplyGravity` | Force | None | External forces |
| `OpEnforceBoundary` | None | Grid | Boundary conditions |
| `OpTransferToGrid` | Transfer | Grid+Neighbors | Particles to grid (FLIP) |
| `OpTransferToParticles` | Transfer | Grid+Neighbors | Grid to particles (FLIP) |

────────────────────────────────────────────────────────────────────────────────
                                                          // fluid // constraints
────────────────────────────────────────────────────────────────────────────────

## FluidConstraint (Presburger Arithmetic)

All constraints are decidable via Presburger arithmetic (linear integer
arithmetic without multiplication).

**FluidConstraint Sum Type:**

| Constructor | Description |
|-------------|-------------|
| `ConstraintParticleCount Int Int` | current <= max |
| `ConstraintGridDimension Int Int` | current <= max |
| `ConstraintMemory Int Int` | cost <= budget (bytes) |
| `ConstraintFrameTime Number Number` | time <= budget (ms) |
| `ConstraintAnd a b` | Conjunction |
| `ConstraintTrue` | Always satisfied |
| `ConstraintFalse` | Never satisfied |

**Factory Functions:**
```purescript
particleCountBound :: Int -> Int -> FluidConstraint
gridDimensionBound :: Int -> Int -> FluidConstraint
memoryCostBound    :: Int -> Int -> FluidConstraint
constraintSatisfied :: FluidConstraint -> Boolean
```

## FluidObjective (ILP Optimization)

Quality vs. performance tradeoffs as Integer Linear Programming.

**QualityMetric Enum:**

| Constructor | Description |
|-------------|-------------|
| `QualityParticleCount` | More particles = better |
| `QualityGridResolution` | Higher resolution = better |
| `QualitySolverIterations` | More iterations = better |
| `QualityTimestep` | Smaller timestep = better (inverted) |

**PerformanceMetric Enum:**

| Constructor | Description |
|-------------|-------------|
| `PerfFrameTime` | Minimize frame time |
| `PerfMemoryUsage` | Minimize memory |
| `PerfBandwidth` | Minimize bandwidth |
| `PerfGPUOccupancy` | Maximize GPU utilization |

────────────────────────────────────────────────────────────────────────────────
                                                            // fluid // solver
────────────────────────────────────────────────────────────────────────────────

## VelocityField (Eulerian Grid)

2D velocity field on a staggered MAC grid.

| Field | Type | Description |
|-------|------|-------------|
| width | Int | Grid width |
| height | Int | Grid height |
| velocities | Array Velocity | u, v at each cell |

**Velocity Type:**
```purescript
type Velocity = { u :: Number, v :: Number }
```

**Operations:**
```purescript
mkVelocityField   :: Int -> Int -> VelocityField
getVelocityAt     :: VelocityField -> Int -> Int -> Velocity
setVelocityAt     :: VelocityField -> Int -> Int -> Velocity -> VelocityField
clearVelocityField :: VelocityField -> VelocityField
```

## FluidProperties

Physical properties of the simulated fluid.

| Field | Type | Unit | Description |
|-------|------|------|-------------|
| viscosity | Number | Pa*s | Dynamic viscosity |
| density | Number | kg/m3 | Fluid density |
| surfaceTension | Number | N/m | Surface tension coefficient |

**Presets:**

| Name | Viscosity | Density | Description |
|------|-----------|---------|-------------|
| `defaultPaint` | 0.5 | 1200.0 | Medium viscosity paint |
| `waterPaint` | 0.01 | 1000.0 | Watercolor (low viscosity) |
| `oilPaint` | 2.0 | 1300.0 | Oil paint (high viscosity) |
| `honeyPaint` | 10.0 | 1400.0 | Honey-like (very thick) |

## SolverConfig

Configuration for the grid-based solver.

| Field | Type | Default | Description |
|-------|------|---------|-------------|
| iterations | Int | 20 | Pressure solver iterations |
| timestep | Number | 0.016 | Time step (seconds) |
| cellSize | Number | 0.01 | Cell size (meters) |

**Presets:**

| Name | Iterations | Description |
|------|------------|-------------|
| `defaultSolverConfig` | 20 | Standard quality |
| `highQualitySolver` | 50 | More iterations |

## Simulation Steps

Standard Navier-Stokes pipeline:

```purescript
-- Semi-Lagrangian advection (trace particles backward)
advect :: VelocityField -> SolverConfig -> VelocityField

-- Apply external forces (gravity)
applyForces :: VelocityField -> ExternalForces -> SolverConfig -> VelocityField

-- Viscosity diffusion (Jacobi iteration)
diffuse :: VelocityField -> FluidProperties -> SolverConfig -> VelocityField

-- Pressure projection (make divergence-free)
project :: VelocityField -> SolverConfig -> VelocityField

-- Complete solver step
solverStep :: VelocityField -> FluidProperties -> ExternalForces -> SolverConfig -> VelocityField
```

**Analysis Functions:**
```purescript
maxVelocity   :: VelocityField -> Number
divergence    :: VelocityField -> Int -> Int -> Number
kineticEnergy :: VelocityField -> FluidProperties -> Number
```

────────────────────────────────────────────────────────────────────────────────
                                                           // fluid // particle
────────────────────────────────────────────────────────────────────────────────

## Particle (SPH)

Single particle in Smoothed Particle Hydrodynamics simulation.

| Field | Type | Description |
|-------|------|-------------|
| id | Int | Unique identifier |
| x, y | Number | Position |
| vx, vy | Number | Velocity |
| mass | Number | Particle mass (>= 0.001) |
| density | Number | Computed density |
| pressure | Number | Computed pressure |
| viscosity | Number | Viscosity coefficient |

## SPH Kernels

Smoothing kernels for particle interpolation.

**KernelType Enum:**

| Constructor | Use Case | Description |
|-------------|----------|-------------|
| `Poly6Kernel` | Density | General interpolation |
| `SpikyKernel` | Pressure | Avoids particle clumping |
| `ViscosityKernel` | Viscosity | Viscous forces |

**Kernel Functions:**

```purescript
-- Poly6: W(r, h) = 315 / (64*pi*h^9) * (h^2 - r^2)^3
kernelPoly6 :: Number -> Number -> Number

-- Spiky: W(r, h) = 15 / (pi*h^6) * (h - r)^3
kernelSpiky :: Number -> Number -> Number

-- Viscosity: Complex formula for viscous forces
kernelViscosity :: Number -> Number -> Number

-- Gradient of spiky (pressure force)
kernelGradientSpiky :: Number -> Number -> Number

-- Laplacian of viscosity
kernelLaplacianViscosity :: Number -> Number -> Number
```

**SPH Interpolation Formula:**
```
A(r) = sum_j m_j * (A_j / rho_j) * W(r - r_j, h)
```
Where:
- m_j = particle mass
- rho_j = particle density
- W = smoothing kernel
- h = smoothing radius

## ParticleSystem

Collection of particles with simulation parameters.

| Field | Type | Description |
|-------|------|-------------|
| particles | Array Particle | All particles |
| smoothingRadius | Number | SPH kernel radius h |
| restDensity | Number | Target fluid density |
| stiffness | Number | Pressure stiffness k |
| viscosityCoeff | Number | Global viscosity |
| gravity | { x, y } | Gravity vector |

**Density Computation:**
```purescript
computeDensity      :: ParticleSystem -> Particle -> Number
computeAllDensities :: ParticleSystem -> ParticleSystem
```

**Pressure Computation (Tait Equation):**
```
p = k * (rho - rho_0)
```

**Force Computation:**
```purescript
computePressureForce  :: ParticleSystem -> Particle -> { fx, fy }
computeViscosityForce :: ParticleSystem -> Particle -> { fx, fy }
computeGravityForce   :: ParticleSystem -> Particle -> { fx, fy }
computeTotalForce     :: ParticleSystem -> Particle -> { fx, fy }
```

**Integration (Symplectic Euler):**
```purescript
integrateParticle :: ParticleSystem -> Particle -> Number -> Particle
integrateSystem   :: ParticleSystem -> Number -> ParticleSystem
```

## BoundaryType

How particles interact with boundaries.

| Constructor | Description |
|-------------|-------------|
| `ReflectBoundary` | Bounce off walls |
| `ClampBoundary` | Stop at walls |
| `WrapBoundary` | Periodic boundaries |

────────────────────────────────────────────────────────────────────────────────
                                                             // fluid // intent
────────────────────────────────────────────────────────────────────────────────

## FluidIntent (Semantic Mapping for AI)

Maps human descriptions to simulation parameters. Training data for AI models.

**FluidBehavior Enum:**

| Constructor | Keywords | Description |
|-------------|----------|-------------|
| `Flowing` | flow, stream, river | Continuous movement |
| `Dripping` | drip, drop, bead | Discrete drops falling |
| `Pooling` | pool, puddle, collect | Settling in low areas |
| `Splashing` | splash, spray, burst | Impact dispersion |
| `Spreading` | spread, seep, bleed | Expanding outward |
| `Mixing` | mix, blend, swirl | Fluids combining |
| `Drying` | dry, evaporate, set | Wet to solid transition |
| `Toppling` | topple, collapse, slump | Thick fluid falling |

**ViscosityClass Enum:**

| Constructor | Coefficient (Pa*s) | Examples |
|-------------|-------------------|----------|
| `Watery` | 0.001 | Water, alcohol, thin ink |
| `Milky` | 0.05 | Milk, light cream |
| `Syrupy` | 0.5 | Maple syrup, shampoo |
| `Oily` | 5.0 | Motor oil, glycerin |
| `Honey` | 50.0 | Honey, thick paint |
| `Tar` | 500.0 | Tar, molasses |
| `Solid` | 5000.0 | Modeling clay, putty |

**ScaleClass Enum:**

| Constructor | Particle Count | Grid Resolution | Description |
|-------------|---------------|-----------------|-------------|
| `Microscopic` | 50 | 32x32 | Single drops |
| `Small` | 500 | 64x64 | Brush strokes |
| `Medium` | 5000 | 128x128 | Puddles, blobs |
| `Large` | 50000 | 256x256 | Poured paint |
| `Massive` | 500000 | 512x512 | Floods |

**InteractionType Enum:**

| Constructor | Description |
|-------------|-------------|
| `Passive` | Just watching (gravity, drying) |
| `Painting` | Brush strokes adding fluid |
| `Pouring` | Continuous stream |
| `Tilting` | Device orientation affects gravity |
| `Touching` | Direct manipulation |
| `Blowing` | Wind affecting surface |

**SimulationChoice:**
```purescript
chooseSimulation :: FluidIntent -> SimulationChoice
```

| Choice | When |
|--------|------|
| `UseSPH` | Splashing, dripping, small scale |
| `UseGridSolver` | Flowing, pooling, large scale |
| `UseHybrid` | Toppling, best quality |

**Preset Intents (Training Examples):**

| Preset | Behavior | Viscosity | Scale | Description |
|--------|----------|-----------|-------|-------------|
| `intentWaterDrop` | Dripping | Watery | Microscopic | Single water drop |
| `intentHoneyDrip` | Dripping | Honey | Small | Slow honey drip |
| `intentOilPaint` | Spreading | Oily | Medium | Oil paint application |
| `intentWatercolor` | Spreading | Watery | Medium | Watercolor wash |
| `intentInkSplatter` | Splashing | Milky | Small | Ink on impact |
| `intentLavaFlow` | Flowing | Tar | Large | Slow lava |
| `intentMilkPour` | Flowing | Milky | Medium | Milk pouring |
| `intentBloodDrop` | Dripping | Syrupy | Microscopic | Blood drop |

────────────────────────────────────────────────────────────────────────────────
                                                        // fluid // neighborhood
────────────────────────────────────────────────────────────────────────────────

## Spatial Data Structures

Neighbor search is the SPH bottleneck. Naive O(n^2) is intractable at scale.

### UniformGrid

Simple grid with fixed cell size. Good for uniform distributions.

| Field | Type | Description |
|-------|------|-------------|
| bounds | SpatialBounds | World bounds |
| cellSize | Number | Cell size (>= smoothing radius) |
| resolutionX, Y | Int | Grid dimensions |
| cells | Array GridCell | Cell storage |

**Operations:**
```purescript
mkUniformGrid   :: SpatialBounds -> Number -> UniformGrid
insertParticle  :: UniformGrid -> Int -> Number -> Number -> UniformGrid
queryNeighbors  :: UniformGrid -> Number -> Number -> Number -> Array Int
clearGrid       :: UniformGrid -> UniformGrid
rebuildGrid     :: UniformGrid -> Array Particle -> UniformGrid
```

**Complexity:** O(n) build, O(k) query where k = average neighbors.

### Octree (Quadtree in 2D)

Adaptive tree for variable density distributions. Based on SIGGRAPH Asia 2022.

**OctreeNode Sum Type:**

| Constructor | Description |
|-------------|-------------|
| `OctreeLeaf { bounds, particles, depth }` | Leaf with particles |
| `OctreeBranch { bounds, children, depth }` | Internal node |

**OctreeConfig:**

| Field | Type | Description |
|-------|------|-------------|
| maxParticles | Int | Particles before split |
| maxDepth | Int | Maximum tree depth |

**Operations:**
```purescript
mkOctree       :: SpatialBounds -> OctreeConfig -> Octree
octreeInsert   :: Octree -> Int -> Number -> Number -> Octree
octreeQuery    :: Octree -> Number -> Number -> Number -> Array Int
octreeRebuild  :: Octree -> Array Particle -> Octree
octreeDepth    :: Octree -> Int
octreeNodeCount :: Octree -> Int
```

**Complexity:** O(n log n) build, O(k) query.

### HashGrid

Memory-efficient spatial hashing. Good cache locality.

| Field | Type | Description |
|-------|------|-------------|
| cellSize | Number | Hash cell size |
| tableSize | Int | Hash table size |
| buckets | Array (Array Int) | Hash buckets |

**Spatial Hash Function:**
```purescript
spatialHash :: Int -> Int -> Int -> Int
-- h = ((cx * 73856093) + (cy * 19349663)) mod tableSize
```

**Operations:**
```purescript
mkHashGrid      :: Number -> Int -> HashGrid
hashGridInsert  :: HashGrid -> Int -> Number -> Number -> HashGrid
hashGridQuery   :: HashGrid -> Number -> Number -> Number -> Array Int
hashGridClear   :: HashGrid -> HashGrid
```

**Complexity:** O(n) build, O(k) query.

### SearchStrategy Selection

```purescript
chooseStrategy :: Int -> Number -> SearchStrategy
-- particleCount < 100        -> BruteForce
-- densityVariance > 0.5      -> Octree
-- particleCount > 100000     -> HashGrid
-- otherwise                  -> UniformGrid
```

────────────────────────────────────────────────────────────────────────────────
                                                          // projective // core
────────────────────────────────────────────────────────────────────────────────

## Projective Dynamics

Reformulates physics simulation as optimization. Based on SIGGRAPH papers on
cloth and deformable body simulation.

**Core Insight:**
```
x* = argmin_x (1/2h^2)||M^(1/2)(x - x_tilde)||^2 + sum_i w_i/2 ||A_i S_i x - B_i p_i||^2
```

Where:
- x = positions (what we solve for)
- x_tilde = predicted positions (from velocity)
- M = mass matrix
- p_i = auxiliary variables (constraint projections)
- w_i = constraint weights

**Local-Global Solver:**

1. **Local Step** (parallelizable per constraint):
   Project current positions onto constraint manifolds

2. **Global Step** (single linear solve):
   Find positions that best satisfy all projections

### Position and Velocity

3D vectors for projective dynamics.

```purescript
type Position = { x :: Number, y :: Number, z :: Number }
type Velocity = { vx :: Number, vy :: Number, vz :: Number }
```

### Mass

```purescript
type Mass = { value :: Number }
mkMass      :: Number -> Mass      -- Clamps to >= 0.001
inverseMass :: Mass -> Number      -- 1/m
```

### Particle (DOF)

Degree of freedom in the system.

| Field | Type | Description |
|-------|------|-------------|
| id | Int | Unique identifier |
| position | Position | Current position |
| velocity | Velocity | Current velocity |
| mass | Mass | Particle mass |
| predicted | Position | Predicted position for step |

### PDConstraintType

Types of constraints for projective dynamics.

| Constructor | Particles | Description |
|-------------|-----------|-------------|
| `DistancePDConstraint` | 2 | Maintain distance (springs) |
| `BendingPDConstraint` | 4 | Resist bending (cloth) |
| `StretchPDConstraint` | 3 | Resist stretching (triangle) |
| `AttachmentPDConstraint` | 1 | Fix to world position (pins) |
| `VolumePDConstraint` | 4 | Preserve volume (tetrahedron) |
| `CollisionPDConstraint` | 1+ | Prevent penetration |

**Default Stiffness:**

| Type | Stiffness | Notes |
|------|-----------|-------|
| Distance | 1.0 | Standard spring |
| Bending | 0.1 | Soft bending |
| Stretch | 1.0 | Resist stretching |
| Attachment | 10.0 | Strong pins |
| Volume | 1.0 | Volume preservation |
| Collision | 1.0 | Contact response |

### Projection

Result of the local step.

| Field | Type | Description |
|-------|------|-------------|
| constraintId | Int | Which constraint |
| targetPositions | Array Position | Target for each particle |
| energy | Number | Constraint energy |

### SolverConfig

| Field | Type | Default | Description |
|-------|------|---------|-------------|
| iterations | Int | 10 | Local-global iterations |
| timestep | Number | 0.016 | Time step h |
| damping | Number | 0.99 | Velocity damping (0-1) |

**Presets:**

| Name | Iterations | Description |
|------|------------|-------------|
| `defaultSolverConfig` | 10 | Standard |
| `highQualitySolverConfig` | 30 | More iterations |
| `realtimeSolverConfig` | 5 | Fewer iterations |

### Solver Operations

```purescript
-- Local step: project all constraints
projectAllConstraints :: Array Particle -> Array PDConstraint -> Array Projection

-- Global step: solve for positions
globalSolve :: SolverConfig -> Array Particle -> Array Projection -> Array Position

-- Complete integration step
integrateStep :: SolverConfig -> SystemState -> SystemState
```

### Energy Functions

```purescript
constraintEnergy :: Array Particle -> PDConstraint -> Number
totalEnergy      :: SystemState -> Number
kineticEnergy    :: SystemState -> Number
potentialEnergy  :: SystemState -> Number
```

### Vector Utilities

```purescript
distanceBetween :: Position -> Position -> Number
distanceSq      :: Position -> Position -> Number
normalize       :: Position -> Position
dot             :: Position -> Position -> Number
cross           :: Position -> Position -> Position
scale           :: Number -> Position -> Position
add             :: Position -> Position -> Position
subtract        :: Position -> Position -> Position
```

────────────────────────────────────────────────────────────────────────────────
                                                         // projective // domain
────────────────────────────────────────────────────────────────────────────────

## Domain Decomposition

Parallel projective dynamics. Based on SIGGRAPH 2025 paper.

### DomainEffect (Graded)

What domain operations CAN DO.

| Constructor | Description |
|-------------|-------------|
| `EffectNone` | Pure computation |
| `EffectModifyPositions` | Update positions |
| `EffectModifyVelocities` | Update velocities |
| `EffectExchangeBoundary` | Transfer boundary data |
| `EffectSynchronize` | Global barrier |
| `EffectComposite` | Multiple effects |

### DomainCoEffect (Needs)

What domain operations NEED.

| Constructor | Description |
|-------------|-------------|
| `CoEffectNone` | No requirements |
| `CoEffectNeighborDomain` | Adjacent domain data |
| `CoEffectGlobalState` | Full system state |
| `CoEffectConstraints` | Constraint data |
| `CoEffectMemory Int` | Memory (bytes) |
| `CoEffectCPUCores Int` | CPU cores |
| `CoEffectComposite` | Multiple requirements |

### DomainOp

| Constructor | Effect | CoEffect | Description |
|-------------|--------|----------|-------------|
| `OpSolveInterior` | Positions | Constraints | Local step |
| `OpSolveBoundary` | Positions+Exchange | Constraints+Neighbor | Boundary DOFs |
| `OpSolveCorners` | Positions+Sync | Global | Corner DOFs |
| `OpExchangeForces` | Exchange | Neighbor | Transfer forces |
| `OpExchangePositions` | Exchange | Neighbor | Transfer positions |
| `OpComputeResidual` | None | Constraints | Check convergence |
| `OpPartition` | None | Global | Create domains |
| `OpIdentifyBoundaries` | None | Global | Find shared DOFs |
| `OpIdentifyCorners` | None | Global | Find corner DOFs |

### Bounded Types

```purescript
-- DOF index [0, 2^20 - 1] (max ~1 million DOFs)
newtype DOFIndex = DOFIndex Int
mkDOFIndex :: Int -> DOFIndex  -- Clamps to [0, 1048575]

-- Domain ID [0, 1023] (max 1024 domains)
newtype DomainId = DomainId Int
mkDomainId :: Int -> DomainId  -- Clamps to [0, 1023]

-- DOF count [0, 2^24 - 1] (max ~16 million DOFs)
newtype DOFCount = DOFCount Int
mkDOFCount :: Int -> DOFCount  -- Clamps to [0, 16777215]
```

### Domain

| Field | Type | Description |
|-------|------|-------------|
| id | DomainId | Unique identifier |
| interiorDOFs | Array DOFIndex | Solved independently |
| boundaryDOFs | Array DOFIndex | Shared with neighbors |
| constraintIndices | Array Int | Local constraints |

### DomainBoundary

Boundary between two adjacent domains. The "epilogue" in Landauer terms.

| Field | Type | Description |
|-------|------|-------------|
| domainA | DomainId | First domain |
| domainB | DomainId | Second domain |
| sharedDOFs | Array DOFIndex | DOFs shared by both |

### DomainDecomposition

| Field | Type | Description |
|-------|------|-------------|
| domains | Array Domain | All domains |
| boundaries | Array DomainBoundary | All boundaries |
| cornerDOFs | Array DOFIndex | Shared by 3+ domains |

### Constraints (Presburger)

```purescript
domainCountBound   :: Int -> Int -> DomainConstraint  -- domains <= max
dofCountBound      :: Int -> Int -> DomainConstraint  -- dofs <= max
boundaryRatioBound :: Int -> Int -> DomainConstraint  -- boundary% <= max
```

### Metrics

| Metric | Range | Description |
|--------|-------|-------------|
| loadBalance | 0.0-1.0 | min size / max size (1.0 = perfect) |
| boundaryRatio | 0.0-1.0 | boundary DOFs / total DOFs |
| interiorRatio | 0.0-1.0 | interior DOFs / total DOFs |

```purescript
computeMetrics :: DomainDecomposition -> DomainMetrics
```

────────────────────────────────────────────────────────────────────────────────
                                                              // haptic // force
────────────────────────────────────────────────────────────────────────────────

## Haptic Force Feedback

Tactile feedback primitives for BMI/haptic interfaces.

### Physical Units

| Quantity | Type | Unit | Range | Description |
|----------|------|------|-------|-------------|
| Force | Number | N | 0-1000 | Newtons |
| Torque | Number | N*m | 0-100 | Newton-meters |
| Frequency | Number | Hz | 1-1000 | Vibration frequency |
| Duration | Number | ms | 0-10000 | Effect duration |

### Human Perception Bounds

| Threshold | Value | Notes |
|-----------|-------|-------|
| Minimum perceptible force | ~0.01 N | Fingertip |
| Maximum comfortable force | ~50 N | Whole hand grip |
| Peak vibration sensitivity | 200-300 Hz | Pacinian corpuscles |
| Just-noticeable difference | ~7% | Force change detection |

### Unit Conversions

```purescript
newtons      :: Number -> Force       -- Direct
millinewtons :: Number -> Force       -- / 1000
gramsForce   :: Number -> Force       -- * 0.00981
poundsForce  :: Number -> Force       -- * 4.448
```

### HapticPulse

Single brief force application.

| Field | Type | Description |
|-------|------|-------------|
| force | Force | Peak force |
| duration | Duration | Pulse length |

**Click Presets:**

| Name | Force (N) | Duration (ms) | Description |
|------|-----------|---------------|-------------|
| `buttonClick` | 2.0 | 10 | Standard click |
| `softClick` | 0.5 | 8 | Subtle feedback |
| `hardClick` | 5.0 | 15 | Definite feedback |
| `toggleOn` | 3.0 | 12 | Switch on |
| `toggleOff` | 2.0 | 8 | Switch off |

### HapticVibration

Continuous vibration at a frequency.

| Field | Type | Description |
|-------|------|-------------|
| frequency | Frequency | Vibration Hz |
| amplitude | Force | Peak amplitude |
| duration | Duration | Effect length |

**Notification Presets:**

| Name | Freq (Hz) | Amp (N) | Dur (ms) | Description |
|------|-----------|---------|----------|-------------|
| `notificationLight` | 150 | 0.5 | 100 | Gentle alert |
| `notificationMedium` | 200 | 1.0 | 200 | Standard alert |
| `notificationStrong` | 250 | 2.0 | 300 | Urgent alert |
| `warningBuzz` | 100 | 3.0 | 500 | Attention needed |
| `errorBuzz` | 80 | 4.0 | 400 | Error feedback |
| `successPulse` | 250 | 1.5 | 150 | Success confirmation |

### HapticTexture

Texture simulation through modulated vibration.

| Field | Type | Range | Description |
|-------|------|-------|-------------|
| baseFrequency | Frequency | 1-1000 Hz | Base vibration |
| roughness | Number | 0.0-1.0 | 0 = smooth, 1 = rough |
| amplitude | Force | — | Peak amplitude |

**Texture Presets:**

| Name | Freq | Roughness | Description |
|------|------|-----------|-------------|
| `smoothSurface` | 300 | 0.1 | Minimal texture |
| `roughSurface` | 200 | 0.5 | Noticeable texture |
| `sandpaper` | 150 | 0.8 | Coarse texture |
| `corduroy` | 50 | 0.6 | Periodic ridges |
| `bumpyRoad` | 20 | 0.9 | Low freq, high amp |

### HapticImpact

Sharp onset with decay. Used for collision feedback.

| Field | Type | Description |
|-------|------|-------------|
| peakForce | Force | Maximum force at impact |
| attackTime | Duration | Rise time to peak |
| decayTime | Duration | Fall time to zero |

**Impact Presets:**

| Name | Peak (N) | Attack (ms) | Decay (ms) | Description |
|------|----------|-------------|------------|-------------|
| `lightTap` | 1.0 | 2 | 10 | Gentle touch |
| `mediumImpact` | 5.0 | 5 | 30 | Normal collision |
| `heavyImpact` | 15.0 | 8 | 50 | Strong collision |
| `collision` | 30.0 | 3 | 100 | Maximum impact |

### HapticResistance

Continuous spring-like feedback for rotary/linear controls.

| Field | Type | Description |
|-------|------|-------------|
| stiffness | Force | Force per unit displacement |
| damping | Force | Velocity-dependent resistance |
| maxForce | Force | Saturation limit |

**Resistance Presets:**

| Name | Stiffness (N) | Damping (N) | Max (N) | Description |
|------|---------------|-------------|---------|-------------|
| `freeSpin` | 0.0 | 0.0 | 0.0 | No resistance |
| `lightResistance` | 1.0 | 0.5 | 5.0 | Slight pushback |
| `mediumResistance` | 5.0 | 2.0 | 20.0 | Noticeable |
| `heavyResistance` | 15.0 | 5.0 | 50.0 | Strong pushback |
| `hardStop` | 100.0 | 20.0 | 100.0 | Cannot pass |

### Operations

```purescript
scaleForce    :: Number -> Force -> Force
scaleTorque   :: Number -> Torque -> Torque
combineForces :: Force -> Force -> Force
isPerceptible :: Force -> Boolean  -- > 0.01 N
isComfortable :: Force -> Boolean  -- <= 50 N
```

────────────────────────────────────────────────────────────────────────────────
                                                              // uuid5 // identity
────────────────────────────────────────────────────────────────────────────────

## Deterministic Identity

Every physics configuration has a deterministic UUID5.
Same parameters -> same UUID -> reproducible simulation.

**Namespaces:**

| Namespace | Purpose |
|-----------|---------|
| `nsFluidParticle` | Particle identity |
| `nsFluidSolver` | Solver configuration |
| `nsFluidIntent` | Intent specification |
| `nsFluidEffect` | Effect expressions |
| `nsNeighborhood` | Spatial structures |
| `nsProjective` | Projective dynamics |
| `nsPDConstraint` | Constraints |
| `nsDomain` | Domain decomposition |

**UUID Generation:**
```purescript
fluidConfigUUID :: String -> UUID5
particleUUID    :: Int -> Number -> Number -> UUID5
solverUUID      :: Int -> Int -> Number -> UUID5
exprUUID        :: FluidExpr -> UUID5
```

────────────────────────────────────────────────────────────────────────────────
                                                              // source // files
────────────────────────────────────────────────────────────────────────────────

```
src/Hydrogen/Schema/Physics/
├── Force.purs                    71 lines   # Leader module
├── Force/
│   ├── Types.purs               190 lines   # Force2D, ForceType
│   ├── Conservative.purs        272 lines   # Gravity, Spring, Point
│   ├── Dissipative.purs         232 lines   # Drag, Friction, Damping
│   ├── Fields.purs              120 lines   # ForceField composition
│   └── Internal.purs             74 lines   # Internal helpers
├── Collision.purs               159 lines   # Leader module
├── Collision/
│   ├── Point.purs               126 lines   # Point2D primitives
│   ├── Volumes.purs             357 lines   # AABB, Circle, Capsule, OBB
│   ├── Contact.purs             140 lines   # Contact information
│   ├── Detection.purs           294 lines   # Collision algorithms
│   ├── Response.purs            175 lines   # Bounce, Slide, Stick
│   ├── Layers.purs              105 lines   # Layer filtering
│   ├── State.purs                98 lines   # Collision state
│   └── Internal.purs             95 lines   # Internal helpers
├── Fluid.purs                   341 lines   # Leader module
├── Fluid/
│   ├── Core.purs                733 lines   # Graded effects, AST
│   ├── Solver.purs              565 lines   # Eulerian solver
│   ├── Particle.purs            674 lines   # SPH simulation
│   ├── Intent.purs              743 lines   # Semantic mapping
│   └── Neighborhood.purs        825 lines   # Spatial structures
├── Projective/
│   ├── Core.purs                821 lines   # Local-global solver
│   └── Domain.purs              874 lines   # Domain decomposition
└── Haptic/
    └── Force.purs               563 lines   # Haptic feedback

24 files, 8,647 lines total.
```

────────────────────────────────────────────────────────────────────────────────
                                                       // design // philosophy
────────────────────────────────────────────────────────────────────────────────

## Why These Primitives Matter

Physics primitives define **how things move** in response to forces, collisions,
and constraints. Every interactive UI element needs physics: draggable objects
need drag forces, buttons need collision detection, fluid animations need
proper simulation.

**Forces:**
The complete vocabulary of UI physics — gravity for weight, springs for
bounce, drag for smooth stopping. All bounded to prevent numerical explosion.

**Collision:**
Bounding volumes provide cheap broad-phase filtering. Detection algorithms
give exact contact information. Response types enable different physical
behaviors (bouncy vs. sticky).

**Fluid Simulation:**
Two complementary approaches: Eulerian (grid-based) for large flowing bodies,
Lagrangian (SPH) for discrete particles and splashing. Intent mapping enables
AI to select parameters from natural descriptions.

**Projective Dynamics:**
Modern cloth and soft body simulation via optimization. Domain decomposition
enables parallel solving at scale — interior DOFs solve independently,
boundaries reconcile pairwise, corners need global sync.

**Graded Effects:**
Effect and co-effect tracking enables static analysis: what can a simulation
do? what does it need? This enables optimization before execution and safe
composition of simulation components.

**Haptic Feedback:**
Bounded force primitives for tactile interfaces. Human perception limits
inform the bounds — minimum perceptible force, maximum comfortable force,
vibration frequency range.

At billion-agent scale, these primitives enable:
- Deterministic simulation (same input = same motion)
- Parallel execution (domain decomposition)
- Intelligent selection (intent mapping)
- Resource prediction (effect analysis)

────────────────────────────────────────────────────────────────────────────────
