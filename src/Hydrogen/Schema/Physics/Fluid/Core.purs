-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // schema // physics // fluid // core
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Fluid Core — Foundational types for fluid simulation AST.
-- |
-- | ## Design Philosophy
-- |
-- | Fluid simulation is expressed as pure data. Every operation is an AST
-- | node that can be serialized, optimized, and executed on any backend
-- | (CPU, GPU, distributed). Scale-invariant: same AST for 1 or 1 billion
-- | particles.
-- |
-- | ## Graded Effects
-- |
-- | `FluidEffect` tracks what a simulation CAN DO:
-- | - EmitParticles: Create new particles
-- | - ApplyForces: Modify velocities
-- | - TransferMass: Move material between cells
-- | - ModifyTopology: Change connectivity
-- |
-- | ## Co-Effects
-- |
-- | `FluidCoEffect` tracks what a simulation NEEDS:
-- | - NeedsNeighbors: Requires spatial neighbor lookup
-- | - NeedsGrid: Requires Eulerian grid
-- | - NeedsGPU: Benefits from GPU acceleration
-- | - NeedsMemory: Memory bound (particle count)
-- |
-- | ## UUID5 Identity
-- |
-- | Every fluid configuration has a deterministic UUID5.
-- | Same parameters → same UUID → same simulation.
-- |
-- | ## Presburger Constraints
-- |
-- | Particle counts, grid dimensions are bounded integers.
-- | Constraints are decidable via Presburger arithmetic.
-- |
-- | ## ILP Optimization
-- |
-- | Quality vs. performance tradeoffs are ILP problems:
-- | - Maximize quality subject to frame budget
-- | - Minimize memory subject to quality threshold
-- |
-- | ## Dependencies
-- | - Prelude
-- | - Hydrogen.Schema.Attestation.UUID5

module Hydrogen.Schema.Physics.Fluid.Core
  ( -- * UUID5 Namespaces
    nsFluidParticle
  , nsFluidSolver
  , nsFluidIntent
  , nsFluidEffect
  
  -- * Fluid Effects (graded)
  , FluidEffect(..)
  , allFluidEffects
  , effectCombine
  , effectNone
  , effectAll
  
  -- * Fluid Co-Effects (resources needed)
  , FluidCoEffect(..)
  , allFluidCoEffects
  , coEffectCombine
  , coEffectNone
  , coEffectAll
  
  -- * Fluid Expression AST
  , FluidExpr(..)
  , exprEffect
  , exprCoEffect
  , exprUUID
  
  -- * Particle Operations
  , ParticleOp(..)
  , allParticleOps
  
  -- * Solver Operations
  , SolverOp(..)
  , allSolverOps
  
  -- * Constraints (Presburger)
  , FluidConstraint(..)
  , particleCountBound
  , gridDimensionBound
  , memoryCostBound
  , constraintSatisfied
  
  -- * Optimization (ILP)
  , FluidObjective(..)
  , QualityMetric(..)
  , allQualityMetrics
  , PerformanceMetric(..)
  , allPerformanceMetrics
  
  -- * Configuration Identity
  , fluidConfigUUID
  , particleUUID
  , solverUUID
  
  -- * Effect Analysis
  , hasEffect
  , hasAnyEffect
  , isPureExpr
  , estimateMemory
  , estimateCost
  , effectStrongerThan
  , isConstraintTight
  , constraintSlack
  , mapQualityMetrics
  , combineObjectives
  , emptyObjective
  , normalizeCost
  , emptyEffects
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , class Semigroup
  , class Monoid
  , show
  , (==)
  , (&&)
  , (||)
  , (>=)
  , (<=)
  , (<)
  , (>)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  , map
  , mempty
  )

import Data.Array (foldl, elem) as Array
import Hydrogen.Schema.Attestation.UUID5 as UUID5

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // uuid5 namespaces
-- ═════════════════════════════════════════════════════════════════════════════

-- | Namespace for fluid particle UUIDs.
nsFluidParticle :: UUID5.UUID5
nsFluidParticle = UUID5.uuid5 UUID5.nsElement "hydrogen.physics.fluid.particle"

-- | Namespace for fluid solver UUIDs.
nsFluidSolver :: UUID5.UUID5
nsFluidSolver = UUID5.uuid5 UUID5.nsElement "hydrogen.physics.fluid.solver"

-- | Namespace for fluid intent UUIDs.
nsFluidIntent :: UUID5.UUID5
nsFluidIntent = UUID5.uuid5 UUID5.nsElement "hydrogen.physics.fluid.intent"

-- | Namespace for fluid effect UUIDs.
nsFluidEffect :: UUID5.UUID5
nsFluidEffect = UUID5.uuid5 UUID5.nsElement "hydrogen.physics.fluid.effect"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // fluid effects (graded)
-- ═════════════════════════════════════════════════════════════════════════════

-- | What a fluid simulation CAN DO.
-- |
-- | Graded monoid: effects combine via union.
-- | Grade algebra: E₁ ⊗ E₂ = union of capabilities.
data FluidEffect
  = EffectNone           -- ^ Pure computation, no side effects
  | EffectEmit           -- ^ Can emit new particles
  | EffectForce          -- ^ Can apply forces
  | EffectTransfer       -- ^ Can transfer mass between cells
  | EffectTopology       -- ^ Can modify connectivity
  | EffectRender         -- ^ Can produce render output
  | EffectComposite      -- ^ Combination of effects
      (Array FluidEffect)

derive instance eqFluidEffect :: Eq FluidEffect
derive instance ordFluidEffect :: Ord FluidEffect

instance showFluidEffect :: Show FluidEffect where
  show EffectNone = "none"
  show EffectEmit = "emit"
  show EffectForce = "force"
  show EffectTransfer = "transfer"
  show EffectTopology = "topology"
  show EffectRender = "render"
  show (EffectComposite effs) = "composite(" <> show effs <> ")"

instance semigroupFluidEffect :: Semigroup FluidEffect where
  append = effectCombine

instance monoidFluidEffect :: Monoid FluidEffect where
  mempty = EffectNone

-- | All primitive fluid effects.
allFluidEffects :: Array FluidEffect
allFluidEffects = 
  [ EffectNone, EffectEmit, EffectForce
  , EffectTransfer, EffectTopology, EffectRender
  ]

-- | Combine two effects (monoid operation).
effectCombine :: FluidEffect -> FluidEffect -> FluidEffect
effectCombine EffectNone e = e
effectCombine e EffectNone = e
effectCombine (EffectComposite a) (EffectComposite b) = EffectComposite (a <> b)
effectCombine (EffectComposite a) e = EffectComposite (a <> [e])
effectCombine e (EffectComposite b) = EffectComposite ([e] <> b)
effectCombine e1 e2 = if e1 == e2 then e1 else EffectComposite [e1, e2]

-- | No effects (identity).
effectNone :: FluidEffect
effectNone = EffectNone

-- | All effects combined.
effectAll :: FluidEffect
effectAll = EffectComposite allFluidEffects

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // fluid co-effects (needs)
-- ═════════════════════════════════════════════════════════════════════════════

-- | What a fluid simulation NEEDS (resources).
-- |
-- | Co-effect algebra: tracks dependencies.
data FluidCoEffect
  = CoEffectNone            -- ^ No special requirements
  | CoEffectNeighbors       -- ^ Needs spatial neighbor lookup
  | CoEffectGrid            -- ^ Needs Eulerian grid
  | CoEffectGPU             -- ^ Benefits from GPU
  | CoEffectMemory Int      -- ^ Memory bound (bytes)
  | CoEffectBandwidth Int   -- ^ Bandwidth bound (bytes/sec)
  | CoEffectComposite       -- ^ Multiple requirements
      (Array FluidCoEffect)

derive instance eqFluidCoEffect :: Eq FluidCoEffect
derive instance ordFluidCoEffect :: Ord FluidCoEffect

instance showFluidCoEffect :: Show FluidCoEffect where
  show CoEffectNone = "none"
  show CoEffectNeighbors = "neighbors"
  show CoEffectGrid = "grid"
  show CoEffectGPU = "gpu"
  show (CoEffectMemory n) = "memory(" <> show n <> ")"
  show (CoEffectBandwidth n) = "bandwidth(" <> show n <> ")"
  show (CoEffectComposite effs) = "composite(" <> show effs <> ")"

instance semigroupFluidCoEffect :: Semigroup FluidCoEffect where
  append = coEffectCombine

instance monoidFluidCoEffect :: Monoid FluidCoEffect where
  mempty = CoEffectNone

-- | All primitive co-effects.
allFluidCoEffects :: Array FluidCoEffect
allFluidCoEffects = 
  [ CoEffectNone, CoEffectNeighbors, CoEffectGrid, CoEffectGPU ]

-- | Combine co-effects.
coEffectCombine :: FluidCoEffect -> FluidCoEffect -> FluidCoEffect
coEffectCombine CoEffectNone e = e
coEffectCombine e CoEffectNone = e
coEffectCombine (CoEffectMemory a) (CoEffectMemory b) = CoEffectMemory (a + b)
coEffectCombine (CoEffectBandwidth a) (CoEffectBandwidth b) = CoEffectBandwidth (a + b)
coEffectCombine (CoEffectComposite a) (CoEffectComposite b) = CoEffectComposite (a <> b)
coEffectCombine (CoEffectComposite a) e = CoEffectComposite (a <> [e])
coEffectCombine e (CoEffectComposite b) = CoEffectComposite ([e] <> b)
coEffectCombine e1 e2 = if e1 == e2 then e1 else CoEffectComposite [e1, e2]

-- | No co-effects (identity).
coEffectNone :: FluidCoEffect
coEffectNone = CoEffectNone

-- | All co-effects combined.
coEffectAll :: FluidCoEffect
coEffectAll = CoEffectComposite allFluidCoEffects

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // fluid expression ast
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fluid simulation AST.
-- |
-- | Every expression carries its effect grade and co-effect requirements.
-- | This enables static analysis and optimization before execution.
data FluidExpr
  = -- | Pure value (no effects)
    FluidPure Number
    
  | -- | Particle operation
    FluidParticleOp ParticleOp
    
  | -- | Solver operation
    FluidSolverOp SolverOp
    
  | -- | Sequential composition
    FluidSeq FluidExpr FluidExpr
    
  | -- | Parallel composition (independent)
    FluidPar FluidExpr FluidExpr
    
  | -- | Conditional
    FluidIf FluidExpr FluidExpr FluidExpr
    
  | -- | Loop (bounded iteration)
    FluidLoop Int FluidExpr
    
  | -- | Annotated with effect
    FluidAnnotate FluidEffect FluidExpr

derive instance eqFluidExpr :: Eq FluidExpr
derive instance ordFluidExpr :: Ord FluidExpr

instance showFluidExpr :: Show FluidExpr where
  show (FluidPure n) = "pure(" <> show n <> ")"
  show (FluidParticleOp op) = "particle(" <> show op <> ")"
  show (FluidSolverOp op) = "solver(" <> show op <> ")"
  show (FluidSeq e1 e2) = "seq(" <> show e1 <> ", " <> show e2 <> ")"
  show (FluidPar e1 e2) = "par(" <> show e1 <> ", " <> show e2 <> ")"
  show (FluidIf c t e) = "if(" <> show c <> ", " <> show t <> ", " <> show e <> ")"
  show (FluidLoop n e) = "loop(" <> show n <> ", " <> show e <> ")"
  show (FluidAnnotate eff e) = "annotate(" <> show eff <> ", " <> show e <> ")"

-- | Compute effect grade of expression.
exprEffect :: FluidExpr -> FluidEffect
exprEffect (FluidPure _) = EffectNone
exprEffect (FluidParticleOp op) = particleOpEffect op
exprEffect (FluidSolverOp op) = solverOpEffect op
exprEffect (FluidSeq e1 e2) = effectCombine (exprEffect e1) (exprEffect e2)
exprEffect (FluidPar e1 e2) = effectCombine (exprEffect e1) (exprEffect e2)
exprEffect (FluidIf _ t e) = effectCombine (exprEffect t) (exprEffect e)
exprEffect (FluidLoop _ e) = exprEffect e
exprEffect (FluidAnnotate eff _) = eff

-- | Compute co-effect requirements of expression.
exprCoEffect :: FluidExpr -> FluidCoEffect
exprCoEffect (FluidPure _) = CoEffectNone
exprCoEffect (FluidParticleOp op) = particleOpCoEffect op
exprCoEffect (FluidSolverOp op) = solverOpCoEffect op
exprCoEffect (FluidSeq e1 e2) = coEffectCombine (exprCoEffect e1) (exprCoEffect e2)
exprCoEffect (FluidPar e1 e2) = coEffectCombine (exprCoEffect e1) (exprCoEffect e2)
exprCoEffect (FluidIf c t e) = coEffectCombine (exprCoEffect c) 
                                (coEffectCombine (exprCoEffect t) (exprCoEffect e))
exprCoEffect (FluidLoop _ e) = exprCoEffect e
exprCoEffect (FluidAnnotate _ e) = exprCoEffect e

-- | Compute deterministic UUID for expression.
exprUUID :: FluidExpr -> UUID5.UUID5
exprUUID expr = UUID5.uuid5 nsFluidEffect (show expr)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // particle operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Operations on particles.
data ParticleOp
  = OpEmitParticle        -- ^ Create new particle
  | OpRemoveParticle      -- ^ Delete particle
  | OpMoveParticle        -- ^ Update position
  | OpAccelerate          -- ^ Apply acceleration
  | OpComputeDensity      -- ^ SPH density computation
  | OpComputePressure     -- ^ SPH pressure computation
  | OpComputeViscosity    -- ^ SPH viscosity force
  | OpFindNeighbors       -- ^ Neighbor search

derive instance eqParticleOp :: Eq ParticleOp
derive instance ordParticleOp :: Ord ParticleOp

instance showParticleOp :: Show ParticleOp where
  show OpEmitParticle = "emit"
  show OpRemoveParticle = "remove"
  show OpMoveParticle = "move"
  show OpAccelerate = "accelerate"
  show OpComputeDensity = "density"
  show OpComputePressure = "pressure"
  show OpComputeViscosity = "viscosity"
  show OpFindNeighbors = "neighbors"

-- | All particle operations.
allParticleOps :: Array ParticleOp
allParticleOps =
  [ OpEmitParticle, OpRemoveParticle, OpMoveParticle, OpAccelerate
  , OpComputeDensity, OpComputePressure, OpComputeViscosity, OpFindNeighbors
  ]

-- | Effect produced by particle operation.
particleOpEffect :: ParticleOp -> FluidEffect
particleOpEffect OpEmitParticle = EffectEmit
particleOpEffect OpRemoveParticle = EffectTopology
particleOpEffect OpMoveParticle = EffectNone
particleOpEffect OpAccelerate = EffectForce
particleOpEffect OpComputeDensity = EffectNone
particleOpEffect OpComputePressure = EffectNone
particleOpEffect OpComputeViscosity = EffectForce
particleOpEffect OpFindNeighbors = EffectNone

-- | Co-effect required by particle operation.
particleOpCoEffect :: ParticleOp -> FluidCoEffect
particleOpCoEffect OpEmitParticle = CoEffectMemory 64  -- 64 bytes per particle
particleOpCoEffect OpRemoveParticle = CoEffectNone
particleOpCoEffect OpMoveParticle = CoEffectNone
particleOpCoEffect OpAccelerate = CoEffectNone
particleOpCoEffect OpComputeDensity = CoEffectNeighbors
particleOpCoEffect OpComputePressure = CoEffectNone
particleOpCoEffect OpComputeViscosity = CoEffectNeighbors
particleOpCoEffect OpFindNeighbors = CoEffectGPU

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // solver operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Operations on grid solver.
data SolverOp
  = OpAdvect              -- ^ Semi-Lagrangian advection
  | OpDiffuse             -- ^ Viscosity diffusion
  | OpProject             -- ^ Pressure projection
  | OpApplyGravity        -- ^ External forces
  | OpEnforceBoundary     -- ^ Boundary conditions
  | OpTransferToGrid      -- ^ Particles → grid (FLIP)
  | OpTransferToParticles -- ^ Grid → particles (FLIP)

derive instance eqSolverOp :: Eq SolverOp
derive instance ordSolverOp :: Ord SolverOp

instance showSolverOp :: Show SolverOp where
  show OpAdvect = "advect"
  show OpDiffuse = "diffuse"
  show OpProject = "project"
  show OpApplyGravity = "gravity"
  show OpEnforceBoundary = "boundary"
  show OpTransferToGrid = "toGrid"
  show OpTransferToParticles = "toParticles"

-- | All solver operations.
allSolverOps :: Array SolverOp
allSolverOps =
  [ OpAdvect, OpDiffuse, OpProject, OpApplyGravity
  , OpEnforceBoundary, OpTransferToGrid, OpTransferToParticles
  ]

-- | Effect produced by solver operation.
solverOpEffect :: SolverOp -> FluidEffect
solverOpEffect OpAdvect = EffectNone
solverOpEffect OpDiffuse = EffectNone
solverOpEffect OpProject = EffectNone
solverOpEffect OpApplyGravity = EffectForce
solverOpEffect OpEnforceBoundary = EffectNone
solverOpEffect OpTransferToGrid = EffectTransfer
solverOpEffect OpTransferToParticles = EffectTransfer

-- | Co-effect required by solver operation.
solverOpCoEffect :: SolverOp -> FluidCoEffect
solverOpCoEffect OpAdvect = CoEffectGrid
solverOpCoEffect OpDiffuse = CoEffectGrid
solverOpCoEffect OpProject = CoEffectGrid
solverOpCoEffect OpApplyGravity = CoEffectNone
solverOpCoEffect OpEnforceBoundary = CoEffectGrid
solverOpCoEffect OpTransferToGrid = coEffectCombine CoEffectGrid CoEffectNeighbors
solverOpCoEffect OpTransferToParticles = coEffectCombine CoEffectGrid CoEffectNeighbors

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // constraints (presburger)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Linear constraints on fluid simulation parameters.
-- |
-- | All constraints are decidable via Presburger arithmetic.
data FluidConstraint
  = -- | Particle count ≤ bound
    ConstraintParticleCount Int Int     -- current ≤ max
    
  | -- | Grid dimension ≤ bound
    ConstraintGridDimension Int Int     -- current ≤ max
    
  | -- | Memory cost ≤ budget
    ConstraintMemory Int Int            -- cost ≤ budget (bytes)
    
  | -- | Frame time ≤ budget
    ConstraintFrameTime Number Number   -- time ≤ budget (ms)
    
  | -- | Conjunction of constraints
    ConstraintAnd FluidConstraint FluidConstraint
    
  | -- | Always satisfied
    ConstraintTrue
    
  | -- | Never satisfied
    ConstraintFalse

derive instance eqFluidConstraint :: Eq FluidConstraint

instance showFluidConstraint :: Show FluidConstraint where
  show (ConstraintParticleCount c m) = "particles(" <> show c <> " ≤ " <> show m <> ")"
  show (ConstraintGridDimension c m) = "grid(" <> show c <> " ≤ " <> show m <> ")"
  show (ConstraintMemory c m) = "memory(" <> show c <> " ≤ " <> show m <> ")"
  show (ConstraintFrameTime c m) = "time(" <> show c <> " ≤ " <> show m <> ")"
  show (ConstraintAnd a b) = show a <> " ∧ " <> show b
  show ConstraintTrue = "⊤"
  show ConstraintFalse = "⊥"

-- | Create particle count constraint.
particleCountBound :: Int -> Int -> FluidConstraint
particleCountBound current maxCount = ConstraintParticleCount current maxCount

-- | Create grid dimension constraint.
gridDimensionBound :: Int -> Int -> FluidConstraint
gridDimensionBound current maxDim = ConstraintGridDimension current maxDim

-- | Create memory cost constraint.
memoryCostBound :: Int -> Int -> FluidConstraint
memoryCostBound cost budget = ConstraintMemory cost budget

-- | Check if constraint is satisfied.
constraintSatisfied :: FluidConstraint -> Boolean
constraintSatisfied (ConstraintParticleCount c m) = c <= m
constraintSatisfied (ConstraintGridDimension c m) = c <= m
constraintSatisfied (ConstraintMemory c m) = c <= m
constraintSatisfied (ConstraintFrameTime c m) = c <= m
constraintSatisfied (ConstraintAnd a b) = constraintSatisfied a && constraintSatisfied b
constraintSatisfied ConstraintTrue = true
constraintSatisfied ConstraintFalse = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // optimization (ilp)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Quality metrics for fluid simulation.
data QualityMetric
  = QualityParticleCount    -- ^ More particles = better
  | QualityGridResolution   -- ^ Higher resolution = better
  | QualitySolverIterations -- ^ More iterations = better
  | QualityTimestep         -- ^ Smaller timestep = better (inverted)

derive instance eqQualityMetric :: Eq QualityMetric
derive instance ordQualityMetric :: Ord QualityMetric

instance showQualityMetric :: Show QualityMetric where
  show QualityParticleCount = "particle-count"
  show QualityGridResolution = "grid-resolution"
  show QualitySolverIterations = "iterations"
  show QualityTimestep = "timestep"

-- | All quality metrics.
allQualityMetrics :: Array QualityMetric
allQualityMetrics =
  [ QualityParticleCount, QualityGridResolution
  , QualitySolverIterations, QualityTimestep
  ]

-- | Performance metrics for fluid simulation.
data PerformanceMetric
  = PerfFrameTime           -- ^ Frame time (minimize)
  | PerfMemoryUsage         -- ^ Memory usage (minimize)
  | PerfBandwidth           -- ^ Memory bandwidth (minimize)
  | PerfGPUOccupancy        -- ^ GPU utilization (maximize)

derive instance eqPerformanceMetric :: Eq PerformanceMetric
derive instance ordPerformanceMetric :: Ord PerformanceMetric

instance showPerformanceMetric :: Show PerformanceMetric where
  show PerfFrameTime = "frame-time"
  show PerfMemoryUsage = "memory"
  show PerfBandwidth = "bandwidth"
  show PerfGPUOccupancy = "gpu-occupancy"

-- | All performance metrics.
allPerformanceMetrics :: Array PerformanceMetric
allPerformanceMetrics =
  [ PerfFrameTime, PerfMemoryUsage, PerfBandwidth, PerfGPUOccupancy ]

-- | Optimization objective for fluid simulation.
-- |
-- | This becomes an ILP problem: maximize quality subject to constraints.
type FluidObjective =
  { maximize :: Array QualityMetric
  , minimize :: Array PerformanceMetric
  , constraints :: Array FluidConstraint
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // configuration identity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate deterministic UUID for fluid configuration.
-- |
-- | Same configuration → same UUID → same simulation.
fluidConfigUUID :: String -> UUID5.UUID5
fluidConfigUUID configStr = UUID5.uuid5 nsFluidSolver configStr

-- | Generate deterministic UUID for particle.
particleUUID :: Int -> Number -> Number -> UUID5.UUID5
particleUUID pid x y = 
  UUID5.uuid5 nsFluidParticle (show pid <> ":" <> show x <> ":" <> show y)

-- | Generate deterministic UUID for solver state.
solverUUID :: Int -> Int -> Number -> UUID5.UUID5
solverUUID width height timestep =
  UUID5.uuid5 nsFluidSolver (show width <> "x" <> show height <> "@" <> show timestep)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // effect analysis
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if effect includes capability.
hasEffect :: FluidEffect -> FluidEffect -> Boolean
hasEffect (EffectComposite effs) target = Array.elem target effs
hasEffect eff target = eff == target || eff == EffectComposite [target]

-- | Check if any effect is present.
hasAnyEffect :: FluidEffect -> Boolean
hasAnyEffect EffectNone = false
hasAnyEffect _ = true

-- | Check if expression is pure (no effects).
isPureExpr :: FluidExpr -> Boolean
isPureExpr expr = exprEffect expr == EffectNone

-- | Estimate memory cost of expression in bytes.
estimateMemory :: FluidExpr -> Int
estimateMemory (FluidPure _) = 8
estimateMemory (FluidParticleOp OpEmitParticle) = 64
estimateMemory (FluidParticleOp _) = 0
estimateMemory (FluidSolverOp _) = 0
estimateMemory (FluidSeq e1 e2) = estimateMemory e1 + estimateMemory e2
estimateMemory (FluidPar e1 e2) = estimateMemory e1 + estimateMemory e2
estimateMemory (FluidIf _ t e) = maxInt (estimateMemory t) (estimateMemory e)
estimateMemory (FluidLoop n e) = n * estimateMemory e
estimateMemory (FluidAnnotate _ e) = estimateMemory e



-- | Estimate computational cost (relative units).
estimateCost :: FluidExpr -> Number
estimateCost (FluidPure _) = 1.0
estimateCost (FluidParticleOp OpFindNeighbors) = 100.0
estimateCost (FluidParticleOp OpComputeDensity) = 50.0
estimateCost (FluidParticleOp OpComputeViscosity) = 50.0
estimateCost (FluidParticleOp _) = 10.0
estimateCost (FluidSolverOp OpProject) = 200.0
estimateCost (FluidSolverOp OpDiffuse) = 100.0
estimateCost (FluidSolverOp _) = 50.0
estimateCost (FluidSeq e1 e2) = estimateCost e1 + estimateCost e2
estimateCost (FluidPar e1 e2) = maxNum (estimateCost e1) (estimateCost e2)
estimateCost (FluidIf c t e) = estimateCost c + maxNum (estimateCost t) (estimateCost e)
estimateCost (FluidLoop n e) = intToNum n * estimateCost e
estimateCost (FluidAnnotate _ e) = estimateCost e

-- | Check if effect is stronger than another.
effectStrongerThan :: FluidEffect -> FluidEffect -> Boolean
effectStrongerThan EffectNone _ = false
effectStrongerThan _ EffectNone = true
effectStrongerThan (EffectComposite a) (EffectComposite b) = 
  Array.foldl (\acc e -> acc || Array.elem e b) false a
effectStrongerThan _ _ = false

-- | Check if constraint bound is tight.
isConstraintTight :: FluidConstraint -> Boolean
isConstraintTight (ConstraintParticleCount c m) = c == m
isConstraintTight (ConstraintGridDimension c m) = c == m
isConstraintTight (ConstraintMemory c m) = c == m
isConstraintTight (ConstraintFrameTime c m) = c == m
isConstraintTight (ConstraintAnd a b) = isConstraintTight a || isConstraintTight b
isConstraintTight ConstraintTrue = false
isConstraintTight ConstraintFalse = true

-- | Compute slack in constraint (how much room remains).
constraintSlack :: FluidConstraint -> Number
constraintSlack (ConstraintParticleCount c m) = intToNum (m - c)
constraintSlack (ConstraintGridDimension c m) = intToNum (m - c)
constraintSlack (ConstraintMemory c m) = intToNum (m - c)
constraintSlack (ConstraintFrameTime c m) = m - c
constraintSlack (ConstraintAnd a b) = minNum (constraintSlack a) (constraintSlack b)
constraintSlack ConstraintTrue = 1.0e9
constraintSlack ConstraintFalse = 0.0 - 1.0

-- | Map over quality metrics.
mapQualityMetrics :: (QualityMetric -> QualityMetric) -> Array QualityMetric -> Array QualityMetric
mapQualityMetrics f metrics = map f metrics

-- | Combine objectives.
combineObjectives :: FluidObjective -> FluidObjective -> FluidObjective
combineObjectives a b =
  { maximize: a.maximize <> b.maximize
  , minimize: a.minimize <> b.minimize
  , constraints: a.constraints <> b.constraints
  }

-- | Empty objective.

-- | Helpers
maxNum :: Number -> Number -> Number
maxNum a b = if a > b then a else b

minNum :: Number -> Number -> Number
minNum a b = if a < b then a else b


intToNum :: Int -> Number
intToNum n = intToNumber n
  where
    intToNumber i = case i of
      0 -> 0.0
      _ -> if i > 0 then 1.0 + intToNumber (i - 1) else (0.0 - 1.0) + intToNumber (i + 1)

-- | Maximum of two integers.
maxInt :: Int -> Int -> Int
maxInt a b = if a >= b then a else b

-- | Empty objective.
emptyObjective :: FluidObjective
emptyObjective = { maximize: [], minimize: [], constraints: [] }

-- | Normalize cost by particle count.
normalizeCost :: Number -> Int -> Number
normalizeCost cost particleCount = 
  if particleCount > 0 
    then cost / intToNum particleCount 
    else cost

-- | Empty effect set (monoid identity).
emptyEffects :: FluidEffect
emptyEffects = mempty
