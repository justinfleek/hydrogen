-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // physics // fluid
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Fluid — Complete fluid simulation infrastructure.
-- |
-- | ## Architecture
-- |
-- | The fluid pillar provides scale-invariant simulation:
-- |
-- | - **Core**: Graded effects, co-effects, AST, Presburger constraints, ILP
-- | - **Solver**: Grid-based Eulerian (Navier-Stokes)
-- | - **Particle**: SPH Lagrangian simulation
-- | - **Intent**: Semantic mapping for AI model selection
-- | - **Neighborhood**: Spatial data structures (octree, hash grid, uniform grid)
-- |
-- | ## Scale Invariance
-- |
-- | All types are pure data. The same algorithms work for:
-- | - 1 particle (microscopic drop)
-- | - 1 billion particles (ocean simulation)
-- |
-- | Hyperconsole/WASM handles batching and GPU dispatch.
-- |
-- | ## Graded Monads
-- |
-- | FluidEffect tracks capabilities:
-- | - EffectEmit: Can create particles
-- | - EffectForce: Can apply forces
-- | - EffectTransfer: Can move mass
-- |
-- | ## Co-Effect Algebra
-- |
-- | FluidCoEffect tracks requirements:
-- | - CoEffectNeighbors: Needs spatial lookup
-- | - CoEffectGrid: Needs Eulerian grid
-- | - CoEffectGPU: Benefits from GPU
-- |
-- | ## UUID5 Identity
-- |
-- | Every configuration has deterministic identity:
-- | - Same parameters → same UUID → reproducible results
-- | - Enables caching, diffing, distributed computation
-- |
-- | ## Dependencies
-- | - Hydrogen.Schema.Physics.Fluid.Core
-- | - Hydrogen.Schema.Physics.Fluid.Solver
-- | - Hydrogen.Schema.Physics.Fluid.Particle
-- | - Hydrogen.Schema.Physics.Fluid.Intent
-- | - Hydrogen.Schema.Physics.Fluid.Neighborhood

module Hydrogen.Schema.Physics.Fluid
  ( -- * Re-exports from Core
    module Core
    
  -- * Re-exports from Solver
  , module Solver
  
  -- * Re-exports from Particle
  , module Particle
  
  -- * Re-exports from Intent
  , module Intent
  
  -- * Re-exports from Neighborhood
  , module Neighborhood
  ) where

import Hydrogen.Schema.Physics.Fluid.Core
  ( nsFluidParticle
  , nsFluidSolver
  , nsFluidIntent
  , nsFluidEffect
  , FluidEffect(EffectNone, EffectEmit, EffectForce, EffectTransfer, EffectTopology, EffectRender, EffectComposite)
  , allFluidEffects
  , effectCombine
  , effectNone
  , effectAll
  , FluidCoEffect(CoEffectNone, CoEffectNeighbors, CoEffectGrid, CoEffectGPU, CoEffectMemory, CoEffectBandwidth, CoEffectComposite)
  , allFluidCoEffects
  , coEffectCombine
  , coEffectNone
  , coEffectAll
  , FluidExpr(FluidPure, FluidParticleOp, FluidSolverOp, FluidSeq, FluidPar, FluidIf, FluidLoop, FluidAnnotate)
  , exprEffect
  , exprCoEffect
  , exprUUID
  , ParticleOp(OpEmitParticle, OpRemoveParticle, OpMoveParticle, OpAccelerate, OpComputeDensity, OpComputePressure, OpComputeViscosity, OpFindNeighbors)
  , allParticleOps
  , SolverOp(OpAdvect, OpDiffuse, OpProject, OpApplyGravity, OpEnforceBoundary, OpTransferToGrid, OpTransferToParticles)
  , allSolverOps
  , FluidConstraint(ConstraintParticleCount, ConstraintGridDimension, ConstraintMemory, ConstraintFrameTime, ConstraintAnd, ConstraintTrue, ConstraintFalse)
  , particleCountBound
  , gridDimensionBound
  , memoryCostBound
  , constraintSatisfied
  , FluidObjective
  , QualityMetric(QualityParticleCount, QualityGridResolution, QualitySolverIterations, QualityTimestep)
  , allQualityMetrics
  , PerformanceMetric(PerfFrameTime, PerfMemoryUsage, PerfBandwidth, PerfGPUOccupancy)
  , allPerformanceMetrics
  , fluidConfigUUID
  , particleUUID
  , solverUUID
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
  ) as Core

import Hydrogen.Schema.Physics.Fluid.Solver
  ( Velocity
  , VelocityField
  , mkVelocityField
  , fieldWidth
  , fieldHeight
  , getVelocityAt
  , setVelocityAt
  , clearVelocityField
  , FluidProperties
  , mkFluidProperties
  , viscosity
  , density
  , surfaceTension
  , defaultPaint
  , waterPaint
  , oilPaint
  , honeyPaint
  , ExternalForces
  , mkExternalForces
  , gravityForce
  , noForces
  , SolverConfig
  , mkSolverConfig
  , solverIterations
  , solverTimestep
  , defaultSolverConfig
  , highQualitySolver
  , advect
  , applyForces
  , diffuse
  , project
  , solverStep
  , maxVelocity
  , divergence
  , kineticEnergy
  , displayFluidProperties
  , displaySolverConfig
  , velocitiesEqual
  , velocityExceeds
  , negateVelocity
  , VelocityOrder(Slower, SameSpeed, Faster)
  , compareVelocities
  , totalCells
  ) as Solver

import Hydrogen.Schema.Physics.Fluid.Particle
  ( Particle
  , mkParticle
  , particleId
  , particlePosition
  , particleVelocity
  , particleMass
  , particleDensity
  , particlePressure
  , ParticleSystem
  , mkParticleSystem
  , systemParticles
  , systemSmoothingRadius
  , addParticle
  , removeParticle
  , clearParticles
  , particleCount
  , KernelType(Poly6Kernel, SpikyKernel, ViscosityKernel)
  , allKernelTypes
  , kernelPoly6
  , kernelSpiky
  , kernelViscosity
  , kernelGradientSpiky
  , kernelLaplacianViscosity
  , computeDensity
  , computeAllDensities
  , restDensity
  , computePressure
  , computeAllPressures
  , stiffnessConstant
  , computePressureForce
  , computeViscosityForce
  , computeGravityForce
  , computeTotalForce
  , integrateParticle
  , integrateSystem
  , BoundaryType(ReflectBoundary, ClampBoundary, WrapBoundary)
  , allBoundaryTypes
  , enforceBoundary
  , systemEnergy
  , averageDensity
  , maxSpeed
  , displayParticle
  , displayKernelType
  , getParticleAt
  , updateParticleAt
  , removeParticleAt
  , isParticleInBounds
  , isParticleSlow
  , getParticleAtOrDefault
  ) as Particle

import Hydrogen.Schema.Physics.Fluid.Intent
  ( FluidBehavior(Flowing, Dripping, Pooling, Splashing, Spreading, Mixing, Drying, Toppling)
  , allFluidBehaviors
  , describeBehavior
  , ViscosityClass(Watery, Milky, Syrupy, Oily, Honey, Tar, Solid)
  , allViscosityClasses
  , viscosityToCoefficient
  , describeViscosity
  , ScaleClass(Microscopic, Small, Medium, Large, Massive)
  , allScaleClasses
  , scaleToParticleCount
  , scaleToGridResolution
  , describeScale
  , InteractionType(Passive, Painting, Pouring, Tilting, Touching, Blowing)
  , allInteractionTypes
  , describeInteraction
  , FluidIntent
  , mkFluidIntent
  , intentBehavior
  , intentViscosity
  , intentScale
  , intentInteraction
  , SimulationChoice(UseSPH, UseGridSolver, UseHybrid)
  , chooseSimulation
  , intentToSolverConfig
  , intentToFluidProperties
  , intentToParticleConfig
  , intentWaterDrop
  , intentHoneyDrip
  , intentOilPaint
  , intentWatercolor
  , intentInkSplatter
  , intentLavaFlow
  , intentMilkPour
  , intentBloodDrop
  , behaviorKeywords
  , viscosityKeywords
  , scaleKeywords
  , intentsSimilar
  , isHighPerformance
  , isThickFluid
  , withGravity
  , withSurfaceTension
  , scaleUp
  , scaleDown
  , makeThicker
  , makeThinner
  , displayIntent
  , needsSPH
  , combinedParticleCount
  , allIntentKeywords
  , isThinner
  , isLarger
  , viscosityRatio
  , gravityDifference
  , suggestedInteractions
  , allBehaviorDescriptions
  , allViscosityDescriptions
  ) as Intent

import Hydrogen.Schema.Physics.Fluid.Neighborhood
  ( nsNeighborhood
  , SpatialBounds
  , mkSpatialBounds
  , boundsMinX
  , boundsMaxX
  , boundsMinY
  , boundsMaxY
  , boundsWidth
  , boundsHeight
  , boundsContains
  , expandBounds
  , pointDistance
  , pointDistanceSq
  , boundsDistanceToPoint
  , GridCell
  , mkGridCell
  , cellX
  , cellY
  , cellParticles
  , cellAddParticle
  , UniformGrid
  , mkUniformGrid
  , gridResolutionX
  , gridResolutionY
  , gridCellSize
  , insertParticle
  , queryNeighbors
  , clearGrid
  , rebuildGrid
  , OctreeNode(OctreeLeaf, OctreeBranch)
  , OctreeConfig
  , mkOctreeConfig
  , maxParticlesPerNode
  , maxDepth
  , Octree
  , mkOctree
  , octreeInsert
  , octreeQuery
  , octreeRebuild
  , octreeDepth
  , octreeNodeCount
  , HashGrid
  , mkHashGrid
  , hashGridInsert
  , hashGridQuery
  , hashGridClear
  , spatialHash
  , NeighborIterator
  , mkNeighborIterator
  , iteratorNext
  , iteratorHasMore
  , collectNeighbors
  , SearchMetrics
  , mkSearchMetrics
  , totalQueries
  , totalNeighborsFound
  , averageNeighbors
  , cacheHitRate
  , SearchStrategy(StrategyUniformGrid, StrategyOctree, StrategyHashGrid, StrategyBruteForce)
  , allSearchStrategies
  , chooseStrategy
  , strategyComplexity
  ) as Neighborhood
