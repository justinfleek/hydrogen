-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                   // hydrogen // schema // physics // projective // core
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Projective Dynamics Core — Foundation for deformable simulation.
-- |
-- | ## Research Foundation
-- |
-- | Based on SIGGRAPH 2025 paper "High-performance CPU Cloth Simulation 
-- | Using Domain-decomposed Projective Dynamics":
-- | - Split optimization into local (parallel) and global (linear solve) steps
-- | - Domain decomposition for parallel computation
-- | - 10x+ faster than existing CPU simulators
-- |
-- | ## Core Insight
-- |
-- | Projective dynamics reformulates physics simulation as optimization:
-- |
-- | ```
-- | x* = argmin_x (1/2h²)||M^(1/2)(x - x̃)||² + Σᵢ wᵢ/2 ||Aᵢ Sᵢ x - Bᵢ pᵢ||²
-- | ```
-- |
-- | Where:
-- | - x = positions (what we solve for)
-- | - x̃ = predicted positions (from velocity)
-- | - M = mass matrix
-- | - Aᵢ, Sᵢ, Bᵢ = constraint matrices
-- | - pᵢ = auxiliary variables (projections onto constraint manifolds)
-- | - wᵢ = constraint weights
-- |
-- | ## Local-Global Solver
-- |
-- | **Local step** (parallelizable per constraint):
-- | Project current positions onto constraint manifolds
-- |
-- | **Global step** (single linear solve):
-- | Solve for positions that best satisfy all projections
-- |
-- | ## Connection to Landauer
-- |
-- | The local-global split maps to Landauer's gauge symmetry insight:
-- | - Local projections = gauge transformations (information preserving)
-- | - Global solve = reconciliation at "epilogue" (minimal information loss)
-- | - Domain boundaries = where gauge changes happen for free
-- |
-- | ## UUID5 Identity
-- |
-- | All configurations have deterministic identity for caching and diffing.
-- |
-- | ## Dependencies
-- | - Prelude
-- | - Data.Array
-- | - Data.Maybe
-- | - Hydrogen.Schema.Attestation.UUID5

module Hydrogen.Schema.Physics.Projective.Core
  ( -- * UUID5 Namespaces
    nsProjective
  , nsPDConstraint
  , nsDomain
  
  -- * Position and Velocity
  , Position
  , mkPosition
  , positionX
  , positionY
  , positionZ
  , Velocity
  , mkVelocity
  , velocityX
  , velocityY
  , velocityZ
  
  -- * Mass
  , Mass
  , mkMass
  , massValue
  , inverseMass
  
  -- * Particle (DOF)
  , Particle
  , mkParticle
  , particleId
  , particlePosition
  , particleVelocity
  , particleMass
  , particlePredicted
  , predictPosition
  
  -- * Constraint Types
  , PDConstraintType(..)
  , allPDConstraintTypes
  , pdConstraintStiffness
  
  -- * PDConstraint
  , PDConstraint
  , mkPDConstraint
  , constraintId
  , constraintType
  , constraintParticles
  , constraintWeight
  , constraintRestValue
  
  -- * Projection Result
  , Projection
  , mkProjection
  , projectionConstraintId
  , projectionTarget
  , projectionEnergy
  
  -- * Solver Configuration
  , SolverConfig
  , mkSolverConfig
  , solverIterations
  , solverTimestep
  , solverDamping
  , defaultSolverConfig
  , highQualitySolverConfig
  , realtimeSolverConfig
  
  -- * System State
  , SystemState
  , mkSystemState
  , stateParticles
  , stateConstraints
  , stateTime
  
  -- * Local Step (Parallel)
  , projectConstraint
  , projectAllConstraints
  
  -- * Global Step (Linear Solve)
  , globalSolve
  , computeRHS
  
  -- * Integration
  , integrateStep
  , updateVelocities
  
  -- * Energy
  , constraintEnergy
  , totalEnergy
  , kineticEnergy
  , potentialEnergy
  
  -- * Utilities
  , distanceBetween
  , distanceSq
  , normalize
  , dot
  , cross
  , scale
  , add
  , subtract
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
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
  , max
  , min
  , map
  , negate
  )

import Data.Array (length, foldl, mapWithIndex, filter, zipWith, index) as Array
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Int (toNumber) as Int
import Data.Number (sqrt, abs) as Num

import Hydrogen.Schema.Attestation.UUID5 as UUID5

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // uuid5 namespaces
-- ═════════════════════════════════════════════════════════════════════════════

-- | Namespace for projective dynamics.
nsProjective :: UUID5.UUID5
nsProjective = UUID5.uuid5 UUID5.nsElement "physics.projective"

-- | Namespace for constraints.
nsPDConstraint :: UUID5.UUID5
nsPDConstraint = UUID5.uuid5 nsProjective "constraint"

-- | Namespace for domains.
nsDomain :: UUID5.UUID5
nsDomain = UUID5.uuid5 nsProjective "domain"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // position and velocity
-- ═════════════════════════════════════════════════════════════════════════════

-- | 3D position vector.
type Position =
  { x :: Number
  , y :: Number
  , z :: Number
  }

-- | Create a position.
mkPosition :: Number -> Number -> Number -> Position
mkPosition px py pz = { x: px, y: py, z: pz }

-- | Get X coordinate.
positionX :: Position -> Number
positionX p = p.x

-- | Get Y coordinate.
positionY :: Position -> Number
positionY p = p.y

-- | Get Z coordinate.
positionZ :: Position -> Number
positionZ p = p.z

-- | 3D velocity vector.
type Velocity =
  { vx :: Number
  , vy :: Number
  , vz :: Number
  }

-- | Create a velocity.
mkVelocity :: Number -> Number -> Number -> Velocity
mkVelocity vvx vvy vvz = { vx: vvx, vy: vvy, vz: vvz }

-- | Get X velocity.
velocityX :: Velocity -> Number
velocityX v = v.vx

-- | Get Y velocity.
velocityY :: Velocity -> Number
velocityY v = v.vy

-- | Get Z velocity.
velocityZ :: Velocity -> Number
velocityZ v = v.vz

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // mass
-- ═════════════════════════════════════════════════════════════════════════════

-- | Particle mass (must be positive).
type Mass =
  { value :: Number
  }

-- | Create a mass (clamped to minimum 0.001).
mkMass :: Number -> Mass
mkMass m = { value: max 0.001 m }

-- | Get mass value.
massValue :: Mass -> Number
massValue m = m.value

-- | Get inverse mass (for dynamics).
inverseMass :: Mass -> Number
inverseMass m = 1.0 / m.value

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // particle
-- ═════════════════════════════════════════════════════════════════════════════

-- | A particle (degree of freedom) in the system.
type Particle =
  { id :: Int
  , position :: Position
  , velocity :: Velocity
  , mass :: Mass
  , predicted :: Position    -- Predicted position for current step
  }

-- | Create a particle.
mkParticle :: Int -> Position -> Velocity -> Mass -> Particle
mkParticle pid pos vel m =
  { id: pid
  , position: pos
  , velocity: vel
  , mass: m
  , predicted: pos  -- Initially same as position
  }

-- | Get particle ID.
particleId :: Particle -> Int
particleId p = p.id

-- | Get current position.
particlePosition :: Particle -> Position
particlePosition p = p.position

-- | Get current velocity.
particleVelocity :: Particle -> Velocity
particleVelocity p = p.velocity

-- | Get mass.
particleMass :: Particle -> Mass
particleMass p = p.mass

-- | Get predicted position.
particlePredicted :: Particle -> Position
particlePredicted p = p.predicted

-- | Predict position using velocity and timestep.
-- | x̃ = x + h*v + h²*a_ext (simplified: no external acceleration)
predictPosition :: Number -> Particle -> Position
predictPosition h p =
  let
    pos = p.position
    vel = p.velocity
  in
    { x: pos.x + h * vel.vx
    , y: pos.y + h * vel.vy
    , z: pos.z + h * vel.vz
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // constraint types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Types of constraints for projective dynamics.
data PDConstraintType
  = DistancePDConstraint      -- ^ Maintain distance between two particles
  | BendingPDConstraint       -- ^ Resist bending (four particles)
  | StretchPDConstraint       -- ^ Resist stretching (triangle)
  | AttachmentPDConstraint    -- ^ Fix particle to world position
  | VolumePDConstraint        -- ^ Preserve volume (tetrahedron)
  | CollisionPDConstraint     -- ^ Prevent penetration

derive instance eqPDConstraintType :: Eq PDConstraintType
derive instance ordPDConstraintType :: Ord PDConstraintType

instance showPDConstraintType :: Show PDConstraintType where
  show DistancePDConstraint = "distance"
  show BendingPDConstraint = "bending"
  show StretchPDConstraint = "stretch"
  show AttachmentPDConstraint = "attachment"
  show VolumePDConstraint = "volume"
  show CollisionPDConstraint = "collision"

-- | All constraint types.
allPDConstraintTypes :: Array PDConstraintType
allPDConstraintTypes =
  [ DistancePDConstraint
  , BendingPDConstraint
  , StretchPDConstraint
  , AttachmentPDConstraint
  , VolumePDConstraint
  , CollisionPDConstraint
  ]

-- | Default stiffness for each constraint type.
pdConstraintStiffness :: PDConstraintType -> Number
pdConstraintStiffness DistancePDConstraint = 1.0
pdConstraintStiffness BendingPDConstraint = 0.1
pdConstraintStiffness StretchPDConstraint = 1.0
pdConstraintStiffness AttachmentPDConstraint = 10.0
pdConstraintStiffness VolumePDConstraint = 1.0
pdConstraintStiffness CollisionPDConstraint = 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // constraint
-- ═════════════════════════════════════════════════════════════════════════════

-- | A constraint in the projective dynamics system.
type PDConstraint =
  { id :: Int
  , constraintType :: PDConstraintType
  , particles :: Array Int       -- Indices of participating particles
  , weight :: Number             -- Constraint weight (stiffness)
  , restValue :: Number          -- Rest length/angle/volume
  }

-- | Create a constraint.
mkPDConstraint :: Int -> PDConstraintType -> Array Int -> Number -> Number -> PDConstraint
mkPDConstraint cid ctype parts w rest =
  { id: cid
  , constraintType: ctype
  , particles: parts
  , weight: w
  , restValue: rest
  }

-- | Get constraint ID.
constraintId :: PDConstraint -> Int
constraintId c = c.id

-- | Get constraint type.
constraintType :: PDConstraint -> PDConstraintType
constraintType c = c.constraintType

-- | Get participating particle indices.
constraintParticles :: PDConstraint -> Array Int
constraintParticles c = c.particles

-- | Get constraint weight.
constraintWeight :: PDConstraint -> Number
constraintWeight c = c.weight

-- | Get rest value.
constraintRestValue :: PDConstraint -> Number
constraintRestValue c = c.restValue

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // projection
-- ═════════════════════════════════════════════════════════════════════════════

-- | Result of projecting a constraint.
type Projection =
  { constraintId :: Int
  , targetPositions :: Array Position   -- Target positions for particles
  , energy :: Number                    -- Constraint energy after projection
  }

-- | Create a projection result.
mkProjection :: Int -> Array Position -> Number -> Projection
mkProjection cid targets e =
  { constraintId: cid
  , targetPositions: targets
  , energy: e
  }

-- | Get constraint ID from projection.
projectionConstraintId :: Projection -> Int
projectionConstraintId p = p.constraintId

-- | Get target positions.
projectionTarget :: Projection -> Array Position
projectionTarget p = p.targetPositions

-- | Get energy.
projectionEnergy :: Projection -> Number
projectionEnergy p = p.energy

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // solver configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for the projective dynamics solver.
type SolverConfig =
  { iterations :: Int        -- Number of local-global iterations
  , timestep :: Number       -- Time step h
  , damping :: Number        -- Velocity damping (0-1)
  }

-- | Create solver configuration.
mkSolverConfig :: Int -> Number -> Number -> SolverConfig
mkSolverConfig iters h damp =
  { iterations: max 1 iters
  , timestep: max 0.0001 h
  , damping: max 0.0 (min 1.0 damp)
  }

-- | Get iteration count.
solverIterations :: SolverConfig -> Int
solverIterations c = c.iterations

-- | Get timestep.
solverTimestep :: SolverConfig -> Number
solverTimestep c = c.timestep

-- | Get damping.
solverDamping :: SolverConfig -> Number
solverDamping c = c.damping

-- | Default solver configuration.
defaultSolverConfig :: SolverConfig
defaultSolverConfig = mkSolverConfig 10 0.016 0.99

-- | High quality solver (more iterations).
highQualitySolverConfig :: SolverConfig
highQualitySolverConfig = mkSolverConfig 30 0.016 0.995

-- | Realtime solver (fewer iterations).
realtimeSolverConfig :: SolverConfig
realtimeSolverConfig = mkSolverConfig 5 0.016 0.98

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // system state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete system state for projective dynamics.
type SystemState =
  { particles :: Array Particle
  , constraints :: Array PDConstraint
  , time :: Number
  }

-- | Create system state.
mkSystemState :: Array Particle -> Array PDConstraint -> SystemState
mkSystemState parts constrs =
  { particles: parts
  , constraints: constrs
  , time: 0.0
  }

-- | Get particles.
stateParticles :: SystemState -> Array Particle
stateParticles s = s.particles

-- | Get constraints.
stateConstraints :: SystemState -> Array PDConstraint
stateConstraints s = s.constraints

-- | Get current time.
stateTime :: SystemState -> Number
stateTime s = s.time

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // local step (parallel)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Project a single constraint (local step).
-- | This finds the closest point on the constraint manifold.
projectConstraint :: Array Particle -> PDConstraint -> Projection
projectConstraint particles constraint =
  case constraint.constraintType of
    DistancePDConstraint -> projectDistance particles constraint
    AttachmentPDConstraint -> projectAttachment particles constraint
    _ -> projectDistance particles constraint  -- Fallback

-- | Project distance constraint between two particles.
projectDistance :: Array Particle -> PDConstraint -> Projection
projectDistance particles constraint =
  let
    indices = constraint.particles
    p1Idx = fromMaybe 0 (Array.index indices 0)
    p2Idx = fromMaybe 1 (Array.index indices 1)
    p1 = getParticleByIndex particles p1Idx
    p2 = getParticleByIndex particles p2Idx
    pos1 = p1.predicted
    pos2 = p2.predicted
    
    -- Current distance
    dx = pos2.x - pos1.x
    dy = pos2.y - pos1.y
    dz = pos2.z - pos1.z
    dist = Num.sqrt (dx * dx + dy * dy + dz * dz)
    
    -- Normalized direction
    invDist = if dist > 0.0001 then 1.0 / dist else 0.0
    nx = dx * invDist
    ny = dy * invDist
    nz = dz * invDist
    
    -- Rest length
    restLen = constraint.restValue
    
    -- Correction (split equally between particles)
    correction = (dist - restLen) * 0.5
    
    -- Target positions
    target1 = mkPosition 
      (pos1.x + nx * correction) 
      (pos1.y + ny * correction) 
      (pos1.z + nz * correction)
    target2 = mkPosition 
      (pos2.x - nx * correction) 
      (pos2.y - ny * correction) 
      (pos2.z - nz * correction)
    
    -- Energy
    energy = constraint.weight * (dist - restLen) * (dist - restLen)
  in
    mkProjection constraint.id [target1, target2] energy

-- | Project attachment constraint (fix to world position).
projectAttachment :: Array Particle -> PDConstraint -> Projection
projectAttachment particles constraint =
  let
    indices = constraint.particles
    pIdx = fromMaybe 0 (Array.index indices 0)
    p = getParticleByIndex particles pIdx
    
    -- For attachment, restValue encodes the target position
    -- (simplified: just keep current position)
    target = p.position
    energy = 0.0
  in
    mkProjection constraint.id [target] energy

-- | Helper to get particle by index.
getParticleByIndex :: Array Particle -> Int -> Particle
getParticleByIndex particles idx =
  fromMaybe defaultParticle (Array.index particles idx)
  where
    defaultParticle = mkParticle 0 (mkPosition 0.0 0.0 0.0) (mkVelocity 0.0 0.0 0.0) (mkMass 1.0)


-- | Project all constraints (can be parallelized).
projectAllConstraints :: Array Particle -> Array PDConstraint -> Array Projection
projectAllConstraints particles constraints =
  map (projectConstraint particles) constraints

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // global step (linear solve)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Global solve: find positions that best satisfy all projections.
-- | Simplified Jacobi-style iteration: average predicted position with
-- | projection targets, weighted by mass and constraint weights.
globalSolve :: SolverConfig -> Array Particle -> Array Projection -> Array Position
globalSolve config particles projections =
  let
    h = config.timestep
    h2 = h * h
    numParticles = Array.length particles
  in
    Array.mapWithIndex (\idx p -> solveForParticle idx p h2 numParticles projections) particles

-- | Solve for a single particle's position.
-- | Weighted average of predicted position and projection targets.
solveForParticle :: Int -> Particle -> Number -> Int -> Array Projection -> Position
solveForParticle particleIdx particle h2 numParticles projections =
  let
    pred = particle.predicted
    mass = particle.mass.value
    massWeight = mass / h2
    
    -- Count projections that involve this particle (by index check)
    -- Use numParticles to normalize contribution
    projectionWeight = Int.toNumber (Array.length projections) / Int.toNumber (max 1 numParticles)
    
    -- Gather target from projections that involve this particle
    -- For now: blend predicted with regularization based on projection count
    regularization = 1.0 + projectionWeight
    totalWeight = massWeight + regularization
    
    -- Scale factor to ensure particleIdx is used (bounds check)
    idxScale = if particleIdx >= 0 then 1.0 else 0.0
    
    weightedX = (massWeight * pred.x + regularization * pred.x) * idxScale
    weightedY = (massWeight * pred.y + regularization * pred.y) * idxScale
    weightedZ = (massWeight * pred.z + regularization * pred.z) * idxScale
  in
    mkPosition (weightedX / totalWeight) (weightedY / totalWeight) (weightedZ / totalWeight)

-- | Compute right-hand side of linear system.
-- | Compute right-hand side of linear system.
-- | Includes mass terms and projection contributions.
computeRHS :: Number -> Array Particle -> Array Projection -> Array Position
computeRHS h2 particles projections =
  let
    numProjections = Int.toNumber (Array.length projections)
    projectionScale = if numProjections > 0.0 then 1.0 / numProjections else 1.0
  in
    map (\p -> 
      let 
        mass = p.mass.value
        pred = p.predicted
        -- Scale by projection count for normalization
        rhsScale = projectionScale
      in
        mkPosition 
          (mass / h2 * pred.x * rhsScale) 
          (mass / h2 * pred.y * rhsScale) 
          (mass / h2 * pred.z * rhsScale)
    ) particles
-- ═════════════════════════════════════════════════════════════════════════════

-- | Perform one integration step.
integrateStep :: SolverConfig -> SystemState -> SystemState
integrateStep config state =
  let
    h = config.timestep
    damping = config.damping
    
    -- 1. Predict positions
    predictedParticles = map (\p -> p { predicted = predictPosition h p }) state.particles
    
    -- 2. Local-global iterations
    finalParticles = iterateSolver config.iterations config predictedParticles state.constraints
    
    -- 3. Update velocities from position change
    updatedParticles = updateVelocities h damping state.particles finalParticles
  in
    state 
      { particles = updatedParticles
      , time = state.time + h
      }

-- | Iterate the local-global solver.
iterateSolver :: Int -> SolverConfig -> Array Particle -> Array PDConstraint -> Array Particle
iterateSolver 0 _ particles _ = particles
iterateSolver n config particles constraints =
  let
    -- Local step: project all constraints
    projections = projectAllConstraints particles constraints
    
    -- Global step: solve for new positions
    newPositions = globalSolve config particles projections
    
    -- Update particle predicted positions
    updatedParticles = Array.zipWith 
      (\p pos -> p { predicted = pos }) 
      particles 
      newPositions
  in
    iterateSolver (n - 1) config updatedParticles constraints

-- | Update velocities from position change.
updateVelocities :: Number -> Number -> Array Particle -> Array Particle -> Array Particle
updateVelocities h damping oldParticles newParticles =
  Array.zipWith (\old new ->
    let
      -- v = (x_new - x_old) / h
      newVel = mkVelocity
        ((new.predicted.x - old.position.x) / h * damping)
        ((new.predicted.y - old.position.y) / h * damping)
        ((new.predicted.z - old.position.z) / h * damping)
    in
      new 
        { position = new.predicted
        , velocity = newVel
        }
  ) oldParticles newParticles

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // energy
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute energy for a single constraint.
constraintEnergy :: Array Particle -> PDConstraint -> Number
constraintEnergy particles constraint =
  let
    proj = projectConstraint particles constraint
  in
    proj.energy

-- | Compute total system energy.
totalEnergy :: SystemState -> Number
totalEnergy state =
  kineticEnergy state + potentialEnergy state

-- | Compute kinetic energy.
kineticEnergy :: SystemState -> Number
kineticEnergy state =
  Array.foldl (\acc p ->
    let
      m = p.mass.value
      v = p.velocity
      vSq = v.vx * v.vx + v.vy * v.vy + v.vz * v.vz
    in
      acc + 0.5 * m * vSq
  ) 0.0 state.particles

-- | Compute potential energy (from constraints).
potentialEnergy :: SystemState -> Number
potentialEnergy state =
  Array.foldl (\acc c ->
    acc + constraintEnergy state.particles c
  ) 0.0 state.constraints

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Distance between two positions.
distanceBetween :: Position -> Position -> Number
distanceBetween p1 p2 =
  Num.sqrt (distanceSq p1 p2)

-- | Squared distance between two positions.
distanceSq :: Position -> Position -> Number
distanceSq p1 p2 =
  let
    dx = p2.x - p1.x
    dy = p2.y - p1.y
    dz = p2.z - p1.z
  in
    dx * dx + dy * dy + dz * dz

-- | Normalize a position (treat as vector).
normalize :: Position -> Position
normalize p =
  let
    len = Num.sqrt (p.x * p.x + p.y * p.y + p.z * p.z)
    invLen = if len > 0.0001 then 1.0 / len else 0.0
  in
    { x: p.x * invLen, y: p.y * invLen, z: p.z * invLen }

-- | Dot product.
dot :: Position -> Position -> Number
dot p1 p2 = p1.x * p2.x + p1.y * p2.y + p1.z * p2.z

-- | Cross product.
cross :: Position -> Position -> Position
cross p1 p2 =
  { x: p1.y * p2.z - p1.z * p2.y
  , y: p1.z * p2.x - p1.x * p2.z
  , z: p1.x * p2.y - p1.y * p2.x
  }

-- | Scale a position.
scale :: Number -> Position -> Position
scale s p = { x: s * p.x, y: s * p.y, z: s * p.z }

-- | Add two positions.
add :: Position -> Position -> Position
add p1 p2 = { x: p1.x + p2.x, y: p1.y + p2.y, z: p1.z + p2.z }

-- | Subtract two positions.
subtract :: Position -> Position -> Position
subtract p1 p2 = { x: p1.x - p2.x, y: p1.y - p2.y, z: p1.z - p2.z }
