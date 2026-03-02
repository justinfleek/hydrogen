-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // physics // fluid // particle
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Fluid Particle — SPH (Smoothed Particle Hydrodynamics) simulation.
-- |
-- | ## Design Philosophy
-- |
-- | Based on the SIGGRAPH Asia 2022 paper "Neighborhood Search for SPH"
-- | and classic SPH fluid dynamics. Particles carry mass, position,
-- | velocity, and material properties.
-- |
-- | ## SPH Fundamentals
-- |
-- | Each particle represents a sample of the fluid. Properties are
-- | smoothed using kernel functions:
-- |
-- |   A(r) = Σ_j m_j * (A_j / ρ_j) * W(r - r_j, h)
-- |
-- | Where:
-- | - m_j = particle mass
-- | - ρ_j = particle density
-- | - W = smoothing kernel
-- | - h = smoothing radius
-- |
-- | ## Kernel Functions
-- |
-- | - **Poly6**: General interpolation
-- | - **Spiky**: Pressure forces (avoids particle clumping)
-- | - **Viscosity**: Viscous forces
-- |
-- | ## Dependencies
-- | - Prelude
-- | - Data.Array
-- | - Data.Maybe

module Hydrogen.Schema.Physics.Fluid.Particle
  ( -- * Particle
    Particle
  , mkParticle
  , particleId
  , particlePosition
  , particleVelocity
  , particleMass
  , particleDensity
  , particlePressure
  
  -- * Particle System
  , ParticleSystem
  , mkParticleSystem
  , systemParticles
  , systemSmoothingRadius
  , addParticle
  , removeParticle
  , clearParticles
  , particleCount
  
  -- * SPH Kernels
  , KernelType(Poly6Kernel, SpikyKernel, ViscosityKernel)
  , allKernelTypes
  , kernelPoly6
  , kernelSpiky
  , kernelViscosity
  , kernelGradientSpiky
  , kernelLaplacianViscosity
  
  -- * Density Computation
  , computeDensity
  , computeAllDensities
  , restDensity
  
  -- * Pressure Computation
  , computePressure
  , computeAllPressures
  , stiffnessConstant
  
  -- * Force Computation
  , computePressureForce
  , computeViscosityForce
  , computeGravityForce
  , computeTotalForce
  
  -- * Integration
  , integrateParticle
  , integrateSystem
  
  -- * Boundary Handling
  , BoundaryType(ReflectBoundary, ClampBoundary, WrapBoundary)
  , allBoundaryTypes
  , enforceBoundary
  
  -- * Analysis
  , systemEnergy
  , averageDensity
  , maxSpeed
  
  -- * Display
  , displayParticle
  , displayKernelType
  
  -- * Particle Utilities
  , getParticleAt
  , updateParticleAt
  , removeParticleAt
  , isParticleInBounds
  , isParticleSlow
  , getParticleAtOrDefault
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
  , (/=)
  , (&&)
  , (>=)
  , (||)
  , (<=)
  , (<)
  , (>)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  , negate
  , max
  , min
  , map
  )

import Data.Array (length, index, updateAt, filter, foldl, snoc, deleteAt) as Array
import Data.Maybe (Maybe(Nothing, Just), fromMaybe)
import Data.Number (sqrt, pi, pow) as Num
import Data.Int (toNumber) as Int

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // particle
-- ═════════════════════════════════════════════════════════════════════════════

-- | A single SPH particle.
type Particle =
  { id :: Int                -- ^ Unique identifier
  , x :: Number              -- ^ X position
  , y :: Number              -- ^ Y position
  , vx :: Number             -- ^ X velocity
  , vy :: Number             -- ^ Y velocity
  , mass :: Number           -- ^ Particle mass
  , density :: Number        -- ^ Computed density
  , pressure :: Number       -- ^ Computed pressure
  , viscosity :: Number      -- ^ Particle viscosity coefficient
  }

-- | Create a new particle.
mkParticle :: Int -> Number -> Number -> Number -> Particle
mkParticle pid px py mass =
  { id: pid
  , x: px
  , y: py
  , vx: 0.0
  , vy: 0.0
  , mass: max 0.001 mass
  , density: 1000.0          -- Default water density
  , pressure: 0.0
  , viscosity: 0.1           -- Default viscosity
  }

-- | Get particle ID.
particleId :: Particle -> Int
particleId p = p.id

-- | Get particle position.
particlePosition :: Particle -> { x :: Number, y :: Number }
particlePosition p = { x: p.x, y: p.y }

-- | Get particle velocity.
particleVelocity :: Particle -> { vx :: Number, vy :: Number }
particleVelocity p = { vx: p.vx, vy: p.vy }

-- | Get particle mass.
particleMass :: Particle -> Number
particleMass p = p.mass

-- | Get particle density.
particleDensity :: Particle -> Number
particleDensity p = p.density

-- | Get particle pressure.
particlePressure :: Particle -> Number
particlePressure p = p.pressure

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // particle system
-- ═════════════════════════════════════════════════════════════════════════════

-- | Collection of particles with simulation parameters.
type ParticleSystem =
  { particles :: Array Particle
  , smoothingRadius :: Number    -- ^ SPH kernel radius (h)
  , restDensity :: Number        -- ^ Target fluid density
  , stiffness :: Number          -- ^ Pressure stiffness (k)
  , viscosityCoeff :: Number     -- ^ Global viscosity
  , gravity :: { x :: Number, y :: Number }
  , nextId :: Int                -- ^ Next particle ID
  }

-- | Create an empty particle system.
mkParticleSystem :: Number -> Number -> ParticleSystem
mkParticleSystem smoothingR restDens =
  { particles: []
  , smoothingRadius: max 0.01 smoothingR
  , restDensity: max 1.0 restDens
  , stiffness: 1000.0
  , viscosityCoeff: 0.1
  , gravity: { x: 0.0, y: 9.81 }
  , nextId: 0
  }

-- | Get all particles.
systemParticles :: ParticleSystem -> Array Particle
systemParticles sys = sys.particles

-- | Get smoothing radius.
systemSmoothingRadius :: ParticleSystem -> Number
systemSmoothingRadius sys = sys.smoothingRadius

-- | Add a particle to the system.
addParticle :: ParticleSystem -> Number -> Number -> Number -> ParticleSystem
addParticle sys px py mass =
  let
    newParticle = mkParticle sys.nextId px py mass
  in
    sys 
      { particles = Array.snoc sys.particles newParticle
      , nextId = sys.nextId + 1
      }

-- | Remove a particle by ID.
removeParticle :: ParticleSystem -> Int -> ParticleSystem
removeParticle sys pid =
  sys { particles = Array.filter (\p -> p.id /= pid) sys.particles }

-- | Clear all particles.
clearParticles :: ParticleSystem -> ParticleSystem
clearParticles sys = sys { particles = [], nextId = 0 }

-- | Get particle count.
particleCount :: ParticleSystem -> Int
particleCount sys = Array.length sys.particles

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // sph kernels
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of SPH smoothing kernel.
data KernelType
  = Poly6Kernel       -- ^ General interpolation
  | SpikyKernel       -- ^ Pressure forces
  | ViscosityKernel   -- ^ Viscosity forces

derive instance eqKernelType :: Eq KernelType
derive instance ordKernelType :: Ord KernelType

instance showKernelType :: Show KernelType where
  show Poly6Kernel = "poly6"
  show SpikyKernel = "spiky"
  show ViscosityKernel = "viscosity"

-- | All kernel types.
allKernelTypes :: Array KernelType
allKernelTypes = [Poly6Kernel, SpikyKernel, ViscosityKernel]

-- | Poly6 kernel for density computation.
-- |
-- | W_poly6(r, h) = 315 / (64 * pi * h^9) * (h^2 - r^2)^3
kernelPoly6 :: Number -> Number -> Number
kernelPoly6 r h =
  if r >= h then 0.0
  else
    let
      h2 = h * h
      r2 = r * r
      diff = h2 - r2
      coeff = 315.0 / (64.0 * Num.pi * Num.pow h 9.0)
    in
      coeff * diff * diff * diff

-- | Spiky kernel for pressure forces.
-- |
-- | W_spiky(r, h) = 15 / (pi * h^6) * (h - r)^3
kernelSpiky :: Number -> Number -> Number
kernelSpiky r h =
  if r >= h then 0.0
  else
    let
      diff = h - r
      coeff = 15.0 / (Num.pi * Num.pow h 6.0)
    in
      coeff * diff * diff * diff

-- | Viscosity kernel.
-- |
-- | W_viscosity(r, h) = 15 / (2 * pi * h^3) * (-r^3/(2h^3) + r^2/h^2 + h/(2r) - 1)
kernelViscosity :: Number -> Number -> Number
kernelViscosity r h =
  if r >= h || r < 0.0001 then 0.0
  else
    let
      coeff = 15.0 / (2.0 * Num.pi * Num.pow h 3.0)
      h3 = h * h * h
      r3 = r * r * r
      r2 = r * r
      h2 = h * h
      term1 = negate r3 / (2.0 * h3)
      term2 = r2 / h2
      term3 = h / (2.0 * r)
    in
      coeff * (term1 + term2 + term3 - 1.0)

-- | Gradient of spiky kernel (for pressure force).
-- |
-- | ∇W_spiky = -45 / (pi * h^6) * (h - r)^2 * (r_vec / r)
kernelGradientSpiky :: Number -> Number -> Number
kernelGradientSpiky r h =
  if r >= h || r < 0.0001 then 0.0
  else
    let
      diff = h - r
      coeff = negate 45.0 / (Num.pi * Num.pow h 6.0)
    in
      coeff * diff * diff

-- | Laplacian of viscosity kernel.
-- |
-- | ∇²W_viscosity = 45 / (pi * h^6) * (h - r)
kernelLaplacianViscosity :: Number -> Number -> Number
kernelLaplacianViscosity r h =
  if r >= h then 0.0
  else
    let
      coeff = 45.0 / (Num.pi * Num.pow h 6.0)
    in
      coeff * (h - r)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // density computation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default rest density (water).
restDensity :: Number
restDensity = 1000.0

-- | Compute density for a single particle.
computeDensity :: ParticleSystem -> Particle -> Number
computeDensity sys p =
  let
    h = sys.smoothingRadius
    
    contribution neighbor =
      let
        dx = p.x - neighbor.x
        dy = p.y - neighbor.y
        r = Num.sqrt (dx * dx + dy * dy)
      in
        neighbor.mass * kernelPoly6 r h
  in
    Array.foldl (\acc neighbor -> acc + contribution neighbor) 0.0 sys.particles

-- | Compute densities for all particles.
computeAllDensities :: ParticleSystem -> ParticleSystem
computeAllDensities sys =
  let
    updateDensity p = p { density = computeDensity sys p }
    newParticles = map updateDensity sys.particles
  in
    sys { particles = newParticles }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // pressure computation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default stiffness constant.
stiffnessConstant :: Number
stiffnessConstant = 1000.0

-- | Compute pressure from density.
-- |
-- | Using Tait equation: p = k * ((ρ/ρ0)^γ - 1)
-- | Simplified: p = k * (ρ - ρ0)
computePressure :: Number -> Number -> Number -> Number
computePressure density0 stiffness currentDensity =
  max 0.0 (stiffness * (currentDensity - density0))

-- | Compute pressures for all particles.
computeAllPressures :: ParticleSystem -> ParticleSystem
computeAllPressures sys =
  let
    updatePressure p = 
      p { pressure = computePressure sys.restDensity sys.stiffness p.density }
    newParticles = map updatePressure sys.particles
  in
    sys { particles = newParticles }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // force computation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute pressure force on a particle.
computePressureForce :: ParticleSystem -> Particle -> { fx :: Number, fy :: Number }
computePressureForce sys p =
  let
    h = sys.smoothingRadius
    
    contribution neighbor =
      if neighbor.id == p.id then { fx: 0.0, fy: 0.0 }
      else
        let
          dx = p.x - neighbor.x
          dy = p.y - neighbor.y
          r = Num.sqrt (dx * dx + dy * dy)
          gradW = kernelGradientSpiky r h
          -- Symmetric pressure: (p_i + p_j) / 2
          avgPressure = (p.pressure + neighbor.pressure) / 2.0
          scale = negate neighbor.mass * avgPressure / neighbor.density * gradW
          -- Direction from neighbor to particle
          dirX = if r > 0.0001 then dx / r else 0.0
          dirY = if r > 0.0001 then dy / r else 0.0
        in
          { fx: scale * dirX, fy: scale * dirY }
    
    sumForces acc neighbor =
      let f = contribution neighbor
      in { fx: acc.fx + f.fx, fy: acc.fy + f.fy }
  in
    Array.foldl sumForces { fx: 0.0, fy: 0.0 } sys.particles

-- | Compute viscosity force on a particle.
computeViscosityForce :: ParticleSystem -> Particle -> { fx :: Number, fy :: Number }
computeViscosityForce sys p =
  let
    h = sys.smoothingRadius
    mu = sys.viscosityCoeff
    
    contribution neighbor =
      if neighbor.id == p.id then { fx: 0.0, fy: 0.0 }
      else
        let
          dx = p.x - neighbor.x
          dy = p.y - neighbor.y
          r = Num.sqrt (dx * dx + dy * dy)
          lapW = kernelLaplacianViscosity r h
          -- Velocity difference
          dvx = neighbor.vx - p.vx
          dvy = neighbor.vy - p.vy
          scale = mu * neighbor.mass / neighbor.density * lapW
        in
          { fx: scale * dvx, fy: scale * dvy }
    
    sumForces acc neighbor =
      let f = contribution neighbor
      in { fx: acc.fx + f.fx, fy: acc.fy + f.fy }
  in
    Array.foldl sumForces { fx: 0.0, fy: 0.0 } sys.particles

-- | Compute gravity force on a particle.
computeGravityForce :: ParticleSystem -> Particle -> { fx :: Number, fy :: Number }
computeGravityForce sys p =
  { fx: p.mass * sys.gravity.x
  , fy: p.mass * sys.gravity.y
  }

-- | Compute total force on a particle.
computeTotalForce :: ParticleSystem -> Particle -> { fx :: Number, fy :: Number }
computeTotalForce sys p =
  let
    fPressure = computePressureForce sys p
    fViscosity = computeViscosityForce sys p
    fGravity = computeGravityForce sys p
  in
    { fx: fPressure.fx + fViscosity.fx + fGravity.fx
    , fy: fPressure.fy + fViscosity.fy + fGravity.fy
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // integration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Integrate a single particle (symplectic Euler).
integrateParticle :: ParticleSystem -> Particle -> Number -> Particle
integrateParticle sys p dt =
  let
    force = computeTotalForce sys p
    -- Acceleration = force / mass
    ax = force.fx / p.mass
    ay = force.fy / p.mass
    -- Update velocity
    newVx = p.vx + ax * dt
    newVy = p.vy + ay * dt
    -- Update position
    newX = p.x + newVx * dt
    newY = p.y + newVy * dt
  in
    p { x = newX, y = newY, vx = newVx, vy = newVy }

-- | Integrate entire system for one timestep.
integrateSystem :: ParticleSystem -> Number -> ParticleSystem
integrateSystem sys dt =
  let
    -- First compute densities and pressures
    withDensities = computeAllDensities sys
    withPressures = computeAllPressures withDensities
    -- Then integrate each particle
    newParticles = map (\p -> integrateParticle withPressures p dt) withPressures.particles
  in
    withPressures { particles = newParticles }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // boundary handling
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of boundary condition.
data BoundaryType
  = ReflectBoundary     -- ^ Bounce off walls
  | ClampBoundary       -- ^ Stop at walls
  | WrapBoundary        -- ^ Periodic boundaries

derive instance eqBoundaryType :: Eq BoundaryType
derive instance ordBoundaryType :: Ord BoundaryType

instance showBoundaryType :: Show BoundaryType where
  show ReflectBoundary = "reflect"
  show ClampBoundary = "clamp"
  show WrapBoundary = "wrap"

-- | All boundary types.
allBoundaryTypes :: Array BoundaryType
allBoundaryTypes = [ReflectBoundary, ClampBoundary, WrapBoundary]

-- | Enforce boundary conditions on a particle.
enforceBoundary 
  :: BoundaryType 
  -> Number          -- ^ Min X
  -> Number          -- ^ Max X
  -> Number          -- ^ Min Y
  -> Number          -- ^ Max Y
  -> Number          -- ^ Damping (0-1)
  -> Particle 
  -> Particle
enforceBoundary btype minX maxX minY maxY damping p =
  case btype of
    ReflectBoundary ->
      let
        -- Reflect X
        p1 = if p.x < minX 
          then p { x = minX, vx = negate p.vx * damping }
          else if p.x > maxX
            then p { x = maxX, vx = negate p.vx * damping }
            else p
        -- Reflect Y
        p2 = if p1.y < minY
          then p1 { y = minY, vy = negate p1.vy * damping }
          else if p1.y > maxY
            then p1 { y = maxY, vy = negate p1.vy * damping }
            else p1
      in
        p2
    
    ClampBoundary ->
      p { x = max minX (min maxX p.x)
        , y = max minY (min maxY p.y)
        , vx = if p.x < minX || p.x > maxX then 0.0 else p.vx
        , vy = if p.y < minY || p.y > maxY then 0.0 else p.vy
        }
    
    WrapBoundary ->
      let
        width = maxX - minX
        height = maxY - minY
        wrapX x = if x < minX then x + width else if x > maxX then x - width else x
        wrapY y = if y < minY then y + height else if y > maxY then y - height else y
      in
        p { x = wrapX p.x, y = wrapY p.y }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // analysis
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute total kinetic energy of the system.
systemEnergy :: ParticleSystem -> Number
systemEnergy sys =
  Array.foldl 
    (\acc p -> 
      let speed2 = p.vx * p.vx + p.vy * p.vy
      in acc + 0.5 * p.mass * speed2
    ) 
    0.0 
    sys.particles

-- | Compute average density across all particles.
averageDensity :: ParticleSystem -> Number
averageDensity sys =
  let
    total = Array.foldl (\acc p -> acc + p.density) 0.0 sys.particles
    count = Int.toNumber (Array.length sys.particles)
  in
    if count > 0.0 then total / count else 0.0

-- | Get maximum particle speed.
maxSpeed :: ParticleSystem -> Number
maxSpeed sys =
  Array.foldl
    (\maxV p -> 
      let speed = Num.sqrt (p.vx * p.vx + p.vy * p.vy)
      in max maxV speed
    )
    0.0
    sys.particles

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // display
-- ═════════════════════════════════════════════════════════════════════════════

-- | Display particle info.
displayParticle :: Particle -> String
displayParticle p =
  "Particle " <> show p.id <> " at (" <> show p.x <> ", " <> show p.y <> ")"

-- | Display kernel type.
displayKernelType :: KernelType -> String
displayKernelType k = show k <> " kernel"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // particle utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get particle by index.
getParticleAt :: ParticleSystem -> Int -> Maybe Particle
getParticleAt sys idx = Array.index sys.particles idx

-- | Update particle at index.
updateParticleAt :: ParticleSystem -> Int -> Particle -> ParticleSystem
updateParticleAt sys idx p =
  case Array.updateAt idx p sys.particles of
    Just newParticles -> sys { particles = newParticles }
    Nothing -> sys

-- | Remove particle at index.
removeParticleAt :: ParticleSystem -> Int -> ParticleSystem
removeParticleAt sys idx =
  case Array.deleteAt idx sys.particles of
    Just newParticles -> sys { particles = newParticles }
    Nothing -> sys

-- | Check if particle is within bounds.
isParticleInBounds :: Particle -> Number -> Number -> Number -> Number -> Boolean
isParticleInBounds p minX maxX minY maxY =
  p.x >= minX && p.x <= maxX && p.y >= minY && p.y <= maxY

-- | Check if particle speed is below threshold.
isParticleSlow :: Particle -> Number -> Boolean
isParticleSlow p threshold =
  let speed = Num.sqrt (p.vx * p.vx + p.vy * p.vy)
  in speed <= threshold

-- | Get particle by index with default.
getParticleAtOrDefault :: ParticleSystem -> Int -> Particle -> Particle
getParticleAtOrDefault sys idx defaultP = 
  fromMaybe defaultP (Array.index sys.particles idx)
