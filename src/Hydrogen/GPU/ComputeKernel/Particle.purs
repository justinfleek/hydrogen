-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // gpu // compute-kernel/particle
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ComputeKernel/Particle — GPU Particle System Kernel Types
-- |
-- | Particle simulation for visual effects:
-- | - Physics: Position, velocity, forces, collisions
-- | - Emit: Particle spawning with variance
-- | - Sort: Depth ordering for correct alpha blending

module Hydrogen.GPU.ComputeKernel.Particle
  ( -- * Particle Types
    ParticleKernel(..)
  , ParticleBounds(..)
  , ParticleForce
  , SortAxis(..)
  
  -- * Specific Kernels
  , ParticlePhysicsKernel(..)
  , ParticleEmitKernel(..)
  , ParticleSortKernel(..)
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Hydrogen.GPU.ComputeKernel.Core
  ( KernelConfig
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // particle kernels
-- ═════════════════════════════════════════════════════════════════════════════

-- | Particle kernel variants
-- |
-- | Each variant maps to a WebGPU compute shader with workgroup 256x1x1
-- | (1D particle array processing).
data ParticleKernel
  = ParticlePhysics ParticlePhysicsKernel
  | ParticleEmit ParticleEmitKernel
  | ParticleSort ParticleSortKernel

derive instance eqParticleKernel :: Eq ParticleKernel

instance showParticleKernel :: Show ParticleKernel where
  show (ParticlePhysics k) = "(ParticlePhysics " <> show k <> ")"
  show (ParticleEmit k) = "(ParticleEmit " <> show k <> ")"
  show (ParticleSort k) = "(ParticleSort " <> show k <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // physics
-- ═════════════════════════════════════════════════════════════════════════════

-- | Particle physics simulation kernel
-- |
-- | Updates particle positions, velocities, and lifetimes.
-- | GPU-parallel: each thread handles one particle.
newtype ParticlePhysicsKernel = ParticlePhysicsKernel
  { particleCount :: Int       -- Number of particles
  , deltaTime :: Number        -- Time step in seconds
  , gravity :: Number          -- Gravity strength
  , damping :: Number          -- Velocity damping
  , bounds :: ParticleBounds   -- Boundary behavior
  , forces :: Array ParticleForce  -- External forces
  , config :: KernelConfig
  }

derive instance eqParticlePhysicsKernel :: Eq ParticlePhysicsKernel

instance showParticlePhysicsKernel :: Show ParticlePhysicsKernel where
  show (ParticlePhysicsKernel k) = "(ParticlePhysicsKernel count:" <> show k.particleCount <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Particle boundary behavior
-- |
-- | Defines what happens when particles reach simulation boundaries.
data ParticleBounds
  = BoundsNone               -- No boundaries (particles can escape)
  | BoundsWrap               -- Wrap around edges (toroidal)
  | BoundsBounce             -- Bounce off edges (elastic)
  | BoundsKill               -- Kill particles at edges

derive instance eqParticleBounds :: Eq ParticleBounds

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // forces
-- ═════════════════════════════════════════════════════════════════════════════

-- | External force on particles
-- |
-- | Defines a force vector with position-dependent falloff.
type ParticleForce =
  { x :: Number                -- Force X component
  , y :: Number                -- Force Y component
  , z :: Number                -- Force Z component
  , strength :: Number         -- Force magnitude
  , falloff :: Number          -- Distance falloff
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // emit
-- ═════════════════════════════════════════════════════════════════════════════

-- | Particle emission kernel
-- |
-- | Spawns new particles with controlled randomness.
newtype ParticleEmitKernel = ParticleEmitKernel
  { emitCount :: Int           -- Particles to emit this frame
  , positionX :: Number        -- Emitter X (0.0-1.0)
  , positionY :: Number        -- Emitter Y (0.0-1.0)
  , spread :: Number           -- Emission cone spread (radians)
  , velocity :: Number         -- Initial velocity
  , velocityVariance :: Number -- Velocity randomness
  , lifetime :: Number         -- Particle lifetime (seconds)
  , lifetimeVariance :: Number -- Lifetime randomness
  , seed :: Int                -- Random seed
  , config :: KernelConfig
  }

derive instance eqParticleEmitKernel :: Eq ParticleEmitKernel

instance showParticleEmitKernel :: Show ParticleEmitKernel where
  show (ParticleEmitKernel k) = "(ParticleEmitKernel emit:" <> show k.emitCount <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // sort
-- ═════════════════════════════════════════════════════════════════════════════

-- | Particle sort kernel (for depth ordering)
-- |
-- | Sorts particles for correct alpha blending (back-to-front).
newtype ParticleSortKernel = ParticleSortKernel
  { particleCount :: Int
  , sortAxis :: SortAxis       -- Which axis to sort on
  , config :: KernelConfig
  }

derive instance eqParticleSortKernel :: Eq ParticleSortKernel

instance showParticleSortKernel :: Show ParticleSortKernel where
  show (ParticleSortKernel k) = "(ParticleSortKernel count:" <> show k.particleCount <> ")"

-- | Sort axis for particles
data SortAxis
  = SortAxisZ                -- Sort by depth (Z coordinate)
  | SortAxisDistance         -- Sort by distance from camera

derive instance eqSortAxis :: Eq SortAxis
