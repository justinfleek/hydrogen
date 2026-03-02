-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // gpu // render-effect/particle
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Particle effects for the RenderEffect system.
-- |
-- | Provides two particle system variants:
-- | - **Field**: Ambient particles distributed across area
-- | - **Emitter**: Particles spawning from a point source

module Hydrogen.GPU.RenderEffect.Particle
  ( -- * Particle Effect Type
    ParticleEffect
      ( ParticleFieldEffect
      , ParticleEmitterEffect
      )
  
  -- * Particle Variants
  , ParticleField(ParticleField)
  , ParticleEmitter(ParticleEmitter)
  
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

import Hydrogen.GPU.RenderEffect.Types (GlowColor)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // particle effects
-- ═════════════════════════════════════════════════════════════════════════════

-- | Particle effect variants
-- |
-- | Particle systems are simulated on the GPU. Despite being "stateful" in
-- | appearance, particle state is derived deterministically from FrameState
-- | using seeded pseudo-random generators, ensuring reproducibility.
data ParticleEffect
  = ParticleFieldEffect ParticleField
  | ParticleEmitterEffect ParticleEmitter

derive instance eqParticleEffect :: Eq ParticleEffect

instance showParticleEffect :: Show ParticleEffect where
  show (ParticleFieldEffect p) = "(ParticleFieldEffect " <> show p <> ")"
  show (ParticleEmitterEffect p) = "(ParticleEmitterEffect " <> show p <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // particle variants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Particle field — ambient particles in area
-- |
-- | Creates a field of particles drifting through the element bounds.
-- | Useful for snow, dust, sparkles, and ambient atmosphere.
newtype ParticleField = ParticleField
  { count :: Int             -- Number of particles
  , sizeMin :: Number        -- Minimum particle size
  , sizeMax :: Number        -- Maximum particle size
  , color :: GlowColor       -- Particle color
  , speedMin :: Number       -- Minimum speed
  , speedMax :: Number       -- Maximum speed
  , direction :: Number      -- Base direction (degrees)
  , spread :: Number         -- Direction spread (degrees)
  , lifetime :: Number       -- Particle lifetime (seconds)
  , fadeIn :: Number         -- Fade in duration (0.0-1.0 of lifetime)
  , fadeOut :: Number        -- Fade out duration (0.0-1.0 of lifetime)
  }

derive instance eqParticleField :: Eq ParticleField

instance showParticleField :: Show ParticleField where
  show (ParticleField p) = "(ParticleField count:" <> show p.count <> ")"

-- | Particle emitter — particles from point
-- |
-- | Spawns particles from a specific position with velocity and gravity.
-- | Useful for sparks, explosions, fountains, and directional effects.
newtype ParticleEmitter = ParticleEmitter
  { positionX :: Number      -- Emitter X position (0.0-1.0)
  , positionY :: Number      -- Emitter Y position (0.0-1.0)
  , rate :: Number           -- Particles per second
  , sizeMin :: Number
  , sizeMax :: Number
  , color :: GlowColor
  , velocity :: Number       -- Initial velocity
  , gravity :: Number        -- Gravity strength
  , spread :: Number         -- Emission cone spread (degrees)
  , lifetime :: Number       -- Particle lifetime (seconds)
  }

derive instance eqParticleEmitter :: Eq ParticleEmitter

instance showParticleEmitter :: Show ParticleEmitter where
  show (ParticleEmitter p) = "(ParticleEmitter rate:" <> show p.rate <> ")"
