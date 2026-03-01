-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                    // hydrogen // schema // reactive // hover-effect/particle
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | HoverParticle — Particle effect triggered on hover.
-- |
-- | ## Design Philosophy
-- |
-- | Describes particle systems that emit on hover:
-- | - Sparkles, confetti, dust, bubbles
-- | - Emit from element center or follow cursor
-- | - Customizable colors, sizes, and behaviors
-- |
-- | ## Emission Modes
-- |
-- | - `EmitBurst`: Single burst on enter
-- | - `EmitContinuous`: Continuous emission while hovered
-- | - `EmitOnMove`: Emit particles following cursor movement
-- |
-- | ## Examples
-- |
-- | ```purescript
-- | -- Sparkle burst on hover
-- | sparkles = hoverParticleBurst SparkleParticle 20
-- |
-- | -- Continuous snow while hovering
-- | snow = hoverParticleContinuous SnowParticle 5
-- | ```

module Hydrogen.Schema.Reactive.HoverEffect.Particle
  ( HoverParticle(..)
  , ParticleType(..)
  , EmissionMode(..)
  , hoverParticle
  , noHoverParticle
  , hoverParticleBurst
  , hoverParticleContinuous
  , hoverParticleTrail
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , otherwise
  , (<>)
  , (<)
  , (>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // particle type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Visual type of particle
data ParticleType
  = NoParticle                          -- ^ No particles
  | SparkleParticle                     -- ^ Star-shaped sparkles
  | ConfettiParticle                    -- ^ Rectangular confetti
  | DustParticle                        -- ^ Small circular dust
  | BubbleParticle                      -- ^ Translucent bubbles
  | SnowParticle                        -- ^ Snowflake shapes
  | HeartParticle                       -- ^ Heart shapes
  | StarParticle                        -- ^ Star shapes
  | CustomParticle String               -- ^ Custom SVG path

derive instance eqParticleType :: Eq ParticleType

instance showParticleType :: Show ParticleType where
  show NoParticle = "none"
  show SparkleParticle = "sparkle"
  show ConfettiParticle = "confetti"
  show DustParticle = "dust"
  show BubbleParticle = "bubble"
  show SnowParticle = "snow"
  show HeartParticle = "heart"
  show StarParticle = "star"
  show (CustomParticle _) = "custom"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // emission mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | How particles are emitted
data EmissionMode
  = EmitNone                            -- ^ No emission
  | EmitBurst                           -- ^ Single burst on hover enter
  | EmitContinuous                      -- ^ Continuous while hovering
  | EmitOnMove                          -- ^ Emit following cursor
  | EmitOnLeave                         -- ^ Burst when mouse leaves

derive instance eqEmissionMode :: Eq EmissionMode

instance showEmissionMode :: Show EmissionMode where
  show EmitNone = "none"
  show EmitBurst = "burst"
  show EmitContinuous = "continuous"
  show EmitOnMove = "on-move"
  show EmitOnLeave = "on-leave"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // hover particle
-- ═════════════════════════════════════════════════════════════════════════════

-- | Particle effect triggered on hover
newtype HoverParticle = HoverParticle
  { particleType :: ParticleType        -- ^ Visual style of particles
  , emissionMode :: EmissionMode        -- ^ How particles are emitted
  , count :: Int                        -- ^ Particles per emission
  , lifetimeMs :: Number                -- ^ How long each particle lives
  , spread :: Number                    -- ^ Spread angle in degrees (0-360)
  , speed :: Number                     -- ^ Initial velocity (pixels/second)
  , gravity :: Number                   -- ^ Downward acceleration (pixels/s²)
  , fadeOut :: Boolean                  -- ^ Fade opacity as particle ages
  , shrink :: Boolean                   -- ^ Shrink size as particle ages
  }

derive instance eqHoverParticle :: Eq HoverParticle

instance showHoverParticle :: Show HoverParticle where
  show (HoverParticle p) = 
    "HoverParticle(" <> show p.particleType <> 
    ", " <> show p.emissionMode <> 
    ", count:" <> show p.count <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create hover particle with full configuration
hoverParticle
  :: { particleType :: ParticleType
     , emissionMode :: EmissionMode
     , count :: Int
     , lifetimeMs :: Number
     , spread :: Number
     , speed :: Number
     , gravity :: Number
     , fadeOut :: Boolean
     , shrink :: Boolean
     }
  -> HoverParticle
hoverParticle cfg = HoverParticle
  { particleType: cfg.particleType
  , emissionMode: cfg.emissionMode
  , count: clampCount cfg.count
  , lifetimeMs: clampMs cfg.lifetimeMs
  , spread: clampSpread cfg.spread
  , speed: clampPositive cfg.speed
  , gravity: cfg.gravity
  , fadeOut: cfg.fadeOut
  , shrink: cfg.shrink
  }
  where
    clampCount c
      | c < 0 = 0
      | c > 1000 = 1000
      | otherwise = c
    clampMs ms
      | ms < 0.0 = 0.0
      | otherwise = ms
    clampSpread s
      | s < 0.0 = 0.0
      | s > 360.0 = 360.0
      | otherwise = s
    clampPositive v
      | v < 0.0 = 0.0
      | otherwise = v

-- | No hover particles
noHoverParticle :: HoverParticle
noHoverParticle = HoverParticle
  { particleType: NoParticle
  , emissionMode: EmitNone
  , count: 0
  , lifetimeMs: 0.0
  , spread: 0.0
  , speed: 0.0
  , gravity: 0.0
  , fadeOut: false
  , shrink: false
  }

-- | Burst of particles on hover enter
hoverParticleBurst :: ParticleType -> Int -> HoverParticle
hoverParticleBurst pType count = HoverParticle
  { particleType: pType
  , emissionMode: EmitBurst
  , count: count
  , lifetimeMs: 1000.0
  , spread: 360.0
  , speed: 100.0
  , gravity: 50.0
  , fadeOut: true
  , shrink: true
  }

-- | Continuous particles while hovering
hoverParticleContinuous :: ParticleType -> Int -> HoverParticle
hoverParticleContinuous pType countPerSecond = HoverParticle
  { particleType: pType
  , emissionMode: EmitContinuous
  , count: countPerSecond
  , lifetimeMs: 2000.0
  , spread: 180.0
  , speed: 50.0
  , gravity: 20.0
  , fadeOut: true
  , shrink: false
  }

-- | Particles following cursor movement
hoverParticleTrail :: ParticleType -> HoverParticle
hoverParticleTrail pType = HoverParticle
  { particleType: pType
  , emissionMode: EmitOnMove
  , count: 3
  , lifetimeMs: 500.0
  , spread: 45.0
  , speed: 30.0
  , gravity: 0.0
  , fadeOut: true
  , shrink: true
  }
