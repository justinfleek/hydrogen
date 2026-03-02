-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // schema // motion // effects // particle
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Particle Effects — CC Particle World and CC Particle Systems II.
-- |
-- | ## Industry Standard
-- |
-- | - **CC Particle World**: Full 3D particle system
-- | - **CC Particle Systems II**: 2D particle system
-- |
-- | ## GPU Simulation
-- |
-- | Particle systems typically run on GPU compute shaders in the runtime.

module Hydrogen.Schema.Motion.Effects.Simulation.Particle
  ( -- * CC Particle World
    ParticleWorldEffect
  , ParticleType(..)
  , PhysicsModel(..)
  , defaultParticleWorld
  , particleWorldWithCount
  
  -- * CC Particle Systems II
  , ParticleSystemsEffect
  , defaultParticleSystems
  
  -- * Serialization
  , particleTypeToString
  , physicsModelToString
  
  -- * Effect Names
  , particleWorldEffectName
  , particleSystemsEffectName
  
  -- * Effect Descriptions
  , describeParticleWorld
  
  -- * Queries
  , particleWorldHasGravity
  , estimateParticleCount
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , ($)
  , (<>)
  , (>)
  , (*)
  , show
  )

import Hydrogen.Schema.Bounded (clampNumber)
import Hydrogen.Schema.Color.RGB (RGB, rgb)
import Hydrogen.Schema.Dimension.Point2D (Point2D, point2D)
import Hydrogen.Schema.Dimension.Vector.Vec3 (Vec3, vec3)
import Hydrogen.Schema.Motion.Composition (BlendMode(..))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // particle // world
-- ═════════════════════════════════════════════════════════════════════════════

-- | Particle type — visual appearance of particles.
data ParticleType
  = PTLine              -- ^ Line particles
  | PTTriPolyExplosive  -- ^ Exploding triangular polygon
  | PTTripolyBilinear   -- ^ Bilinear triangular polygon
  | PTQuadPolyExplosive -- ^ Exploding quad polygon
  | PTQuadPolyBilinear  -- ^ Bilinear quad polygon
  | PTStarExplosive     -- ^ Exploding star
  | PTStar              -- ^ Star shape
  | PTFadedSphere       -- ^ Faded sphere
  | PTShaded            -- ^ Shaded 3D sphere
  | PTBubble            -- ^ Transparent bubble
  | PTTextured          -- ^ Textured from layer
  | PTCloudy            -- ^ Cloud-like
  | PTLensConvex        -- ^ Convex lens
  | PTLensConcave       -- ^ Concave lens
  | PTMotionPolygon     -- ^ Motion-blurred polygon

derive instance eqParticleType :: Eq ParticleType
derive instance ordParticleType :: Ord ParticleType

instance showParticleType :: Show ParticleType where
  show PTLine = "line"
  show PTTriPolyExplosive = "tri-poly-explosive"
  show PTTripolyBilinear = "tri-poly-bilinear"
  show PTQuadPolyExplosive = "quad-poly-explosive"
  show PTQuadPolyBilinear = "quad-poly-bilinear"
  show PTStarExplosive = "star-explosive"
  show PTStar = "star"
  show PTFadedSphere = "faded-sphere"
  show PTShaded = "shaded"
  show PTBubble = "bubble"
  show PTTextured = "textured"
  show PTCloudy = "cloudy"
  show PTLensConvex = "lens-convex"
  show PTLensConcave = "lens-concave"
  show PTMotionPolygon = "motion-polygon"

-- | Physics model — how particles interact.
data PhysicsModel
  = PMExplosive         -- ^ Outward explosion
  | PMTwirl             -- ^ Spiral motion
  | PMVortex            -- ^ Vortex suction
  | PMFire              -- ^ Fire-like rising
  | PMJet               -- ^ Directional jet
  | PMViscocity         -- ^ Viscous fluid
  | PMDirectional       -- ^ Fixed direction
  | PMSprite            -- ^ Sprite behavior

derive instance eqPhysicsModel :: Eq PhysicsModel
derive instance ordPhysicsModel :: Ord PhysicsModel

instance showPhysicsModel :: Show PhysicsModel where
  show PMExplosive = "explosive"
  show PMTwirl = "twirl"
  show PMVortex = "vortex"
  show PMFire = "fire"
  show PMJet = "jet"
  show PMViscocity = "viscocity"
  show PMDirectional = "directional"
  show PMSprite = "sprite"

-- | CC Particle World Effect — full 3D particle system.
-- |
-- | ## AE Properties
-- |
-- | The most comprehensive particle system in AE.
-- | Supports birth/death, physics, rendering options.
type ParticleWorldEffect =
  { -- Birth
    birthRate :: Number              -- ^ Particles per second (0-10000)
  , longevity :: Number              -- ^ Particle life in seconds (0-100)
  
  -- Producer
  , producerPosition :: Vec3 Number  -- ^ Emitter position (x, y, z)
  , producerRadius :: { x :: Number, y :: Number, z :: Number }  -- ^ Emitter size
  
  -- Physics
  , velocity :: Number               -- ^ Initial velocity (0-500)
  , inheritVelocity :: Number        -- ^ From layer motion (0-100 %)
  , gravity :: Number                -- ^ Gravity strength (-100 to 100)
  , physicsModel :: PhysicsModel     -- ^ Physics behavior
  
  -- Particle
  , particleType :: ParticleType     -- ^ Visual type
  , birthSize :: Number              -- ^ Size at birth (0-500)
  , deathSize :: Number              -- ^ Size at death (0-500)
  , birthColor :: RGB                -- ^ Color at birth
  , deathColor :: RGB                -- ^ Color at death
  , birthOpacity :: Number           -- ^ Opacity at birth (0-100)
  , deathOpacity :: Number           -- ^ Opacity at death (0-100)
  
  -- Rendering
  , transferMode :: BlendMode        -- ^ Blend mode
  , randomSeed :: Int                -- ^ Random seed
  }

-- | Default particle world: moderate birth rate, white particles.
defaultParticleWorld :: ParticleWorldEffect
defaultParticleWorld =
  { birthRate: 100.0
  , longevity: 2.0
  , producerPosition: vec3 0.0 0.0 0.0
  , producerRadius: { x: 10.0, y: 10.0, z: 10.0 }
  , velocity: 50.0
  , inheritVelocity: 0.0
  , gravity: 0.0
  , physicsModel: PMExplosive
  , particleType: PTFadedSphere
  , birthSize: 10.0
  , deathSize: 1.0
  , birthColor: rgb 255 255 255
  , deathColor: rgb 255 255 255
  , birthOpacity: 100.0
  , deathOpacity: 0.0
  , transferMode: BMAdd
  , randomSeed: 0
  }

-- | Create particle world with specific count.
particleWorldWithCount :: Number -> Number -> ParticleWorldEffect
particleWorldWithCount rate life =
  { birthRate: clampNumber 0.0 10000.0 rate
  , longevity: clampNumber 0.0 100.0 life
  , producerPosition: vec3 0.0 0.0 0.0
  , producerRadius: { x: 10.0, y: 10.0, z: 10.0 }
  , velocity: 50.0
  , inheritVelocity: 0.0
  , gravity: 0.0
  , physicsModel: PMExplosive
  , particleType: PTFadedSphere
  , birthSize: 10.0
  , deathSize: 1.0
  , birthColor: rgb 255 255 255
  , deathColor: rgb 255 255 255
  , birthOpacity: 100.0
  , deathOpacity: 0.0
  , transferMode: BMAdd
  , randomSeed: 0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // particle // systems // ii
-- ═════════════════════════════════════════════════════════════════════════════

-- | CC Particle Systems II Effect — simpler 2D particle system.
-- |
-- | Less complex than Particle World, but faster.
type ParticleSystemsEffect =
  { birthRate :: Number              -- ^ Particles per second (0-2000)
  , longevity :: Number              -- ^ Particle life (0-20 seconds)
  , producerPosition :: Point2D      -- ^ Emitter position
  , producerRadius :: Number         -- ^ Emitter radius (0-1000)
  , direction :: Number              -- ^ Direction angle (0-360)
  , directionSpread :: Number        -- ^ Spread angle (0-180)
  , velocity :: Number               -- ^ Initial velocity (0-200)
  , gravity :: Number                -- ^ Gravity (-100 to 100)
  , resistance :: Number             -- ^ Air resistance (0-100)
  , particleType :: ParticleType     -- ^ Visual type
  , birthSize :: Number              -- ^ Size at birth (0-100)
  , deathSize :: Number              -- ^ Size at death (0-100)
  , birthColor :: RGB                -- ^ Color at birth
  , deathColor :: RGB                -- ^ Color at death
  , transferMode :: BlendMode        -- ^ Blend mode
  , randomSeed :: Int                -- ^ Random seed
  }

-- | Default particle systems II.
defaultParticleSystems :: ParticleSystemsEffect
defaultParticleSystems =
  { birthRate: 50.0
  , longevity: 2.0
  , producerPosition: point2D 100.0 100.0
  , producerRadius: 5.0
  , direction: 270.0  -- Up
  , directionSpread: 45.0
  , velocity: 30.0
  , gravity: 10.0
  , resistance: 5.0
  , particleType: PTFadedSphere
  , birthSize: 8.0
  , deathSize: 2.0
  , birthColor: rgb 255 200 100
  , deathColor: rgb 200 50 0
  , transferMode: BMAdd
  , randomSeed: 0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert ParticleType to string.
particleTypeToString :: ParticleType -> String
particleTypeToString pt = show pt

-- | Convert PhysicsModel to string.
physicsModelToString :: PhysicsModel -> String
physicsModelToString pm = show pm

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // effect // names
-- ═════════════════════════════════════════════════════════════════════════════

-- | Effect name for Particle World.
particleWorldEffectName :: ParticleWorldEffect -> String
particleWorldEffectName _ = "CC Particle World"

-- | Effect name for Particle Systems II.
particleSystemsEffectName :: ParticleSystemsEffect -> String
particleSystemsEffectName _ = "CC Particle Systems II"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // effect // descriptions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create particle world description.
describeParticleWorld :: ParticleWorldEffect -> String
describeParticleWorld e =
  "ParticleWorld(" <> show e.birthRate <> " particles/sec, " <>
  show e.physicsModel <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if particle world has gravity.
particleWorldHasGravity :: ParticleWorldEffect -> Boolean
particleWorldHasGravity e = e.gravity > 0.0

-- | Get particle world total particles estimate.
estimateParticleCount :: ParticleWorldEffect -> Number
estimateParticleCount e = clampNumber 0.0 100000.0 $ e.birthRate * e.longevity
