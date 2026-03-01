-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                      // hydrogen // schema // motion // effects // simulation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Simulation Effects — Physics-based and procedural simulation effects.
-- |
-- | ## After Effects Parity
-- |
-- | Implements AE's Simulation effect category:
-- |
-- | - **CC Particle World**: Full 3D particle system
-- | - **CC Particle Systems II**: 2D particle system
-- | - **Shatter**: Glass/surface shatter effect
-- | - **Card Dance**: Grid-based card animation
-- | - **Caustics**: Water caustics simulation
-- | - **Wave World**: 3D water wave simulation
-- | - **Foam**: Bubble/foam generation
-- | - **CC Ball Action**: Ball grid effect
-- | - **CC Bubbles**: Rising bubbles effect
-- | - **CC Drizzle**: Rain drizzle effect
-- | - **CC Rain**: Rain particle effect
-- | - **CC Snowfall**: Snow particle effect
-- | - **CC Star Burst**: Star burst effect
-- |
-- | ## GPU Simulation
-- |
-- | These effects are computationally intensive. Particle systems
-- | typically run on GPU compute shaders in the runtime.
-- |
-- | ## Bounded Properties
-- |
-- | All properties use bounded types for deterministic simulation.
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from:
-- |
-- | - `Simulation.Particle` — Particle World and Particle Systems II
-- | - `Simulation.Surface` — Shatter and Card Dance
-- | - `Simulation.Water` — Caustics, Wave World, and Foam
-- | - `Simulation.Weather` — Drizzle, Rain, and Snowfall
-- | - `Simulation.Misc` — Ball Action, Bubbles, and Star Burst

module Hydrogen.Schema.Motion.Effects.Simulation
  ( -- * CC Particle World
    module Particle
  
  -- * Shatter and Card Dance
  , module Surface
  
  -- * Water Effects
  , module Water
  
  -- * Weather Effects
  , module Weather
  
  -- * Miscellaneous Effects
  , module Misc
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Motion.Effects.Simulation.Particle
  ( ParticleWorldEffect
  , ParticleType
      ( PTLine
      , PTTriPolyExplosive
      , PTTripolyBilinear
      , PTQuadPolyExplosive
      , PTQuadPolyBilinear
      , PTStarExplosive
      , PTStar
      , PTFadedSphere
      , PTShaded
      , PTBubble
      , PTTextured
      , PTCloudy
      , PTLensConvex
      , PTLensConcave
      , PTMotionPolygon
      )
  , PhysicsModel
      ( PMExplosive
      , PMTwirl
      , PMVortex
      , PMFire
      , PMJet
      , PMViscocity
      , PMDirectional
      , PMSprite
      )
  , defaultParticleWorld
  , particleWorldWithCount
  , ParticleSystemsEffect
  , defaultParticleSystems
  , particleTypeToString
  , physicsModelToString
  , particleWorldEffectName
  , particleSystemsEffectName
  , describeParticleWorld
  , particleWorldHasGravity
  , estimateParticleCount
  ) as Particle

import Hydrogen.Schema.Motion.Effects.Simulation.Surface
  ( ShatterEffect
  , ShatterShape
      ( SSGlass
      , SSBrick
      , SSPuzzle
      , SSTriangles
      , SSCustom
      )
  , ShatterForce
      ( SFGradient
      , SFRadius
      , SFDepth
      )
  , defaultShatter
  , shatterWithForce
  , CardDanceEffect
  , CardDanceAxis
      ( CDAPosition
      , CDARotation
      , CDAScale
      )
  , defaultCardDance
  , cardDanceWithRows
  , shatterShapeToString
  , shatterForceToString
  , cardDanceAxisToString
  , shatterEffectName
  , cardDanceEffectName
  , describeShatter
  , describeCardDance
  , isShatterRadial
  ) as Surface

import Hydrogen.Schema.Motion.Effects.Simulation.Water
  ( CausticsEffect
  , CausticsLightType
      ( CLTPointAbove
      , CLTDistantAbove
      , CLTPointBelow
      , CLTDistantBelow
      )
  , defaultCaustics
  , causticsWithIntensity
  , WaveWorldEffect
  , WaveMethod
      ( WMSteep
      , WMSmooth
      , WMRelaxed
      )
  , defaultWaveWorld
  , waveWorldWithHeight
  , FoamEffect
  , FoamProducer
      ( FPPoint
      , FPLine
      , FPArea
      )
  , defaultFoam
  , foamWithBubbles
  , causticsLightTypeToString
  , waveMethodToString
  , foamProducerToString
  , causticsEffectName
  , waveWorldEffectName
  , foamEffectName
  , describeCaustics
  , describeWaveWorld
  , isWaveWorldSteep
  , isFoamHighDensity
  , estimateFoamBubbles
  ) as Water

import Hydrogen.Schema.Motion.Effects.Simulation.Weather
  ( DrizzleEffect
  , defaultDrizzle
  , drizzleWithDrops
  , RainEffect
  , defaultRain
  , rainWithDrops
  , SnowfallEffect
  , SnowflakeType
      ( SFTDot
      , SFTCrystal
      , SFTFlake
      , SFTMixed
      )
  , defaultSnowfall
  , snowfallWithFlakes
  , snowflakeTypeToString
  , drizzleEffectName
  , rainEffectName
  , snowfallEffectName
  , rainHasWind
  , snowfallHasTurbulence
  ) as Weather

import Hydrogen.Schema.Motion.Effects.Simulation.Misc
  ( BallActionEffect
  , defaultBallAction
  , ballActionWithGrid
  , BubblesEffect
  , defaultBubbles
  , bubblesWithSize
  , StarBurstEffect
  , defaultStarBurst
  , starBurstWithCount
  , ballActionEffectName
  , bubblesEffectName
  , starBurstEffectName
  ) as Misc
