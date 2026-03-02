-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                    // hydrogen // schema // reactive // hover-effect/combined
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | HoverEffect — Combined hover effect configuration.
-- |
-- | ## Design Philosophy
-- |
-- | Composes all hover effect types into a single configuration:
-- | - Transform (scale, translate, rotate)
-- | - Style (brightness, shadows, filters)
-- | - Audio (enter/leave/loop sounds)
-- | - Animation (Lottie, CSS, spring)
-- | - Particle (sparkles, confetti, etc.)
-- |
-- | ## Timing
-- |
-- | All effects share common timing parameters:
-- | - `transitionDurationMs`: How long transitions take
-- | - `transitionDelay`: Delay before starting
-- |
-- | ## Examples
-- |
-- | ```purescript
-- | -- Basic hover with lift and shadow
-- | basicHover = defaultHoverEffect
-- |
-- | -- Complex hover with audio and particles
-- | fancyHover = hoverEffect
-- |   { transform: liftTransform
-- |   , style: glowHoverStyle
-- |   , audio: hoverAudioEnter (HoverAudioUrl "/click.mp3") 0.5
-- |   , animation: noHoverAnimation
-- |   , particle: hoverParticleBurst SparkleParticle 10
-- |   , transitionDurationMs: 200.0
-- |   , transitionDelay: 0.0
-- |   }
-- | ```

module Hydrogen.Schema.Reactive.HoverEffect.Combined
  ( HoverEffect(HoverEffect)
  , hoverEffect
  , noHoverEffect
  , defaultHoverEffect
  , subtleHoverEffect
  , prominentHoverEffect
  , glowHoverEffect
  , audioHoverEffect
  , animatedHoverEffect
  , sparkleHoverEffect
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
  )

import Hydrogen.Schema.Reactive.HoverEffect.Transform
  ( HoverTransform
  , identityTransform
  , defaultHoverTransform
  , liftTransform
  , scaleUpTransform
  )

import Hydrogen.Schema.Reactive.HoverEffect.Style
  ( HoverStyle
  , identityStyle
  , defaultHoverStyle
  , subtleHoverStyle
  , prominentHoverStyle
  , glowHoverStyle
  )

import Hydrogen.Schema.Reactive.HoverEffect.Audio
  ( HoverAudio
  , HoverAudioSource
  , noHoverAudio
  , hoverAudioEnter
  )

import Hydrogen.Schema.Reactive.HoverEffect.Animation
  ( HoverAnimation
  , noHoverAnimation
  , hoverAnimationLottie
  )

import Hydrogen.Schema.Reactive.HoverEffect.Particle
  ( HoverParticle
  , ParticleType
      ( SparkleParticle
      )
  , noHoverParticle
  , hoverParticleBurst
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // hover effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Combined hover effect configuration
newtype HoverEffect = HoverEffect
  { transform :: HoverTransform          -- ^ Transform on hover
  , style :: HoverStyle                  -- ^ Style changes on hover
  , audio :: HoverAudio                  -- ^ Audio triggers
  , animation :: HoverAnimation          -- ^ Animation triggers
  , particle :: HoverParticle            -- ^ Particle effects
  , transitionDurationMs :: Number       -- ^ Duration of transitions
  , transitionDelay :: Number            -- ^ Delay before transition starts
  }

derive instance eqHoverEffect :: Eq HoverEffect

instance showHoverEffect :: Show HoverEffect where
  show (HoverEffect e) = 
    "HoverEffect(duration:" <> show e.transitionDurationMs <> "ms)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create hover effect with full configuration
hoverEffect
  :: { transform :: HoverTransform
     , style :: HoverStyle
     , audio :: HoverAudio
     , animation :: HoverAnimation
     , particle :: HoverParticle
     , transitionDurationMs :: Number
     , transitionDelay :: Number
     }
  -> HoverEffect
hoverEffect cfg = HoverEffect
  { transform: cfg.transform
  , style: cfg.style
  , audio: cfg.audio
  , animation: cfg.animation
  , particle: cfg.particle
  , transitionDurationMs: clampMs cfg.transitionDurationMs
  , transitionDelay: clampMs cfg.transitionDelay
  }
  where
    clampMs ms
      | ms < 0.0 = 0.0
      | otherwise = ms

-- | No hover effect (completely inert)
noHoverEffect :: HoverEffect
noHoverEffect = HoverEffect
  { transform: identityTransform
  , style: identityStyle
  , audio: noHoverAudio
  , animation: noHoverAnimation
  , particle: noHoverParticle
  , transitionDurationMs: 0.0
  , transitionDelay: 0.0
  }

-- | Default hover effect (subtle lift + brightness).
-- |
-- | Research-based defaults:
-- | - 150ms duration (optimal for perceived responsiveness)
-- | - Slight Y translation (-1px lift)
-- | - 5% brightness increase
-- | - 25% shadow intensity increase
defaultHoverEffect :: HoverEffect
defaultHoverEffect = HoverEffect
  { transform: defaultHoverTransform
  , style: defaultHoverStyle
  , audio: noHoverAudio
  , animation: noHoverAnimation
  , particle: noHoverParticle
  , transitionDurationMs: 150.0
  , transitionDelay: 0.0
  }

-- | Subtle hover (minimal visual feedback)
subtleHoverEffect :: HoverEffect
subtleHoverEffect = HoverEffect
  { transform: identityTransform
  , style: subtleHoverStyle
  , audio: noHoverAudio
  , animation: noHoverAnimation
  , particle: noHoverParticle
  , transitionDurationMs: 100.0
  , transitionDelay: 0.0
  }

-- | Prominent hover (more noticeable feedback)
prominentHoverEffect :: HoverEffect
prominentHoverEffect = HoverEffect
  { transform: liftTransform
  , style: prominentHoverStyle
  , audio: noHoverAudio
  , animation: noHoverAnimation
  , particle: noHoverParticle
  , transitionDurationMs: 200.0
  , transitionDelay: 0.0
  }

-- | Glow hover (emissive appearance)
glowHoverEffect :: HoverEffect
glowHoverEffect = HoverEffect
  { transform: scaleUpTransform
  , style: glowHoverStyle
  , audio: noHoverAudio
  , animation: noHoverAnimation
  , particle: noHoverParticle
  , transitionDurationMs: 250.0
  , transitionDelay: 0.0
  }

-- | Interactive hover with audio feedback
audioHoverEffect :: HoverAudioSource -> Number -> HoverEffect
audioHoverEffect audioSrc volume = HoverEffect
  { transform: defaultHoverTransform
  , style: defaultHoverStyle
  , audio: hoverAudioEnter audioSrc volume
  , animation: noHoverAnimation
  , particle: noHoverParticle
  , transitionDurationMs: 150.0
  , transitionDelay: 0.0
  }

-- | Animated hover with Lottie
animatedHoverEffect :: String -> HoverEffect
animatedHoverEffect lottieUrl = HoverEffect
  { transform: identityTransform
  , style: identityStyle
  , audio: noHoverAudio
  , animation: hoverAnimationLottie lottieUrl
  , particle: noHoverParticle
  , transitionDurationMs: 0.0
  , transitionDelay: 0.0
  }

-- | Particle hover with sparkles
sparkleHoverEffect :: HoverEffect
sparkleHoverEffect = HoverEffect
  { transform: scaleUpTransform
  , style: glowHoverStyle
  , audio: noHoverAudio
  , animation: noHoverAnimation
  , particle: hoverParticleBurst SparkleParticle 15
  , transitionDurationMs: 200.0
  , transitionDelay: 0.0
  }
