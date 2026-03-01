-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // reactive // hover-effect
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | HoverEffect — Interactive hover behaviors for UI elements.
-- |
-- | ## Design Philosophy
-- |
-- | Hover effects are declarative descriptions of what happens when a user
-- | hovers over an element. The runtime interprets these into actual
-- | event handlers and animations.
-- |
-- | ## Effect Categories
-- |
-- | - **Transform**: Scale, translate, rotate on hover
-- | - **Style**: Color, opacity, filter changes
-- | - **Audio**: Sound triggers on enter/leave
-- | - **Animation**: Lottie/CSS animation triggers
-- | - **Particle**: Particle burst effects
-- |
-- | ## State Machine
-- |
-- | ```
-- | idle → entering → hovering → leaving → idle
-- | ```
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from:
-- | - `HoverEffect.State` — Hover state machine
-- | - `HoverEffect.Transform` — Transform effects
-- | - `HoverEffect.Style` — Style effects
-- | - `HoverEffect.Audio` — Audio triggers
-- | - `HoverEffect.Animation` — Animation triggers
-- | - `HoverEffect.Particle` — Particle effects
-- | - `HoverEffect.Combined` — Combined hover effect
-- |
-- | ## Dependencies
-- |
-- | - Schema.Dimension.Temporal (timing)
-- | - Schema.Color.RGB (color changes)
-- | - Schema.Motion.Easing (transition curves)

module Hydrogen.Schema.Reactive.HoverEffect
  ( -- * Hover State
    module State
  
  -- * Transform Effects
  , module Transform
  
  -- * Style Effects
  , module Style
  
  -- * Audio Trigger
  , module Audio
  
  -- * Animation Trigger
  , module Animation
  
  -- * Particle Trigger
  , module Particle
  
  -- * Combined Hover Effect
  , module Combined
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Reactive.HoverEffect.State
  ( HoverState
      ( HoverIdle
      , HoverEntering
      , HoverActive
      , HoverLeaving
      )
  ) as State

import Hydrogen.Schema.Reactive.HoverEffect.Transform
  ( HoverTransform(..)
  , TransformOrigin(..)
  , hoverTransform
  , identityTransform
  , defaultHoverTransform
  , liftTransform
  , pressTransform
  , scaleUpTransform
  , elevatedHoverTransform
  ) as Transform

import Hydrogen.Schema.Reactive.HoverEffect.Style
  ( HoverStyle(..)
  , OpacityChange(..)
  , hoverStyle
  , identityStyle
  , defaultHoverStyle
  , subtleHoverStyle
  , prominentHoverStyle
  , glowHoverStyle
  , dimHoverStyle
  ) as Style

import Hydrogen.Schema.Reactive.HoverEffect.Audio
  ( HoverAudio(..)
  , HoverAudioSource(..)
  , hoverAudio
  , noHoverAudio
  , hoverAudioEnter
  , hoverAudioEnterLeave
  , hoverAudioLoop
  ) as Audio

import Hydrogen.Schema.Reactive.HoverEffect.Animation
  ( HoverAnimation(..)
  , HoverAnimationType(..)
  , HoverSpringConfig
  , hoverAnimation
  , noHoverAnimation
  , hoverAnimationLottie
  , hoverAnimationCss
  , hoverAnimationSpring
  , defaultSpringConfig
  ) as Animation

import Hydrogen.Schema.Reactive.HoverEffect.Particle
  ( HoverParticle(..)
  , ParticleType(..)
  , EmissionMode(..)
  , hoverParticle
  , noHoverParticle
  , hoverParticleBurst
  , hoverParticleContinuous
  , hoverParticleTrail
  ) as Particle

import Hydrogen.Schema.Reactive.HoverEffect.Combined
  ( HoverEffect(..)
  , hoverEffect
  , noHoverEffect
  , defaultHoverEffect
  , subtleHoverEffect
  , prominentHoverEffect
  , glowHoverEffect
  , audioHoverEffect
  , animatedHoverEffect
  , sparkleHoverEffect
  ) as Combined
