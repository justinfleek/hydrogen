-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // gpu // render-effect
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | RenderEffect — Unified Real-Time Effect Pipeline
-- |
-- | ## Design Philosophy
-- |
-- | Frame.io, Ghostty, Linear — hyper-responsive UIs that feel alive.
-- | This module provides the composable effect vocabulary for that experience:
-- |
-- | - **Blur effects**: Gaussian, directional, radial, zoom
-- | - **Glow effects**: Inner, outer, animated pulse, color cycling
-- | - **Shadow effects**: Drop, box, layered, animated
-- | - **Border effects**: Gradient stroke, conic rotation, marching ants
-- | - **Material effects**: Glass, frosted, noise, grain
-- | - **Temporal effects**: Motion blur, echo, time displacement
-- |
-- | ## Architecture
-- |
-- | Effects are **pure data** describing GPU render passes. At billion-agent
-- | scale, effects compose deterministically:
-- |
-- | ```
-- | Element + Effects → RenderPlan → GPU Passes → Tensor Output
-- | ```
-- |
-- | Same effect parameters = same pixels. Always.
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from:
-- | - `Hydrogen.GPU.RenderEffect.Types` — Shared types (GlowColor, BlendMode, etc.)
-- | - `Hydrogen.GPU.RenderEffect.Core` — RenderEffect ADT and composition
-- | - `Hydrogen.GPU.RenderEffect.Blur` — Blur effect variants
-- | - `Hydrogen.GPU.RenderEffect.Glow` — Glow effect variants
-- | - `Hydrogen.GPU.RenderEffect.Shadow` — Shadow effect variants
-- | - `Hydrogen.GPU.RenderEffect.Border` — Border effect variants
-- | - `Hydrogen.GPU.RenderEffect.Material` — Material effect variants
-- | - `Hydrogen.GPU.RenderEffect.Temporal` — Temporal effect variants
-- | - `Hydrogen.GPU.RenderEffect.Particle` — Particle effect variants
-- | - `Hydrogen.GPU.RenderEffect.Constructors` — Convenience constructors
-- | - `Hydrogen.GPU.RenderEffect.Presets` — Pre-configured effects

module Hydrogen.GPU.RenderEffect
  ( -- * Core Types
    module Hydrogen.GPU.RenderEffect.Core
  , module Hydrogen.GPU.RenderEffect.Types
  
  -- * Effect Categories
  , module Hydrogen.GPU.RenderEffect.Blur
  , module Hydrogen.GPU.RenderEffect.Glow
  , module Hydrogen.GPU.RenderEffect.Shadow
  , module Hydrogen.GPU.RenderEffect.Border
  , module Hydrogen.GPU.RenderEffect.Material
  , module Hydrogen.GPU.RenderEffect.Temporal
  , module Hydrogen.GPU.RenderEffect.Particle
  
  -- * GPU Primitives (from ComputeKernel)
  , module Hydrogen.GPU.ComputeKernel
  
  -- * Constructors & Presets
  , module Hydrogen.GPU.RenderEffect.Constructors
  , module Hydrogen.GPU.RenderEffect.Presets
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.GPU.RenderEffect.Types
  ( GlowColor
  , EffectPass
  , PassInput(InputPrevious, InputOriginal, InputTexture, InputMultiple)
  , PassOutput(OutputNext, OutputFinal, OutputTexture, OutputScreen)
  , BlendMode(BlendNormal, BlendAdd, BlendMultiply, BlendScreen, BlendOverlay, BlendSoftLight, BlendHardLight, BlendDifference, BlendExclusion)
  , EffectCondition(ConditionHover, ConditionActive, ConditionFocus, ConditionAnimationPhase, ConditionViewportSize, ConditionAlways)
  )

import Hydrogen.GPU.RenderEffect.Core
  ( RenderEffect(EffectBlur, EffectGlow, EffectShadow, EffectBorder, EffectMaterial, EffectTemporal, EffectParticle, EffectSequence, EffectParallel, EffectConditional, EffectAnimated, EffectNone)
  , effectSequence
  , effectParallel
  , effectConditional
  , effectWhen
  , effectIfThenElse
  , effectAnimated
  )

import Hydrogen.GPU.RenderEffect.Blur
  ( BlurEffect(BlurGaussian, BlurDirectional, BlurRadial, BlurZoom)
  , GaussianBlur(GaussianBlur)
  , DirectionalBlur(DirectionalBlur)
  , RadialBlur(RadialBlur)
  , ZoomBlur(ZoomBlur)
  )

import Hydrogen.GPU.ComputeKernel
  ( BlurQuality(BlurQualityLow, BlurQualityMedium, BlurQualityHigh)
  , RadialBlurType(RadialTypeSpin, RadialTypeZoom)
  )

import Hydrogen.GPU.RenderEffect.Glow
  ( GlowEffect(GlowInner, GlowOuter, GlowPulsing, GlowNeon)
  , InnerGlow(InnerGlow)
  , OuterGlow(OuterGlow)
  , PulsingGlow(PulsingGlow)
  , NeonGlow(NeonGlow)
  , GlowEasing(GlowEaseLinear, GlowEaseSine, GlowEaseQuad, GlowEaseCubic)
  )

import Hydrogen.GPU.RenderEffect.Shadow
  ( ShadowEffect(ShadowDrop, ShadowBox, ShadowContact)
  , DropShadowEffect(DropShadowEffect)
  , BoxShadowEffect(BoxShadowEffect)
  , ContactShadow(ContactShadow)
  )

import Hydrogen.GPU.RenderEffect.Border
  ( BorderEffect(BorderGradient, BorderConic, BorderAnimatedDash, BorderGlowing)
  , GradientBorder(GradientBorder)
  , ConicBorder(ConicBorder)
  , AnimatedDashBorder(AnimatedDashBorder)
  , GlowingBorder(GlowingBorder)
  , BorderGradientType(BorderGradientLinear, BorderGradientRadial, BorderGradientConic)
  , DashDirection(DashDirectionForward, DashDirectionBackward, DashDirectionAlternate)
  )

import Hydrogen.GPU.RenderEffect.Material
  ( MaterialEffect(MaterialGlass, MaterialFrosted, MaterialNoise, MaterialGrain)
  , GlassEffect(GlassEffect)
  , FrostedGlass(FrostedGlass)
  , NoiseOverlay(NoiseOverlay)
  , GrainEffect(GrainEffect)
  , NoiseType(NoisePerlin, NoiseSimplex, NoiseWorley, NoiseWhite, NoiseFBM)
  )

import Hydrogen.GPU.RenderEffect.Temporal
  ( TemporalEffect(TemporalMotionBlur, TemporalEcho, TemporalTimeWarp)
  , MotionBlur(MotionBlur)
  , EchoEffect(EchoEffect)
  , TimeWarp(TimeWarp)
  , EchoOperator(EchoAdd, EchoScreen, EchoMaximum, EchoMinimum, EchoBlend)
  )

import Hydrogen.GPU.RenderEffect.Particle
  ( ParticleEffect(ParticleFieldEffect, ParticleEmitterEffect)
  , ParticleField(ParticleField)
  , ParticleEmitter(ParticleEmitter)
  )

import Hydrogen.GPU.RenderEffect.Constructors
  ( gaussianBlur
  , directionalBlur
  , radialBlur
  , zoomBlur
  , innerGlow
  , outerGlow
  , pulsingGlow
  , neonGlow
  , dropShadowEffect
  , boxShadowEffect
  , contactShadow
  , gradientBorder
  , conicBorder
  , animatedDashBorder
  , glowingBorder
  , glassEffect
  , frostedGlass
  , noiseOverlay
  , grainEffect
  , motionBlur
  , echoEffect
  , timeWarp
  , particleField
  , particleEmitter
  )

import Hydrogen.GPU.RenderEffect.Presets
  ( subtleBlur
  , heavyBlur
  , backgroundBlur
  , heroBlur
  , centeredZoomBlur
  , softGlow
  , intenseGlow
  , elevatedShadow
  , floatingShadow
  , linearBorder
  , spotlightBorder
  , liquidGlass
  , acrylicGlass
  , filmGrain
  , digitalNoise
  )
