-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // gpu // render-effect/constructors
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Convenience constructors for RenderEffect values.
-- |
-- | These functions provide sensible defaults for common effect configurations,
-- | making it easy to create effects without specifying every parameter.

module Hydrogen.GPU.RenderEffect.Constructors
  ( -- * Blur Constructors
    gaussianBlur
  , directionalBlur
  , radialBlur
  , zoomBlur
  
  -- * Glow Constructors
  , innerGlow
  , outerGlow
  , pulsingGlow
  , neonGlow
  
  -- * Shadow Constructors
  , dropShadowEffect
  , boxShadowEffect
  , contactShadow
  
  -- * Border Constructors
  , gradientBorder
  , conicBorder
  , animatedDashBorder
  , glowingBorder
  
  -- * Material Constructors
  , glassEffect
  , frostedGlass
  , noiseOverlay
  , grainEffect
  
  -- * Temporal Constructors
  , motionBlur
  , echoEffect
  , timeWarp
  
  -- * Particle Constructors
  , particleField
  , particleEmitter
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.GPU.ComputeKernel
  ( BlurQuality(BlurQualityMedium)
  , RadialBlurType(RadialTypeSpin)
  )

import Hydrogen.GPU.RenderEffect.Types (GlowColor)

import Hydrogen.GPU.RenderEffect.Blur
  ( BlurEffect(BlurGaussian, BlurDirectional, BlurRadial, BlurZoom)
  , GaussianBlur(GaussianBlur)
  , DirectionalBlur(DirectionalBlur)
  , RadialBlur(RadialBlur)
  , ZoomBlur(ZoomBlur)
  )

import Hydrogen.GPU.RenderEffect.Glow
  ( GlowEffect(GlowInner, GlowOuter, GlowPulsing, GlowNeon)
  , InnerGlow(InnerGlow)
  , OuterGlow(OuterGlow)
  , PulsingGlow(PulsingGlow)
  , NeonGlow(NeonGlow)
  , GlowEasing(GlowEaseSine)
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
  , BorderGradientType(BorderGradientLinear)
  , DashDirection(DashDirectionForward)
  )

import Hydrogen.GPU.RenderEffect.Material
  ( MaterialEffect(MaterialGlass, MaterialFrosted, MaterialNoise, MaterialGrain)
  , GlassEffect(GlassEffect)
  , FrostedGlass(FrostedGlass)
  , NoiseOverlay(NoiseOverlay)
  , GrainEffect(GrainEffect)
  , NoiseType
  )

import Hydrogen.GPU.RenderEffect.Temporal
  ( TemporalEffect(TemporalMotionBlur, TemporalEcho, TemporalTimeWarp)
  , MotionBlur(MotionBlur)
  , EchoEffect(EchoEffect)
  , TimeWarp(TimeWarp)
  , EchoOperator(EchoBlend)
  )

import Hydrogen.GPU.RenderEffect.Particle
  ( ParticleEffect(ParticleFieldEffect, ParticleEmitterEffect)
  , ParticleField(ParticleField)
  , ParticleEmitter(ParticleEmitter)
  )

import Hydrogen.GPU.RenderEffect.Core (RenderEffect(EffectBlur, EffectGlow, EffectShadow, EffectBorder, EffectMaterial, EffectTemporal, EffectParticle))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // blur constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a Gaussian blur effect with medium quality
gaussianBlur :: Number -> RenderEffect
gaussianBlur radius = EffectBlur (BlurGaussian (GaussianBlur
  { radius, quality: BlurQualityMedium }))

-- | Create a directional blur effect
directionalBlur :: Number -> Number -> RenderEffect
directionalBlur angle distance = EffectBlur (BlurDirectional (DirectionalBlur
  { angle, distance, quality: BlurQualityMedium }))

-- | Create a radial blur effect (spin type)
radialBlur :: Number -> Number -> Number -> RenderEffect
radialBlur centerX centerY amount = EffectBlur (BlurRadial (RadialBlur
  { centerX, centerY, amount, blurType: RadialTypeSpin }))

-- | Create a zoom blur effect
zoomBlur :: Number -> Number -> Number -> RenderEffect
zoomBlur centerX centerY strength = EffectBlur (BlurZoom (ZoomBlur
  { centerX, centerY, strength }))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // glow constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create an inner glow effect
innerGlow :: GlowColor -> Number -> Number -> RenderEffect
innerGlow color radius intensity = EffectGlow (GlowInner (InnerGlow
  { color, radius, intensity, choke: 0.0 }))

-- | Create an outer glow effect
outerGlow :: GlowColor -> Number -> Number -> RenderEffect
outerGlow color radius intensity = EffectGlow (GlowOuter (OuterGlow
  { color, radius, intensity, spread: 0.0 }))

-- | Create a pulsing glow effect
pulsingGlow :: GlowColor -> Number -> Number -> Number -> RenderEffect
pulsingGlow color minRadius maxRadius periodMs = EffectGlow (GlowPulsing (PulsingGlow
  { color, minRadius, maxRadius, minIntensity: 0.3, maxIntensity: 1.0
  , periodMs, easing: GlowEaseSine }))

-- | Create a neon glow effect
neonGlow :: GlowColor -> GlowColor -> Number -> RenderEffect
neonGlow coreColor outerColor intensity = EffectGlow (GlowNeon (NeonGlow
  { coreColor, outerColor, coreRadius: 2.0, outerRadius: 16.0
  , intensity, flicker: false, flickerSpeed: 0.0 }))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // shadow constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a drop shadow effect
dropShadowEffect :: Number -> Number -> Number -> GlowColor -> RenderEffect
dropShadowEffect offsetX offsetY blur color = EffectShadow (ShadowDrop (DropShadowEffect
  { offsetX, offsetY, blur, color }))

-- | Create a box shadow effect
boxShadowEffect :: Number -> Number -> Number -> Number -> GlowColor -> RenderEffect
boxShadowEffect offsetX offsetY blur spread color = EffectShadow (ShadowBox (BoxShadowEffect
  { offsetX, offsetY, blur, spread, color, inset: false }))

-- | Create a contact shadow effect
contactShadow :: Number -> Number -> RenderEffect
contactShadow blur opacity = EffectShadow (ShadowContact (ContactShadow
  { blur, opacity, offsetY: 2.0, scale: 0.9 }))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // border constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a gradient border effect
gradientBorder :: Number -> Array GlowColor -> Number -> RenderEffect
gradientBorder width colors angle = EffectBorder (BorderGradient (GradientBorder
  { width, gradientType: BorderGradientLinear, colors, angle }))

-- | Create a conic (rotating) border effect
conicBorder :: Number -> Array GlowColor -> Number -> RenderEffect
conicBorder width colors rotationSpeed = EffectBorder (BorderConic (ConicBorder
  { width, colors, rotationSpeed, blurRadius: 8.0, mouseTracking: false, spotlightAngle: 90.0 }))

-- | Create an animated dash border effect
animatedDashBorder :: Number -> Number -> Number -> Number -> GlowColor -> RenderEffect
animatedDashBorder width dashLength gapLength speed color = EffectBorder (BorderAnimatedDash (AnimatedDashBorder
  { width, dashLength, gapLength, speed, direction: DashDirectionForward, color }))

-- | Create a glowing border effect
glowingBorder :: Number -> GlowColor -> GlowColor -> Number -> RenderEffect
glowingBorder width borderColor glowColor glowRadius = EffectBorder (BorderGlowing (GlowingBorder
  { width, borderColor, glowColor, glowRadius, glowIntensity: 0.5, animated: false, pulseSpeed: 0.0 }))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // material constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a glass effect
glassEffect :: GlowColor -> Number -> RenderEffect
glassEffect tint opacity = EffectMaterial (MaterialGlass (GlassEffect
  { tint, opacity, refraction: 0.1, reflection: 0.1, fresnel: true }))

-- | Create a frosted glass effect
frostedGlass :: Number -> Number -> RenderEffect
frostedGlass blur noiseAmount = EffectMaterial (MaterialFrosted (FrostedGlass
  { blur, saturation: 1.0, brightness: 1.0, noiseAmount
  , tint: { r: 255, g: 255, b: 255, a: 0.0 } }))

-- | Create a noise overlay effect
noiseOverlay :: NoiseType -> Number -> Number -> RenderEffect
noiseOverlay noiseType scale intensity = EffectMaterial (MaterialNoise (NoiseOverlay
  { noiseType, scale, intensity, animated: false, speed: 0.0 }))

-- | Create a grain effect
grainEffect :: Number -> Number -> RenderEffect
grainEffect amount size = EffectMaterial (MaterialGrain (GrainEffect
  { amount, size, colorful: false, animated: true }))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // temporal constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a motion blur effect
motionBlur :: Int -> Number -> RenderEffect
motionBlur samples shutterAngle = EffectTemporal (TemporalMotionBlur (MotionBlur
  { samples, shutterAngle }))

-- | Create an echo effect
echoEffect :: Int -> Number -> Number -> RenderEffect
echoEffect count delay decay = EffectTemporal (TemporalEcho (EchoEffect
  { count, delay, decay, operator: EchoBlend }))

-- | Create a time warp effect
timeWarp :: Number -> Number -> RenderEffect
timeWarp displacement noiseScale = EffectTemporal (TemporalTimeWarp (TimeWarp
  { displacement, noiseScale, animated: true }))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // particle constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a particle field effect
particleField :: Int -> GlowColor -> RenderEffect
particleField count color = EffectParticle (ParticleFieldEffect (ParticleField
  { count, sizeMin: 1.0, sizeMax: 3.0, color, speedMin: 10.0, speedMax: 30.0
  , direction: 0.0, spread: 360.0, lifetime: 5.0, fadeIn: 0.1, fadeOut: 0.2 }))

-- | Create a particle emitter effect
particleEmitter :: Number -> Number -> Number -> GlowColor -> RenderEffect
particleEmitter positionX positionY rate color = EffectParticle (ParticleEmitterEffect (ParticleEmitter
  { positionX, positionY, rate, sizeMin: 2.0, sizeMax: 4.0, color
  , velocity: 100.0, gravity: 50.0, spread: 45.0, lifetime: 2.0 }))
