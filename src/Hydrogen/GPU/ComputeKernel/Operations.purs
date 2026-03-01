-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // gpu // compute-kernel/operations
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ComputeKernel/Operations — Kernel Construction and Composition
-- |
-- | This module provides:
-- | - Constructor functions for all kernel types
-- | - Dispatch size calculations
-- | - Cost estimation
-- | - Composition operators (sequence, parallel, conditional)
-- | - Presets for common configurations

module Hydrogen.GPU.ComputeKernel.Operations
  ( -- * Kernel Construction
    gaussianBlurKernel
  , directionalBlurKernel
  , radialBlurKernel
  , boxBlurKernel
  , bloomKernel
  , outerGlowKernel
  , innerGlowKernel
  , perlinNoiseKernel
  , simplexNoiseKernel
  , fbmNoiseKernel
  , worleyNoiseKernel
  , particlePhysicsKernel
  , particleEmitKernel
  , colorGradingKernel
  , toneMappingKernel
  , displacementKernel
  , warpKernel
  , blendKernel
  , maskKernel
  
  -- * Kernel Dispatch
  , computeWorkgroupSize
  , computeDispatchSize
  , estimateKernelCost
  
  -- * Kernel Composition
  , sequenceKernels
  , parallelKernels
  , conditionalKernel
  
  -- * Presets
  , standardGaussian
  , fastGaussian
  , qualityGaussian
  , standardBloom
  , softBloom
  , intenseBloom
  , standardNoise
  , animatedNoise
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (-)
  , (+)
  , (*)
  , (/)
  , (>)
  , ($)
  , map
  )

import Data.Array as Array
import Data.Int as Int
import Data.Maybe (Maybe(Nothing, Just))

import Hydrogen.GPU.ComputeKernel.Core
  ( KernelConfig
  , KernelCondition
  , KernelInput
  , WorkgroupSize
  , DispatchSize
  , defaultConfig
  )

import Hydrogen.GPU.ComputeKernel.Blur
  ( BlurKernel(BlurGaussian, BlurDirectional, BlurRadial, BlurBox)
  , GaussianBlurKernel(GaussianBlurKernel)
  , DirectionalBlurKernel(DirectionalBlurKernel)
  , RadialBlurKernel(RadialBlurKernel)
  , RadialBlurType(RadialTypeSpin)
  , BoxBlurKernel(BoxBlurKernel)
  )

import Hydrogen.GPU.ComputeKernel.Glow
  ( GlowKernel(GlowBloom, GlowOuter, GlowInner)
  , GlowTint
  , GlowFalloff(FalloffGaussian)
  , BloomKernel(BloomKernel)
  , OuterGlowKernel(OuterGlowKernel)
  , InnerGlowKernel(InnerGlowKernel)
  )

import Hydrogen.GPU.ComputeKernel.Noise
  ( NoiseKernel(NoisePerlin, NoiseSimplex, NoiseFBM, NoiseWorley)
  , WorleyDistance(WorleyEuclidean)
  , PerlinNoiseKernel(PerlinNoiseKernel)
  , SimplexNoiseKernel(SimplexNoiseKernel)
  , FBMNoiseKernel(FBMNoiseKernel)
  , WorleyNoiseKernel(WorleyNoiseKernel)
  )

import Hydrogen.GPU.ComputeKernel.Particle
  ( ParticleKernel(ParticlePhysics, ParticleEmit)
  , ParticleBounds(BoundsWrap)
  , ParticlePhysicsKernel(ParticlePhysicsKernel)
  , ParticleEmitKernel(ParticleEmitKernel)
  )

import Hydrogen.GPU.ComputeKernel.Color
  ( ColorKernel(ColorGrading, ColorToneMapping)
  , ToneMappingAlgorithm
  , ColorGradingKernel(ColorGradingKernel)
  , ToneMappingKernel(ToneMappingKernel)
  )

import Hydrogen.GPU.ComputeKernel.Distortion
  ( DistortionKernel(DistortDisplacement, DistortWarp)
  , DisplacementChannel(DisplaceLuminance)
  , WarpType
  , DisplacementKernel(DisplacementKernel)
  , WarpKernel(WarpKernel)
  )

import Hydrogen.GPU.ComputeKernel.Composite
  ( CompositeKernel(CompositeBlend, CompositeMask)
  , BlendKernelMode
  , MaskChannel
  , BlendKernel(BlendKernel)
  , MaskKernel(MaskKernel)
  )

import Hydrogen.GPU.ComputeKernel.Types
  ( ComputeKernel
      ( KernelBlur
      , KernelGlow
      , KernelNoise
      , KernelParticle
      , KernelColor
      , KernelDistortion
      , KernelComposite
      , KernelSequence
      , KernelParallel
      , KernelConditional
      , KernelNoop
      )
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // blur kernel constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a Gaussian blur kernel
gaussianBlurKernel :: Int -> Number -> Int -> Int -> Int -> ComputeKernel
gaussianBlurKernel radius sigma passes width height =
  KernelBlur $ BlurGaussian $ GaussianBlurKernel
    { radius, sigma, passes, config: defaultConfig width height }

-- | Create a directional (motion) blur kernel
directionalBlurKernel :: Number -> Int -> Int -> Int -> Int -> ComputeKernel
directionalBlurKernel angle distance samples width height =
  KernelBlur $ BlurDirectional $ DirectionalBlurKernel
    { angle, distance, samples, config: defaultConfig width height }

-- | Create a radial blur kernel
radialBlurKernel :: Number -> Number -> Number -> Int -> Int -> Int -> ComputeKernel
radialBlurKernel centerX centerY amount samples width height =
  KernelBlur $ BlurRadial $ RadialBlurKernel
    { centerX, centerY, amount, blurType: RadialTypeSpin
    , samples, config: defaultConfig width height }

-- | Create a box blur kernel
boxBlurKernel :: Int -> Int -> Int -> Int -> ComputeKernel
boxBlurKernel radius iterations width height =
  KernelBlur $ BlurBox $ BoxBlurKernel
    { radius, iterations, config: defaultConfig width height }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // glow kernel constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a bloom kernel
bloomKernel :: Number -> Number -> Int -> Int -> Int -> Int -> ComputeKernel
bloomKernel threshold intensity radius passes width height =
  KernelGlow $ GlowBloom $ BloomKernel
    { threshold, intensity, radius, passes
    , tint: { r: 1.0, g: 1.0, b: 1.0, enabled: false }
    , config: defaultConfig width height }

-- | Create an outer glow kernel
outerGlowKernel :: GlowTint -> Int -> Number -> Int -> Int -> ComputeKernel
outerGlowKernel color radius intensity width height =
  KernelGlow $ GlowOuter $ OuterGlowKernel
    { color, radius, intensity, falloff: FalloffGaussian
    , config: defaultConfig width height }

-- | Create an inner glow kernel
innerGlowKernel :: GlowTint -> Int -> Number -> Number -> Int -> Int -> ComputeKernel
innerGlowKernel color radius intensity choke width height =
  KernelGlow $ GlowInner $ InnerGlowKernel
    { color, radius, intensity, choke, config: defaultConfig width height }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // noise kernel constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a Perlin noise kernel
perlinNoiseKernel :: Number -> Int -> Int -> Int -> Int -> ComputeKernel
perlinNoiseKernel scale seed octaves width height =
  KernelNoise $ NoisePerlin $ PerlinNoiseKernel
    { scale, seed, octaves, persistence: 0.5, lacunarity: 2.0
    , time: 0.0, config: defaultConfig width height }

-- | Create a Simplex noise kernel
simplexNoiseKernel :: Number -> Int -> Int -> Int -> ComputeKernel
simplexNoiseKernel scale seed width height =
  KernelNoise $ NoiseSimplex $ SimplexNoiseKernel
    { scale, seed, time: 0.0, config: defaultConfig width height }

-- | Create an FBM noise kernel
fbmNoiseKernel :: Number -> Int -> Int -> Number -> Number -> Int -> Int -> ComputeKernel
fbmNoiseKernel scale seed octaves persistence lacunarity width height =
  KernelNoise $ NoiseFBM $ FBMNoiseKernel
    { scale, seed, octaves, persistence, lacunarity
    , time: 0.0, turbulent: false, config: defaultConfig width height }

-- | Create a Worley noise kernel
worleyNoiseKernel :: Number -> Int -> Int -> Int -> Int -> ComputeKernel
worleyNoiseKernel scale seed cellCount width height =
  KernelNoise $ NoiseWorley $ WorleyNoiseKernel
    { scale, seed, cellCount, distanceType: WorleyEuclidean
    , time: 0.0, config: defaultConfig width height }

-- ═════════════════════════════════════════════════════════════════════════════
--                                               // particle kernel constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a particle physics kernel
particlePhysicsKernel :: Int -> Number -> Number -> Number -> Int -> Int -> ComputeKernel
particlePhysicsKernel particleCount deltaTime gravity damping width height =
  KernelParticle $ ParticlePhysics $ ParticlePhysicsKernel
    { particleCount, deltaTime, gravity, damping, bounds: BoundsWrap
    , forces: [], config: defaultConfig width height }

-- | Create a particle emit kernel
particleEmitKernel :: Int -> Number -> Number -> Number -> Number -> Number -> Int -> Int -> Int -> ComputeKernel
particleEmitKernel emitCount positionX positionY spread velocity lifetime seed width height =
  KernelParticle $ ParticleEmit $ ParticleEmitKernel
    { emitCount, positionX, positionY, spread, velocity
    , velocityVariance: 0.1, lifetime, lifetimeVariance: 0.2
    , seed, config: defaultConfig width height }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // color kernel constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a color grading kernel
colorGradingKernel :: Number -> Number -> Number -> Int -> Int -> ComputeKernel
colorGradingKernel exposure contrast saturation width height =
  KernelColor $ ColorGrading $ ColorGradingKernel
    { exposure, contrast, saturation, temperature: 0.0, tint: 0.0
    , shadows: { r: 0.0, g: 0.0, b: 0.0 }
    , midtones: { r: 0.0, g: 0.0, b: 0.0 }
    , highlights: { r: 0.0, g: 0.0, b: 0.0 }
    , config: defaultConfig width height }

-- | Create a tone mapping kernel
toneMappingKernel :: ToneMappingAlgorithm -> Number -> Int -> Int -> ComputeKernel
toneMappingKernel algorithm whitePoint width height =
  KernelColor $ ColorToneMapping $ ToneMappingKernel
    { algorithm, whitePoint, config: defaultConfig width height }

-- ═════════════════════════════════════════════════════════════════════════════
--                                             // distortion kernel constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a displacement kernel
displacementKernel :: KernelInput -> Number -> Number -> Int -> Int -> ComputeKernel
displacementKernel mapInput scaleX scaleY width height =
  KernelDistortion $ DistortDisplacement $ DisplacementKernel
    { mapInput, scaleX, scaleY, channel: DisplaceLuminance
    , config: defaultConfig width height }

-- | Create a warp kernel
warpKernel :: WarpType -> Number -> Number -> Number -> Int -> Int -> ComputeKernel
warpKernel warpType strength centerX centerY width height =
  KernelDistortion $ DistortWarp $ WarpKernel
    { warpType, strength, centerX, centerY
    , config: defaultConfig width height }

-- ═════════════════════════════════════════════════════════════════════════════
--                                              // composite kernel constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a blend kernel
blendKernel :: KernelInput -> KernelInput -> BlendKernelMode -> Number -> Int -> Int -> ComputeKernel
blendKernel layerA layerB mode opacity width height =
  KernelComposite $ CompositeBlend $ BlendKernel
    { layerA, layerB, mode, opacity, config: defaultConfig width height }

-- | Create a mask kernel
maskKernel :: KernelInput -> KernelInput -> MaskChannel -> Boolean -> Int -> Int -> ComputeKernel
maskKernel source mask' channel invert width height =
  KernelComposite $ CompositeMask $ MaskKernel
    { source, mask: mask', channel, invert, config: defaultConfig width height }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // kernel dispatch
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute appropriate workgroup size for kernel type
computeWorkgroupSize :: ComputeKernel -> WorkgroupSize
computeWorkgroupSize = case _ of
  KernelBlur _ -> { x: 16, y: 16, z: 1 }         -- 2D image processing
  KernelGlow _ -> { x: 16, y: 16, z: 1 }
  KernelNoise _ -> { x: 8, y: 8, z: 8 }          -- 3D noise (x, y, octave)
  KernelParticle _ -> { x: 256, y: 1, z: 1 }     -- 1D particle array
  KernelColor _ -> { x: 16, y: 16, z: 1 }
  KernelDistortion _ -> { x: 16, y: 16, z: 1 }
  KernelComposite _ -> { x: 16, y: 16, z: 1 }
  KernelSequence _ -> { x: 16, y: 16, z: 1 }     -- Default for sequences
  KernelParallel _ -> { x: 16, y: 16, z: 1 }
  KernelConditional c -> computeWorkgroupSize c.thenKernel
  KernelNoop -> { x: 1, y: 1, z: 1 }

-- | Compute dispatch size from kernel config
computeDispatchSize :: KernelConfig -> DispatchSize
computeDispatchSize config =
  { x: divCeil config.width config.workgroupSize.x
  , y: divCeil config.height config.workgroupSize.y
  , z: divCeil config.channels config.workgroupSize.z
  }
  where
    divCeil a b = (a + b - 1) / b

-- | Estimate kernel cost in milliseconds (rough)
estimateKernelCost :: ComputeKernel -> Number
estimateKernelCost = case _ of
  KernelBlur (BlurGaussian (GaussianBlurKernel k)) -> 
    Int.toNumber k.radius * Int.toNumber k.passes * 0.01
  KernelBlur (BlurDirectional (DirectionalBlurKernel k)) ->
    Int.toNumber k.samples * 0.005
  KernelBlur (BlurRadial (RadialBlurKernel k)) ->
    Int.toNumber k.samples * 0.008
  KernelBlur (BlurBox (BoxBlurKernel k)) ->
    Int.toNumber k.iterations * 0.003
  KernelGlow (GlowBloom (BloomKernel k)) ->
    Int.toNumber k.passes * Int.toNumber k.radius * 0.015
  KernelGlow _ -> 0.5
  KernelNoise (NoiseFBM (FBMNoiseKernel k)) ->
    Int.toNumber k.octaves * 0.1
  KernelNoise _ -> 0.2
  KernelParticle (ParticlePhysics (ParticlePhysicsKernel k)) ->
    Int.toNumber k.particleCount * 0.00001
  KernelParticle _ -> 0.1
  KernelColor _ -> 0.1
  KernelDistortion _ -> 0.2
  KernelComposite _ -> 0.1
  KernelSequence kernels -> foldlSum (map estimateKernelCost kernels)
  KernelParallel kernels -> foldlMax (map estimateKernelCost kernels)
  KernelConditional c -> estimateKernelCost c.thenKernel
  KernelNoop -> 0.0
  where
    foldlSum arr = foldlArr (\acc x -> acc + x) 0.0 arr
    foldlMax arr = foldlArr (\acc x -> if x > acc then x else acc) 0.0 arr

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // kernel composition
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sequence kernels (execute in order)
sequenceKernels :: Array ComputeKernel -> ComputeKernel
sequenceKernels = KernelSequence

-- | Parallel kernels (execute simultaneously to different outputs)
parallelKernels :: Array ComputeKernel -> ComputeKernel
parallelKernels = KernelParallel

-- | Conditional kernel execution
conditionalKernel :: KernelCondition -> ComputeKernel -> Maybe ComputeKernel -> ComputeKernel
conditionalKernel condition thenKernel elseKernel = KernelConditional
  { condition, thenKernel, elseKernel }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Standard Gaussian blur preset (balanced quality/performance)
standardGaussian :: Int -> Int -> ComputeKernel
standardGaussian = gaussianBlurKernel 8 4.0 2

-- | Fast Gaussian blur preset (performance priority)
fastGaussian :: Int -> Int -> ComputeKernel
fastGaussian = boxBlurKernel 8 3

-- | Quality Gaussian blur preset (quality priority)
qualityGaussian :: Int -> Int -> ComputeKernel
qualityGaussian = gaussianBlurKernel 16 8.0 4

-- | Standard bloom preset
standardBloom :: Int -> Int -> ComputeKernel
standardBloom = bloomKernel 0.8 1.0 8 3

-- | Soft bloom preset (subtle)
softBloom :: Int -> Int -> ComputeKernel
softBloom = bloomKernel 0.9 0.5 12 2

-- | Intense bloom preset (dramatic)
intenseBloom :: Int -> Int -> ComputeKernel
intenseBloom = bloomKernel 0.6 1.5 16 4

-- | Standard noise preset
standardNoise :: Int -> Int -> ComputeKernel
standardNoise = fbmNoiseKernel 1.0 42 4 0.5 2.0

-- | Animated noise preset
animatedNoise :: Number -> Int -> Int -> ComputeKernel
animatedNoise time width height = KernelNoise $ NoiseFBM $ FBMNoiseKernel
  { scale: 1.0, seed: 42, octaves: 4, persistence: 0.5, lacunarity: 2.0
  , time, turbulent: false, config: defaultConfig width height }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Array fold helper (tail-recursive)
foldlArr :: forall a b. (b -> a -> b) -> b -> Array a -> b
foldlArr f init arr = case Array.uncons arr of
  Nothing -> init
  Just { head, tail } -> foldlArr f (f init head) tail
