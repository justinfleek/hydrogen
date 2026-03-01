-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // gpu // compute-kernel
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ComputeKernel — GPU Compute Abstractions for Effect Processing
-- |
-- | ## Design Philosophy
-- |
-- | Hyper-responsive effects require GPU compute for:
-- | - Real-time blur (Gaussian, radial, directional)
-- | - Glow with bloom and color cycling
-- | - Particle physics simulation
-- | - Noise generation (Perlin, Simplex, FBM)
-- | - Diffusion model inference (latent space fills)
-- |
-- | This module defines **pure data** representing compute operations.
-- | The interpreter converts these to WebGPU compute shaders.
-- |
-- | ## Tensor-Native Model
-- |
-- | Every compute kernel operates on tensors:
-- |
-- | ```
-- | ComputeKernel :: InputTensors -> OutputTensor
-- | ```
-- |
-- | Where tensors have shape `[N, C, H, W]` (batch, channels, height, width).
-- | This matches both GPU memory layout and ML model expectations.
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Kernels are deterministic data:
-- | - Same kernel + same input = same output (always)
-- | - Kernels can be serialized, hashed, cached
-- | - Multiple agents can share kernel definitions
-- | - GPU batches kernels across agents efficiently
-- |
-- | ## WebGPU Mapping
-- |
-- | Each kernel variant maps to a compute shader:
-- |
-- | | Kernel   | Workgroup | Dispatch        |
-- | |----------|-----------|-----------------|
-- | | Blur     | 16x16x1   | (W/16, H/16, 1) |
-- | | Glow     | 16x16x1   | (W/16, H/16, 1) |
-- | | Noise    | 8x8x8     | (W/8, H/8, C/8) |
-- | | Particle | 256x1x1   | (N/256, 1, 1)   |
-- |
-- | ## Module Structure
-- |
-- | This is the leader module that re-exports all submodules:
-- | - Core: Input/output, config, conditions
-- | - Types: ComputeKernel sum type
-- | - Blur: Gaussian, directional, radial, box
-- | - Glow: Bloom, outer, inner
-- | - Noise: Perlin, simplex, FBM, Worley
-- | - Particle: Physics, emit, sort
-- | - Color: Grading, tone mapping, color space
-- | - Distortion: Displacement, warp, ripple
-- | - Composite: Blend, mask, alpha
-- | - Operations: Construction, dispatch, composition, presets

module Hydrogen.GPU.ComputeKernel
  ( -- * Core Types
    module Hydrogen.GPU.ComputeKernel.Core
  
  -- * ComputeKernel Type
  , module Hydrogen.GPU.ComputeKernel.Types
  
  -- * Blur Kernels
  , module Hydrogen.GPU.ComputeKernel.Blur
  
  -- * Glow Kernels
  , module Hydrogen.GPU.ComputeKernel.Glow
  
  -- * Noise Kernels
  , module Hydrogen.GPU.ComputeKernel.Noise
  
  -- * Particle Kernels
  , module Hydrogen.GPU.ComputeKernel.Particle
  
  -- * Color Kernels
  , module Hydrogen.GPU.ComputeKernel.Color
  
  -- * Distortion Kernels
  , module Hydrogen.GPU.ComputeKernel.Distortion
  
  -- * Composite Kernels
  , module Hydrogen.GPU.ComputeKernel.Composite
  
  -- * Operations
  , module Hydrogen.GPU.ComputeKernel.Operations
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.GPU.ComputeKernel.Core
  ( WorkgroupSize
  , DispatchSize
  , KernelInput(InputTexture, InputBuffer, InputUniform, InputPrevious, InputConstant)
  , KernelOutput(OutputTexture, OutputBuffer, OutputNext, OutputScreen)
  , KernelConfig
  , KernelCondition(ConditionQuality, ConditionSize, ConditionPerformance, ConditionAlways)
  , QualityLevel(QualityLow, QualityMedium, QualityHigh, QualityUltra)
  , SizeThreshold
  , defaultConfig
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

import Hydrogen.GPU.ComputeKernel.Blur
  ( BlurKernel(BlurGaussian, BlurDirectional, BlurRadial, BlurBox)
  , BlurQuality(BlurQualityLow, BlurQualityMedium, BlurQualityHigh)
  , RadialBlurType(RadialTypeSpin, RadialTypeZoom)
  , GaussianBlurKernel(GaussianBlurKernel)
  , DirectionalBlurKernel(DirectionalBlurKernel)
  , RadialBlurKernel(RadialBlurKernel)
  , BoxBlurKernel(BoxBlurKernel)
  )

import Hydrogen.GPU.ComputeKernel.Glow
  ( GlowKernel(GlowBloom, GlowOuter, GlowInner)
  , GlowTint
  , GlowFalloff(FalloffLinear, FalloffQuadratic, FalloffExponential, FalloffGaussian)
  , BloomKernel(BloomKernel)
  , OuterGlowKernel(OuterGlowKernel)
  , InnerGlowKernel(InnerGlowKernel)
  )

import Hydrogen.GPU.ComputeKernel.Noise
  ( NoiseKernel(NoisePerlin, NoiseSimplex, NoiseFBM, NoiseWorley)
  , WorleyDistance(WorleyEuclidean, WorleyManhattan, WorleyChebyshev)
  , PerlinNoiseKernel(PerlinNoiseKernel)
  , SimplexNoiseKernel(SimplexNoiseKernel)
  , FBMNoiseKernel(FBMNoiseKernel)
  , WorleyNoiseKernel(WorleyNoiseKernel)
  )

import Hydrogen.GPU.ComputeKernel.Particle
  ( ParticleKernel(ParticlePhysics, ParticleEmit, ParticleSort)
  , ParticleBounds(BoundsNone, BoundsWrap, BoundsBounce, BoundsKill)
  , ParticleForce
  , SortAxis(SortAxisZ, SortAxisDistance)
  , ParticlePhysicsKernel(ParticlePhysicsKernel)
  , ParticleEmitKernel(ParticleEmitKernel)
  , ParticleSortKernel(ParticleSortKernel)
  )

import Hydrogen.GPU.ComputeKernel.Color
  ( ColorKernel(ColorGrading, ColorToneMapping, ColorSpace)
  , ColorAdjust
  , ToneMappingAlgorithm(TonemapReinhard, TonemapACES, TonemapHable, TonemapFilmic)
  , ColorSpaceType(ColorSpaceSRGB, ColorSpaceLinear, ColorSpaceP3, ColorSpaceRec2020, ColorSpaceOKLab, ColorSpaceOKLCH)
  , ColorGradingKernel(ColorGradingKernel)
  , ToneMappingKernel(ToneMappingKernel)
  , ColorSpaceKernel(ColorSpaceKernel)
  )

import Hydrogen.GPU.ComputeKernel.Distortion
  ( DistortionKernel(DistortDisplacement, DistortWarp, DistortRipple)
  , DisplacementChannel(DisplaceRed, DisplaceGreen, DisplaceBlue, DisplaceAlpha, DisplaceLuminance)
  , WarpType(WarpSphere, WarpPinch, WarpTwirl, WarpWave)
  , DisplacementKernel(DisplacementKernel)
  , WarpKernel(WarpKernel)
  , RippleKernel(RippleKernel)
  )

import Hydrogen.GPU.ComputeKernel.Composite
  ( CompositeKernel(CompositeBlend, CompositeMask, CompositeAlpha)
  , BlendKernelMode
      ( KernelBlendNormal
      , KernelBlendAdd
      , KernelBlendMultiply
      , KernelBlendScreen
      , KernelBlendOverlay
      , KernelBlendSoftLight
      , KernelBlendHardLight
      , KernelBlendDifference
      )
  , MaskChannel(MaskRed, MaskGreen, MaskBlue, MaskAlpha, MaskLuminance)
  , AlphaOperation(AlphaMultiply, AlphaThreshold, AlphaInvert, AlphaRemapRange)
  , BlendKernel(BlendKernel)
  , MaskKernel(MaskKernel)
  , AlphaKernel(AlphaKernel)
  )

import Hydrogen.GPU.ComputeKernel.Operations
  ( gaussianBlurKernel
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
  , computeWorkgroupSize
  , computeDispatchSize
  , estimateKernelCost
  , sequenceKernels
  , parallelKernels
  , conditionalKernel
  , standardGaussian
  , fastGaussian
  , qualityGaussian
  , standardBloom
  , softBloom
  , intenseBloom
  , standardNoise
  , animatedNoise
  )
