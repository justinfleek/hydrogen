-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                               // hydrogen // gpu // diffusion
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Diffusion — GPU Compute Abstractions for Diffusion Model Inference
-- |
-- | ## Design Philosophy
-- |
-- | Diffusion models generate images through iterative denoising. This module
-- | provides **pure data** representing diffusion operations, compatible with:
-- | - Stable Diffusion (SD 1.5, 2.x, XL, 3.x)
-- | - Flux, Cascade, and other latent diffusion architectures
-- | - Video diffusion models (SVD, Mochi, etc.)
-- |
-- | ## RES4LYF Integration
-- |
-- | Types are designed for compatibility with res4lyf advanced sampling:
-- | - Scheduler types matching ComfyUI + res4lyf custom schedulers
-- | - Noise types: gaussian, brownian, fractal, pyramid variants
-- | - Noise modes: hard, soft, lorentzian for sigma scaling
-- | - Guide modes: flow, sync, lure for conditioning guidance
-- | - Implicit methods: rebound, retro-eta, bongmath, predictor-corrector
-- |
-- | ## Tensor-Native Model
-- |
-- | Diffusion kernels operate on latent tensors:
-- |
-- | ```
-- | DiffusionKernel :: LatentTensor -> Conditioning -> NoiseSchedule -> LatentTensor
-- | ```
-- |
-- | Standard shapes:
-- | - SD 1.5/2.x: [B, 4, H/8, W/8]
-- | - SDXL: [B, 4, H/8, W/8]
-- | - SD3/Flux: [B, 16, H/8, W/8]
-- | - Cascade: [B, 16, H/42, W/42] stage C, [B, 4, H/4, W/4] stage B
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Diffusion parameters are deterministic data:
-- | - Same scheduler + noise seed = same generation (always)
-- | - Kernels can be serialized, hashed, cached across agents
-- | - Multiple agents can share inference pipelines
-- | - GPU batches across agents efficiently
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from:
-- | - Hydrogen.GPU.Diffusion.Types — Core types and ADTs
-- | - Hydrogen.GPU.Diffusion.Kernels — Kernel newtypes and DiffusionConfig
-- | - Hydrogen.GPU.Diffusion.Region — Region diffusion state
-- | - Hydrogen.GPU.Diffusion.Config — Default config and presets
-- | - Hydrogen.GPU.Diffusion.Constructor — Smart constructors

module Hydrogen.GPU.Diffusion
  ( module Types
  , module Kernels
  , module Region
  , module Config
  , module Constructor
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.GPU.Diffusion.Types
  ( SchedulerType
      ( SchedulerNormal
      , SchedulerKarras
      , SchedulerExponential
      , SchedulerSGMUniform
      , SchedulerSimple
      , SchedulerDDIMUniform
      , SchedulerBeta
      , SchedulerLinearQuadratic
      , SchedulerBeta57
      , SchedulerPolyExponential
      , SchedulerVPSDE
      , SchedulerLCMSD
      , SchedulerLCMSDXL
      , SchedulerAYS
      , SchedulerGITS
      , SchedulerConstant
      )
  , NoiseType
      ( NoiseGaussian
      , NoiseBrownian
      , NoiseUniform
      , NoiseLaplacian
      , NoiseStudentT
      , NoisePerlin
      , NoiseWavelet
      , NoiseFractalBrown
      , NoiseFractalPink
      , NoiseFractalWhite
      , NoiseFractalBlue
      , NoiseFractalViolet
      , NoisePyramidBilinear
      , NoisePyramidBicubic
      , NoisePyramidNearest
      , NoiseHiresPyramidBilinear
      , NoiseHiresPyramidBicubic
      , NoiseSimplex
      , NoiseNone
      )
  , NoiseMode
      ( NoiseModeNone
      , NoiseModeHard
      , NoiseModeLorentzian
      , NoiseModeSoft
      , NoiseModeSoftLinear
      , NoiseModeSofter
      , NoiseModeEpsilon
      , NoiseModeSinusoidal
      , NoiseModeExp
      , NoiseModeVPSDE
      , NoiseModeER4
      , NoiseModeHardVar
      )
  , GuideMode
      ( GuideModeFlow
      , GuideModeSync
      , GuideModeLure
      , GuideModeData
      , GuideModeEpsilon
      , GuideModeInversion
      , GuideModePseudoimplicit
      , GuideModeFullyPseudoimplicit
      , GuideModeNone
      )
  , ImplicitType
      ( ImplicitRebound
      , ImplicitRetroEta
      , ImplicitBongmath
      , ImplicitPredictorCorrector
      )
  , LatentTensor
  , LatentShape
  , TensorDtype
      ( DtypeFloat16
      , DtypeFloat32
      , DtypeBFloat16
      )
  , TensorDevice
      ( DeviceCPU
      , DeviceCUDA
      , DeviceWebGPU
      )
  , Conditioning
      ( ConditioningText
      , ConditioningImage
      , ConditioningComposite
      , ConditioningNone
      )
  , TextConditioning
  , ImageConditioning
  , ImageConditionType
      ( ConditionControlNet
      , ConditionIPAdapter
      , ConditionReference
      , ConditionT2IAdapter
      )
  , NoiseSchedule
  , SigmaSchedule
  , DiffusionBlendMode
      ( BlendLinear
      , BlendSoftmax
      , BlendMultiply
      , BlendFeathered
      )
  , StepStrategy
      ( StrategyStandard
      , StrategySubstep
      , StrategyAncestral
      , StrategySDE
      )
  , SubstepConfig
  , SubstepMethod
      ( SubstepEuler
      , SubstepHeun
      , SubstepRK4
      , SubstepDPMSolver
      )
  ) as Types

import Hydrogen.GPU.Diffusion.Kernels
  ( DiffusionKernel
      ( KernelEncode
      , KernelDecode
      , KernelDenoise
      , KernelNoiseSchedule
      , KernelLatentBlend
      , KernelCFG
      , KernelSequence
      , KernelNoop
      )
  , EncodeKernel(EncodeKernel)
  , DecodeKernel(DecodeKernel)
  , DenoiseKernel(DenoiseKernel)
  , NoiseScheduleKernel(NoiseScheduleKernel)
  , LatentBlendKernel(LatentBlendKernel)
  , CFGKernel(CFGKernel)
  , DiffusionConfig
  ) as Kernels

import Hydrogen.GPU.Diffusion.Region
  ( RegionDiffusionState
  , DiffusionRegion
  ) as Region

import Hydrogen.GPU.Diffusion.Config
  ( defaultDiffusionConfig
  , eulerDiscretePreset
  , dpmPlusPlus2MPreset
  , flowMatchEulerPreset
  , res4lyfReboundPreset
  , res4lyfPredictorCorrectorPreset
  ) as Config

import Hydrogen.GPU.Diffusion.Constructor
  ( encodeKernel
  , decodeKernel
  , denoiseKernel
  , noiseScheduleKernel
  , latentBlendKernel
  , cfgKernel
  ) as Constructor
