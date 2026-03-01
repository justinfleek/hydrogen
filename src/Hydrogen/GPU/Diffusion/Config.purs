-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // gpu // diffusion // config
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Diffusion Config — Configuration and presets for diffusion inference
-- |
-- | ## Contents
-- |
-- | - defaultDiffusionConfig: SDXL-optimized defaults
-- | - Presets for common sampler configurations
-- |
-- | ## Presets
-- |
-- | - eulerDiscretePreset: Standard SDXL Euler
-- | - dpmPlusPlus2MPreset: DPM++ 2M with Karras
-- | - flowMatchEulerPreset: SD3/Flux flow matching
-- | - res4lyfReboundPreset: RES4LYF with rebound solver
-- | - res4lyfPredictorCorrectorPreset: High-fidelity PC sampling

module Hydrogen.GPU.Diffusion.Config
  ( -- * Configuration
    defaultDiffusionConfig
  
  -- * Presets
  , eulerDiscretePreset
  , dpmPlusPlus2MPreset
  , flowMatchEulerPreset
  , res4lyfReboundPreset
  , res4lyfPredictorCorrectorPreset
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Data.Maybe (Maybe(Nothing, Just))

import Hydrogen.GPU.Diffusion.Types
  ( SchedulerType
      ( SchedulerBeta57
      , SchedulerNormal
      , SchedulerKarras
      , SchedulerSimple
      )
  , NoiseType
      ( NoiseGaussian
      , NoiseBrownian
      )
  , NoiseMode
      ( NoiseModeHard
      , NoiseModeSoft
      )
  , GuideMode
      ( GuideModeEpsilon
      , GuideModeFlow
      , GuideModeSync
      )
  , ImplicitType
      ( ImplicitRebound
      , ImplicitPredictorCorrector
      )
  , TensorDtype(DtypeFloat16)
  , TensorDevice(DeviceCUDA)
  , StepStrategy
      ( StrategyStandard
      , StrategySubstep
      , StrategySDE
      )
  , SubstepMethod(SubstepDPMSolver)
  )

import Hydrogen.GPU.Diffusion.Kernels (DiffusionConfig)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // default config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default diffusion configuration (SDXL-optimized)
defaultDiffusionConfig :: DiffusionConfig
defaultDiffusionConfig =
  { scheduler: SchedulerBeta57
  , steps: 25
  , sigmaMin: 0.0292
  , sigmaMax: 14.6146
  , noiseType: NoiseGaussian
  , noiseMode: NoiseModeHard
  , seed: 42
  , cfgScale: 7.0
  , guideMode: GuideModeEpsilon
  , implicitType: Nothing
  , stepStrategy: StrategyStandard
  , latentShape: { batch: 1, channels: 4, height: 128, width: 128 }
  , dtype: DtypeFloat16
  , device: DeviceCUDA 0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Euler Discrete preset (standard SDXL)
eulerDiscretePreset :: DiffusionConfig
eulerDiscretePreset = defaultDiffusionConfig
  { scheduler = SchedulerNormal
  , steps = 25
  , cfgScale = 7.0
  , guideMode = GuideModeEpsilon
  }

-- | DPM++ 2M preset (high quality)
dpmPlusPlus2MPreset :: DiffusionConfig
dpmPlusPlus2MPreset = defaultDiffusionConfig
  { scheduler = SchedulerKarras
  , steps = 30
  , cfgScale = 7.5
  , guideMode = GuideModeEpsilon
  , stepStrategy = StrategySubstep { substeps: 2, method: SubstepDPMSolver }
  }

-- | Flow Match Euler preset (SD3/Flux)
flowMatchEulerPreset :: DiffusionConfig
flowMatchEulerPreset = defaultDiffusionConfig
  { scheduler = SchedulerSimple
  , steps = 20
  , cfgScale = 3.5
  , guideMode = GuideModeFlow
  , latentShape = { batch: 1, channels: 16, height: 128, width: 128 }
  }

-- | RES4LYF Beta57 preset with rebound implicit solver
res4lyfReboundPreset :: DiffusionConfig
res4lyfReboundPreset = defaultDiffusionConfig
  { scheduler = SchedulerBeta57
  , steps = 25
  , cfgScale = 7.0
  , guideMode = GuideModeEpsilon
  , implicitType = Just ImplicitRebound
  , noiseType = NoiseGaussian
  , noiseMode = NoiseModeHard
  }

-- | RES4LYF predictor-corrector preset for high fidelity
res4lyfPredictorCorrectorPreset :: DiffusionConfig
res4lyfPredictorCorrectorPreset = defaultDiffusionConfig
  { scheduler = SchedulerBeta57
  , steps = 30
  , cfgScale = 7.5
  , guideMode = GuideModeSync
  , implicitType = Just ImplicitPredictorCorrector
  , noiseType = NoiseBrownian
  , noiseMode = NoiseModeSoft
  , stepStrategy = StrategySDE 
      { noiseTypeStep: NoiseGaussian
      , noiseTypeSubstep: NoiseBrownian
      , noiseModeStep: NoiseModeHard
      , noiseModeSubstep: NoiseModeSoft
      }
  }
