-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // gpu // diffusion // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Diffusion Types — Core ADTs for diffusion model inference
-- |
-- | ## Contents
-- |
-- | - Scheduler types (ComfyUI + RES4LYF schedulers)
-- | - Noise types and modes
-- | - Guidance types and implicit solvers
-- | - Tensor and conditioning types
-- | - Step strategies and blend modes
-- |
-- | ## At Billion-Agent Scale
-- |
-- | These types are bounded enums with deterministic Show instances.
-- | Same type value = same serialized form = same UUID5.

module Hydrogen.GPU.Diffusion.Types
  ( -- * Scheduler Types
    SchedulerType
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
  
  -- * Noise Types
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
  
  -- * Guidance Types
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
  
  -- * Tensor Types
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
  
  -- * Conditioning Types
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
  
  -- * Blend Mode
  , DiffusionBlendMode
      ( BlendLinear
      , BlendSoftmax
      , BlendMultiply
      , BlendFeathered
      )
  
  -- * Step Strategy
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
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Data.Array as Array
import Data.Maybe (Maybe)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // scheduler types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scheduler type for noise schedule generation
-- |
-- | Comprehensive coverage of diffusion schedulers:
-- | - ComfyUI built-in schedulers (normal, karras, exponential, etc.)
-- | - RES4LYF custom schedulers (beta57, linear_quadratic)
-- | - Flow matching schedulers for SD3/Flux (simple, sgm_uniform)
-- |
-- | Each scheduler produces a sigma schedule that controls the denoising process.
-- | The schedule determines how quickly noise is removed at each step.
data SchedulerType
  = SchedulerNormal             -- ^ Standard linear schedule
  | SchedulerKarras             -- ^ Karras et al. schedule (smooth transitions)
  | SchedulerExponential        -- ^ Exponential decay schedule
  | SchedulerSGMUniform         -- ^ SGM uniform (flow matching)
  | SchedulerSimple             -- ^ Simple linear (flow matching)
  | SchedulerDDIMUniform        -- ^ DDIM uniform timestep spacing
  | SchedulerBeta               -- ^ Beta schedule (original DDPM)
  | SchedulerLinearQuadratic    -- ^ Linear quadratic interpolation
  | SchedulerBeta57             -- ^ RES4LYF beta57 schedule (recommended default)
  | SchedulerPolyExponential    -- ^ Polyexponential schedule
  | SchedulerVPSDE              -- ^ Variance Preserving SDE schedule
  | SchedulerLCMSD              -- ^ LCM-specific schedule for SD
  | SchedulerLCMSDXL            -- ^ LCM-specific schedule for SDXL
  | SchedulerAYS                -- ^ Align Your Steps schedule
  | SchedulerGITS               -- ^ GITS scheduler
  | SchedulerConstant           -- ^ Constant sigma (single step)

derive instance eqSchedulerType :: Eq SchedulerType

instance showSchedulerType :: Show SchedulerType where
  show SchedulerNormal = "normal"
  show SchedulerKarras = "karras"
  show SchedulerExponential = "exponential"
  show SchedulerSGMUniform = "sgm_uniform"
  show SchedulerSimple = "simple"
  show SchedulerDDIMUniform = "ddim_uniform"
  show SchedulerBeta = "beta"
  show SchedulerLinearQuadratic = "linear_quadratic"
  show SchedulerBeta57 = "beta57"
  show SchedulerPolyExponential = "polyexponential"
  show SchedulerVPSDE = "vpsde"
  show SchedulerLCMSD = "lcm_sd"
  show SchedulerLCMSDXL = "lcm_sdxl"
  show SchedulerAYS = "ays"
  show SchedulerGITS = "gits"
  show SchedulerConstant = "constant"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // noise types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Noise generator type for SDE sampling
-- |
-- | Comprehensive noise types from res4lyf:
-- | - Standard: gaussian, brownian, uniform
-- | - Statistical: laplacian, studentt
-- | - Fractal: fractal with configurable alpha (brown, pink, white, blue, violet)
-- | - Pyramid: multi-scale pyramid noise for coherent structures
-- | - Perlin: gradient noise for natural patterns
data NoiseType
  = NoiseGaussian              -- ^ Standard Gaussian noise (default)
  | NoiseBrownian              -- ^ Brownian tree noise (SDE-native)
  | NoiseUniform               -- ^ Uniform distribution noise
  | NoiseLaplacian             -- ^ Laplacian distribution (heavier tails)
  | NoiseStudentT              -- ^ Student-t distribution (configurable tails)
  | NoisePerlin                -- ^ Perlin gradient noise
  | NoiseWavelet               -- ^ Wavelet-based noise
  | NoiseFractalBrown          -- ^ Fractal noise alpha=2.0 (brownian)
  | NoiseFractalPink           -- ^ Fractal noise alpha=1.0 (pink/1/f)
  | NoiseFractalWhite          -- ^ Fractal noise alpha=0.0 (white)
  | NoiseFractalBlue           -- ^ Fractal noise alpha=-1.0 (blue)
  | NoiseFractalViolet         -- ^ Fractal noise alpha=-2.0 (violet)
  | NoisePyramidBilinear       -- ^ Pyramid noise with bilinear interpolation
  | NoisePyramidBicubic        -- ^ Pyramid noise with bicubic interpolation
  | NoisePyramidNearest        -- ^ Pyramid noise with nearest-neighbor
  | NoiseHiresPyramidBilinear  -- ^ High-res pyramid bilinear
  | NoiseHiresPyramidBicubic   -- ^ High-res pyramid bicubic
  | NoiseSimplex               -- ^ OpenSimplex noise (if available)
  | NoiseNone                  -- ^ No noise (for testing/debugging)

derive instance eqNoiseType :: Eq NoiseType

instance showNoiseType :: Show NoiseType where
  show NoiseGaussian = "gaussian"
  show NoiseBrownian = "brownian"
  show NoiseUniform = "uniform"
  show NoiseLaplacian = "laplacian"
  show NoiseStudentT = "studentt"
  show NoisePerlin = "perlin"
  show NoiseWavelet = "wavelet"
  show NoiseFractalBrown = "brown"
  show NoiseFractalPink = "pink"
  show NoiseFractalWhite = "white"
  show NoiseFractalBlue = "blue"
  show NoiseFractalViolet = "violet"
  show NoisePyramidBilinear = "pyramid-bilinear"
  show NoisePyramidBicubic = "pyramid-bicubic"
  show NoisePyramidNearest = "pyramid-nearest"
  show NoiseHiresPyramidBilinear = "hires-pyramid-bilinear"
  show NoiseHiresPyramidBicubic = "hires-pyramid-bicubic"
  show NoiseSimplex = "simplex"
  show NoiseNone = "none"

-- | Noise mode — controls how noise scales with sigma schedule
-- |
-- | From res4lyf NOISE_MODE_NAMES:
-- | - Hard modes affect early steps most strongly
-- | - Soft modes have gradual falloff
-- | - Sinusoidal affects middle steps
data NoiseMode
  = NoiseModeNone         -- ^ No scaling
  | NoiseModeHard         -- ^ Hard scaling (aggressive, default)
  | NoiseModeLorentzian   -- ^ Lorentzian falloff curve
  | NoiseModeSoft         -- ^ Soft scaling
  | NoiseModeSoftLinear   -- ^ Soft with linear component
  | NoiseModeSofter       -- ^ Even softer scaling
  | NoiseModeEpsilon      -- ^ Epsilon-based scaling
  | NoiseModeSinusoidal   -- ^ Sinusoidal (affects middle steps)
  | NoiseModeExp          -- ^ Exponential scaling
  | NoiseModeVPSDE        -- ^ VP-SDE native scaling
  | NoiseModeER4          -- ^ ER4 scaling mode
  | NoiseModeHardVar      -- ^ Hard with variance correction

derive instance eqNoiseMode :: Eq NoiseMode

instance showNoiseMode :: Show NoiseMode where
  show NoiseModeNone = "none"
  show NoiseModeHard = "hard"
  show NoiseModeLorentzian = "lorentzian"
  show NoiseModeSoft = "soft"
  show NoiseModeSoftLinear = "soft-linear"
  show NoiseModeSofter = "softer"
  show NoiseModeEpsilon = "eps"
  show NoiseModeSinusoidal = "sinusoidal"
  show NoiseModeExp = "exp"
  show NoiseModeVPSDE = "vpsde"
  show NoiseModeER4 = "er4"
  show NoiseModeHardVar = "hard_var"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // guidance types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Guide mode for conditioning guidance
-- |
-- | From res4lyf GUIDE_MODE_NAMES_BETA_SIMPLE:
-- | Controls how the model prediction is interpreted and guided toward conditioning.
data GuideMode
  = GuideModeFlow              -- ^ Flow matching guidance (SD3/Flux native)
  | GuideModeSync              -- ^ Synchronization guidance
  | GuideModeLure              -- ^ Lure-based guidance
  | GuideModeData              -- ^ Data prediction guidance
  | GuideModeEpsilon           -- ^ Epsilon (noise) prediction guidance
  | GuideModeInversion         -- ^ Inversion guidance for editing
  | GuideModePseudoimplicit    -- ^ Pseudo-implicit guidance
  | GuideModeFullyPseudoimplicit -- ^ Fully pseudo-implicit guidance
  | GuideModeNone              -- ^ No guidance modification

derive instance eqGuideMode :: Eq GuideMode

instance showGuideMode :: Show GuideMode where
  show GuideModeFlow = "flow"
  show GuideModeSync = "sync"
  show GuideModeLure = "lure"
  show GuideModeData = "data"
  show GuideModeEpsilon = "epsilon"
  show GuideModeInversion = "inversion"
  show GuideModePseudoimplicit = "pseudoimplicit"
  show GuideModeFullyPseudoimplicit = "fully_pseudoimplicit"
  show GuideModeNone = "none"

-- | Implicit sampling type
-- |
-- | From res4lyf IMPLICIT_TYPE_NAMES:
-- | Controls the implicit solver behavior for improved sampling quality.
data ImplicitType
  = ImplicitRebound            -- ^ Rebound implicit solver
  | ImplicitRetroEta           -- ^ Retro-eta implicit solver
  | ImplicitBongmath           -- ^ Bongmath implicit solver
  | ImplicitPredictorCorrector -- ^ Predictor-corrector method

derive instance eqImplicitType :: Eq ImplicitType

instance showImplicitType :: Show ImplicitType where
  show ImplicitRebound = "rebound"
  show ImplicitRetroEta = "retro-eta"
  show ImplicitBongmath = "bongmath"
  show ImplicitPredictorCorrector = "predictor-corrector"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // tensor and conditioning
-- ═════════════════════════════════════════════════════════════════════════════

-- | Latent tensor shape specification
-- |
-- | Standard shapes by model:
-- | - SD 1.5/2.x: [B, 4, H/8, W/8]
-- | - SDXL: [B, 4, H/8, W/8]
-- | - SD3/Flux: [B, 16, H/8, W/8]
-- | - Cascade Stage C: [B, 16, H/42, W/42]
-- | - Cascade Stage B: [B, 4, H/4, W/4]
type LatentShape =
  { batch :: Int                   -- Batch size
  , channels :: Int                -- Latent channels (4 or 16)
  , height :: Int                  -- Latent height
  , width :: Int                   -- Latent width
  }

-- | Latent tensor reference
-- |
-- | Pure data describing a latent tensor location.
-- | Actual tensor data lives in GPU memory; this is just metadata.
type LatentTensor =
  { shape :: LatentShape
  , dtype :: TensorDtype           -- Data type
  , device :: TensorDevice         -- GPU device
  , index :: Int                   -- Buffer index for runtime lookup
  }

-- | Tensor data type
data TensorDtype
  = DtypeFloat16                   -- ^ FP16 (default for inference)
  | DtypeFloat32                   -- ^ FP32 (higher precision)
  | DtypeBFloat16                  -- ^ BF16 (better dynamic range)

derive instance eqTensorDtype :: Eq TensorDtype

instance showTensorDtype :: Show TensorDtype where
  show DtypeFloat16 = "float16"
  show DtypeFloat32 = "float32"
  show DtypeBFloat16 = "bfloat16"

-- | Tensor device
data TensorDevice
  = DeviceCPU                      -- ^ CPU memory
  | DeviceCUDA Int                 -- ^ CUDA GPU by index
  | DeviceWebGPU                   -- ^ WebGPU (browser)

derive instance eqTensorDevice :: Eq TensorDevice

instance showTensorDevice :: Show TensorDevice where
  show DeviceCPU = "cpu"
  show (DeviceCUDA idx) = "cuda:" <> show idx
  show DeviceWebGPU = "webgpu"

-- | Conditioning for diffusion
-- |
-- | Supports multiple conditioning types that can be composed:
-- | - Text: CLIP/T5 text embeddings
-- | - Image: Image embeddings for IP-Adapter, ControlNet
-- | - Composite: Multiple conditions combined
data Conditioning
  = ConditioningText TextConditioning
  | ConditioningImage ImageConditioning
  | ConditioningComposite (Array Conditioning)
  | ConditioningNone                 -- For unconditional/negative

derive instance eqConditioning :: Eq Conditioning

instance showConditioning :: Show Conditioning where
  show (ConditioningText _) = "ConditioningText"
  show (ConditioningImage _) = "ConditioningImage"
  show (ConditioningComposite arr) = "ConditioningComposite[" <> show (Array.length arr) <> "]"
  show ConditioningNone = "ConditioningNone"

-- | Text conditioning (CLIP/T5 embeddings)
type TextConditioning =
  { embeddingIndex :: Int          -- Buffer index for embeddings
  , pooledIndex :: Maybe Int       -- Optional pooled embedding index (SDXL)
  , tokenLength :: Int             -- Token sequence length
  , embeddingDim :: Int            -- Embedding dimension (768, 1024, 4096)
  }

-- | Image conditioning (ControlNet, IP-Adapter, Reference)
type ImageConditioning =
  { embeddingIndex :: Int          -- Buffer index for image embeddings
  , conditionType :: ImageConditionType
  , strength :: Number             -- Conditioning strength (0.0-1.0)
  , startPercent :: Number         -- Start applying at this % of steps
  , endPercent :: Number           -- Stop applying at this % of steps
  }

-- | Image conditioning types
data ImageConditionType
  = ConditionControlNet            -- ^ ControlNet conditioning
  | ConditionIPAdapter             -- ^ IP-Adapter image prompt
  | ConditionReference             -- ^ Reference image attention
  | ConditionT2IAdapter            -- ^ T2I-Adapter conditioning

derive instance eqImageConditionType :: Eq ImageConditionType

instance showImageConditionType :: Show ImageConditionType where
  show ConditionControlNet = "controlnet"
  show ConditionIPAdapter = "ip_adapter"
  show ConditionReference = "reference"
  show ConditionT2IAdapter = "t2i_adapter"

-- | Noise schedule (sigma values for each step)
type NoiseSchedule =
  { sigmas :: Array Number         -- Sigma values (descending, ends with 0)
  , timesteps :: Array Number      -- Corresponding timesteps
  , scheduler :: SchedulerType
  , steps :: Int
  }

-- | Sigma schedule specification
type SigmaSchedule =
  { sigmaMin :: Number             -- Minimum sigma (typically ~0.03)
  , sigmaMax :: Number             -- Maximum sigma (typically ~14.6)
  , rho :: Number                  -- Schedule shape parameter
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // blend mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Blend mode for combining regional latents
data DiffusionBlendMode
  = BlendLinear                    -- ^ Linear interpolation by mask
  | BlendSoftmax                   -- ^ Softmax attention blending
  | BlendMultiply                  -- ^ Multiplicative blending
  | BlendFeathered Number          -- ^ Feathered edge blending

derive instance eqDiffusionBlendMode :: Eq DiffusionBlendMode

instance showDiffusionBlendMode :: Show DiffusionBlendMode where
  show BlendLinear = "linear"
  show BlendSoftmax = "softmax"
  show BlendMultiply = "multiply"
  show (BlendFeathered f) = "feathered(" <> show f <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // step strategy
-- ═════════════════════════════════════════════════════════════════════════════

-- | Step strategy for advanced sampling
-- |
-- | Controls the denoising step behavior:
-- | - Standard: Single step per sigma
-- | - Substep: Multiple substeps per sigma (higher quality)
-- | - Ancestral: Add noise after each step (SDE sampling)
data StepStrategy
  = StrategyStandard               -- ^ Standard single step
  | StrategySubstep SubstepConfig  -- ^ Multi-substep sampling
  | StrategyAncestral              -- ^ Ancestral sampling (add noise each step)
    { eta :: Number                -- Noise scale (0 = deterministic, 1 = full SDE)
    }
  | StrategySDE                    -- ^ Full SDE sampling
    { noiseTypeStep :: NoiseType
    , noiseTypeSubstep :: NoiseType
    , noiseModeStep :: NoiseMode
    , noiseModeSubstep :: NoiseMode
    }

derive instance eqStepStrategy :: Eq StepStrategy

instance showStepStrategy :: Show StepStrategy where
  show StrategyStandard = "standard"
  show (StrategySubstep _) = "substep"
  show (StrategyAncestral _) = "ancestral"
  show (StrategySDE _) = "sde"

-- | Substep configuration for high-quality sampling
type SubstepConfig =
  { substeps :: Int                -- Number of substeps per step
  , method :: SubstepMethod        -- Substep integration method
  }

-- | Substep integration method
data SubstepMethod
  = SubstepEuler                   -- ^ Simple Euler substeps
  | SubstepHeun                    -- ^ Heun's method (2nd order)
  | SubstepRK4                     -- ^ Runge-Kutta 4th order
  | SubstepDPMSolver               -- ^ DPM-Solver substeps

derive instance eqSubstepMethod :: Eq SubstepMethod

instance showSubstepMethod :: Show SubstepMethod where
  show SubstepEuler = "euler"
  show SubstepHeun = "heun"
  show SubstepRK4 = "rk4"
  show SubstepDPMSolver = "dpm_solver"
