-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // gpu // diffusion // kernels
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Diffusion Kernels — GPU Compute Kernel ADTs
-- |
-- | ## Design Philosophy
-- |
-- | Kernels are pure data representing GPU operations. The runtime interprets
-- | these kernels to execute actual GPU compute. This separation enables:
-- | - Serialization and hashing for distributed caching
-- | - Deterministic replay across systems
-- | - Algebraic composition of pipelines
-- |
-- | ## Kernel Types
-- |
-- | - EncodeKernel: VAE encode (image -> latent)
-- | - DecodeKernel: VAE decode (latent -> image)
-- | - DenoiseKernel: Single denoising step
-- | - NoiseScheduleKernel: Generate sigma schedule
-- | - LatentBlendKernel: Blend latents for inpainting
-- | - CFGKernel: Classifier-free guidance

module Hydrogen.GPU.Diffusion.Kernels
  ( -- * Diffusion Kernel ADT
    DiffusionKernel(..)
  , EncodeKernel(..)
  , DecodeKernel(..)
  , DenoiseKernel(..)
  , NoiseScheduleKernel(..)
  , LatentBlendKernel(..)
  , CFGKernel(..)
  
  -- * Re-exported for DenoiseKernel
  , DiffusionConfig
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  )

import Data.Maybe (Maybe)

import Hydrogen.GPU.Diffusion.Types
  ( SchedulerType
  , NoiseType
  , NoiseMode
  , GuideMode
  , ImplicitType
  , LatentShape
  , TensorDtype
  , TensorDevice
  , DiffusionBlendMode
  , StepStrategy
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // diffusion config type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete diffusion configuration
-- |
-- | Defined here to be part of DenoiseKernel. Re-exported by this module.
type DiffusionConfig =
  { scheduler :: SchedulerType
  , steps :: Int
  , sigmaMin :: Number
  , sigmaMax :: Number
  , noiseType :: NoiseType
  , noiseMode :: NoiseMode
  , seed :: Int
  , cfgScale :: Number
  , guideMode :: GuideMode
  , implicitType :: Maybe ImplicitType
  , stepStrategy :: StepStrategy
  , latentShape :: LatentShape
  , dtype :: TensorDtype
  , device :: TensorDevice
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // diffusion kernel ADT
-- ═════════════════════════════════════════════════════════════════════════════

-- | DiffusionKernel — GPU operations for diffusion model inference
-- |
-- | Core operations in the diffusion pipeline:
-- | - Encode: Image -> Latent (VAE encoder)
-- | - Decode: Latent -> Image (VAE decoder)
-- | - Denoise: Latent + Noise -> Denoised Latent (U-Net/DiT)
-- | - NoiseSchedule: Generate sigma schedule
-- | - LatentBlend: Blend latents for inpainting/outpainting
-- | - CFG: Classifier-free guidance combination
data DiffusionKernel
  = KernelEncode EncodeKernel
  | KernelDecode DecodeKernel
  | KernelDenoise DenoiseKernel
  | KernelNoiseSchedule NoiseScheduleKernel
  | KernelLatentBlend LatentBlendKernel
  | KernelCFG CFGKernel
  | KernelSequence (Array DiffusionKernel)   -- Execute in order
  | KernelNoop                               -- Identity operation

derive instance eqDiffusionKernel :: Eq DiffusionKernel

instance showDiffusionKernel :: Show DiffusionKernel where
  show (KernelEncode _) = "KernelEncode"
  show (KernelDecode _) = "KernelDecode"
  show (KernelDenoise _) = "KernelDenoise"
  show (KernelNoiseSchedule _) = "KernelNoiseSchedule"
  show (KernelLatentBlend _) = "KernelLatentBlend"
  show (KernelCFG _) = "KernelCFG"
  show (KernelSequence _) = "KernelSequence [...]"
  show KernelNoop = "KernelNoop"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // encode kernels
-- ═════════════════════════════════════════════════════════════════════════════

-- | VAE Encode kernel — Image to Latent
newtype EncodeKernel = EncodeKernel
  { inputWidth :: Int            -- Input image width
  , inputHeight :: Int           -- Input image height
  , inputChannels :: Int         -- Input channels (3 for RGB, 4 for RGBA)
  , latentChannels :: Int        -- Output latent channels (4 for SD, 16 for SD3)
  , scaleFactor :: Number        -- Downscale factor (typically 8)
  , tiled :: Boolean             -- Use tiled encoding for large images
  , tileSize :: Int              -- Tile size if tiled
  }

derive instance eqEncodeKernel :: Eq EncodeKernel

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // decode kernels
-- ═════════════════════════════════════════════════════════════════════════════

-- | VAE Decode kernel — Latent to Image
newtype DecodeKernel = DecodeKernel
  { latentWidth :: Int           -- Latent width
  , latentHeight :: Int          -- Latent height
  , latentChannels :: Int        -- Latent channels
  , outputChannels :: Int        -- Output channels (3 for RGB)
  , scaleFactor :: Number        -- Upscale factor (typically 8)
  , tiled :: Boolean             -- Use tiled decoding
  , tileSize :: Int              -- Tile size if tiled
  }

derive instance eqDecodeKernel :: Eq DecodeKernel

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // denoise kernels
-- ═════════════════════════════════════════════════════════════════════════════

-- | Denoise kernel — Single denoising step
-- |
-- | This is the core diffusion operation that predicts noise and removes it.
newtype DenoiseKernel = DenoiseKernel
  { scheduler :: SchedulerType     -- Scheduler for sigma computation
  , noiseType :: NoiseType         -- Noise generator type
  , noiseMode :: NoiseMode         -- Noise scaling mode
  , guideMode :: GuideMode         -- Guidance interpretation
  , implicitType :: Maybe ImplicitType  -- Optional implicit solver
  , steps :: Int                   -- Total denoising steps
  , currentStep :: Int             -- Current step (0-indexed)
  , cfgScale :: Number             -- Classifier-free guidance scale
  , sigma :: Number                -- Current sigma value
  , sigmaNext :: Number            -- Next sigma value
  , seed :: Int                    -- Random seed for noise
  , config :: DiffusionConfig      -- Full configuration
  }

derive instance eqDenoiseKernel :: Eq DenoiseKernel

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // noise schedule kernels
-- ═════════════════════════════════════════════════════════════════════════════

-- | Noise schedule generation kernel
newtype NoiseScheduleKernel = NoiseScheduleKernel
  { scheduler :: SchedulerType
  , steps :: Int
  , sigmaMin :: Number             -- Minimum sigma (end of schedule)
  , sigmaMax :: Number             -- Maximum sigma (start of schedule)
  , denoise :: Number              -- Denoise strength (0.0-1.0, 1.0 = full)
  }

derive instance eqNoiseScheduleKernel :: Eq NoiseScheduleKernel

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // latent blend kernels
-- ═════════════════════════════════════════════════════════════════════════════

-- | Latent blend kernel — for inpainting, outpainting, regional prompts
newtype LatentBlendKernel = LatentBlendKernel
  { blendMode :: DiffusionBlendMode
  , maskChannel :: Int             -- Which channel is the mask
  , feather :: Number              -- Mask feathering amount
  , preserveOriginal :: Boolean    -- Preserve original latent in masked area
  }

derive instance eqLatentBlendKernel :: Eq LatentBlendKernel

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // cfg kernels
-- ═════════════════════════════════════════════════════════════════════════════

-- | Classifier-free guidance kernel
-- |
-- | Combines conditional and unconditional predictions:
-- | output = uncond + cfg_scale * (cond - uncond)
newtype CFGKernel = CFGKernel
  { scale :: Number                -- CFG scale (typically 7.0-15.0)
  , rescale :: Number              -- CFG rescale factor (0.0-1.0)
  , dynamicThreshold :: Boolean    -- Use dynamic thresholding
  , threshold :: Number            -- Threshold for dynamic CFG
  }

derive instance eqCFGKernel :: Eq CFGKernel
