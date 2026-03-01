-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // gpu // diffusion // constructor
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Diffusion Constructor — Smart constructors for diffusion kernels
-- |
-- | ## Design Philosophy
-- |
-- | Smart constructors provide type-safe kernel creation with sensible defaults.
-- | Each constructor validates its inputs and produces a well-formed kernel.
-- |
-- | ## Kernel Types
-- |
-- | - encodeKernel: Create VAE encode kernel
-- | - decodeKernel: Create VAE decode kernel
-- | - denoiseKernel: Create single denoising step kernel
-- | - noiseScheduleKernel: Create sigma schedule kernel
-- | - latentBlendKernel: Create inpainting blend kernel
-- | - cfgKernel: Create CFG combination kernel

module Hydrogen.GPU.Diffusion.Constructor
  ( -- * Kernel Construction
    encodeKernel
  , decodeKernel
  , denoiseKernel
  , noiseScheduleKernel
  , latentBlendKernel
  , cfgKernel
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude (($))

import Hydrogen.GPU.Diffusion.Types
  ( SchedulerType
  , DiffusionBlendMode
  )

import Hydrogen.GPU.Diffusion.Kernels
  ( DiffusionKernel
      ( KernelEncode
      , KernelDecode
      , KernelDenoise
      , KernelNoiseSchedule
      , KernelLatentBlend
      , KernelCFG
      )
  , EncodeKernel(EncodeKernel)
  , DecodeKernel(DecodeKernel)
  , DenoiseKernel(DenoiseKernel)
  , NoiseScheduleKernel(NoiseScheduleKernel)
  , LatentBlendKernel(LatentBlendKernel)
  , CFGKernel(CFGKernel)
  , DiffusionConfig
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // kernel construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create an encode kernel for VAE encoding
encodeKernel :: Int -> Int -> Int -> Int -> DiffusionKernel
encodeKernel width height channels latentChannels = KernelEncode $ EncodeKernel
  { inputWidth: width
  , inputHeight: height
  , inputChannels: channels
  , latentChannels: latentChannels
  , scaleFactor: 8.0
  , tiled: false
  , tileSize: 512
  }

-- | Create a decode kernel for VAE decoding
decodeKernel :: Int -> Int -> Int -> DiffusionKernel
decodeKernel latentWidth latentHeight latentChannels = KernelDecode $ DecodeKernel
  { latentWidth: latentWidth
  , latentHeight: latentHeight
  , latentChannels: latentChannels
  , outputChannels: 3
  , scaleFactor: 8.0
  , tiled: false
  , tileSize: 64
  }

-- | Create a denoise kernel for a single denoising step
denoiseKernel :: DiffusionConfig -> Int -> Number -> Number -> DiffusionKernel
denoiseKernel config step sigma sigmaNext = KernelDenoise $ DenoiseKernel
  { scheduler: config.scheduler
  , noiseType: config.noiseType
  , noiseMode: config.noiseMode
  , guideMode: config.guideMode
  , implicitType: config.implicitType
  , steps: config.steps
  , currentStep: step
  , cfgScale: config.cfgScale
  , sigma: sigma
  , sigmaNext: sigmaNext
  , seed: config.seed
  , config: config
  }

-- | Create a noise schedule generation kernel
noiseScheduleKernel :: SchedulerType -> Int -> Number -> Number -> Number -> DiffusionKernel
noiseScheduleKernel scheduler steps sigmaMin sigmaMax denoise = 
  KernelNoiseSchedule $ NoiseScheduleKernel
    { scheduler: scheduler
    , steps: steps
    , sigmaMin: sigmaMin
    , sigmaMax: sigmaMax
    , denoise: denoise
    }

-- | Create a latent blend kernel for inpainting
latentBlendKernel :: DiffusionBlendMode -> Number -> DiffusionKernel
latentBlendKernel mode feather = KernelLatentBlend $ LatentBlendKernel
  { blendMode: mode
  , maskChannel: 0
  , feather: feather
  , preserveOriginal: true
  }

-- | Create a CFG kernel
cfgKernel :: Number -> Number -> DiffusionKernel
cfgKernel scale rescale = KernelCFG $ CFGKernel
  { scale: scale
  , rescale: rescale
  , dynamicThreshold: false
  , threshold: 0.995
  }
