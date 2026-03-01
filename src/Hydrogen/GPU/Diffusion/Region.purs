-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // gpu // diffusion // region
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Region Diffusion — Regional prompts and inpainting state
-- |
-- | ## Contents
-- |
-- | - Region diffusion state for regional prompts
-- | - Diffusion region with per-region conditioning
-- |
-- | ## Regional Prompting
-- |
-- | Enables compositing multiple prompts into different image regions:
-- | - Each region has its own mask, conditioning, and blend parameters
-- | - Regions are blended at each denoising step
-- | - Supports inpainting, outpainting, and compositional generation

module Hydrogen.GPU.Diffusion.Region
  ( -- * Region Diffusion
    RegionDiffusionState
  , DiffusionRegion
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.GPU.Diffusion.Types
  ( LatentTensor
  , Conditioning
  , DiffusionBlendMode
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // region diffusion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Region diffusion state for regional prompts and inpainting
type RegionDiffusionState =
  { regions :: Array DiffusionRegion
  , globalLatent :: LatentTensor
  , blendMode :: DiffusionBlendMode
  , currentStep :: Int
  }

-- | A diffusion region with its own conditioning
type DiffusionRegion =
  { mask :: LatentTensor           -- Region mask (same spatial dims as latent)
  , conditioning :: Conditioning   -- Region-specific conditioning
  , strength :: Number             -- Region influence strength
  , blendStart :: Number           -- Start blending at this % of steps
  , blendEnd :: Number             -- End blending at this % of steps
  }
