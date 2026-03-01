-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // gpu // compute-kernel/types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ComputeKernel/Types — Main ComputeKernel Sum Type
-- |
-- | Defines the top-level ComputeKernel type that unifies all kernel variants.
-- | This type is the primary interface for GPU compute operations.

module Hydrogen.GPU.ComputeKernel.Types
  ( ComputeKernel(..)
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

import Data.Maybe (Maybe)

import Hydrogen.GPU.ComputeKernel.Core
  ( KernelCondition
  )

import Hydrogen.GPU.ComputeKernel.Blur
  ( BlurKernel
  )

import Hydrogen.GPU.ComputeKernel.Glow
  ( GlowKernel
  )

import Hydrogen.GPU.ComputeKernel.Noise
  ( NoiseKernel
  )

import Hydrogen.GPU.ComputeKernel.Particle
  ( ParticleKernel
  )

import Hydrogen.GPU.ComputeKernel.Color
  ( ColorKernel
  )

import Hydrogen.GPU.ComputeKernel.Distortion
  ( DistortionKernel
  )

import Hydrogen.GPU.ComputeKernel.Composite
  ( CompositeKernel
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // compute kernel
-- ═════════════════════════════════════════════════════════════════════════════

-- | A compute kernel — GPU operation description
-- |
-- | ComputeKernel is the top-level type for all GPU compute operations.
-- | It supports:
-- | - Domain-specific kernels (blur, glow, noise, particle, color, distortion, composite)
-- | - Composition (sequence, parallel)
-- | - Conditional execution
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Kernels are deterministic data:
-- | - Same kernel + same input = same output (always)
-- | - Kernels can be serialized, hashed, cached
-- | - Multiple agents can share kernel definitions
-- | - GPU batches kernels across agents efficiently
data ComputeKernel
  = KernelBlur BlurKernel
  | KernelGlow GlowKernel
  | KernelNoise NoiseKernel
  | KernelParticle ParticleKernel
  | KernelColor ColorKernel
  | KernelDistortion DistortionKernel
  | KernelComposite CompositeKernel
  | KernelSequence (Array ComputeKernel)     -- Execute in order
  | KernelParallel (Array ComputeKernel)     -- Execute simultaneously (different outputs)
  | KernelConditional                        -- Conditional execution
      { condition :: KernelCondition
      , thenKernel :: ComputeKernel
      , elseKernel :: Maybe ComputeKernel
      }
  | KernelNoop                               -- Identity (no operation)

derive instance eqComputeKernel :: Eq ComputeKernel

instance showComputeKernel :: Show ComputeKernel where
  show (KernelBlur k) = "(KernelBlur " <> show k <> ")"
  show (KernelGlow k) = "(KernelGlow " <> show k <> ")"
  show (KernelNoise k) = "(KernelNoise " <> show k <> ")"
  show (KernelParticle k) = "(KernelParticle " <> show k <> ")"
  show (KernelColor k) = "(KernelColor " <> show k <> ")"
  show (KernelDistortion k) = "(KernelDistortion " <> show k <> ")"
  show (KernelComposite k) = "(KernelComposite " <> show k <> ")"
  show (KernelSequence _) = "(KernelSequence [...])"
  show (KernelParallel _) = "(KernelParallel [...])"
  show (KernelConditional _) = "(KernelConditional ...)"
  show KernelNoop = "KernelNoop"
