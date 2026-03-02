-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // gpu // compute-kernel/glow
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ComputeKernel/Glow — GPU Glow Effect Kernel Types
-- |
-- | Glow operations for visual enhancement:
-- | - Bloom: HDR bright extraction and diffusion
-- | - Outer Glow: Edge-emanating light
-- | - Inner Glow: Inward edge lighting

module Hydrogen.GPU.ComputeKernel.Glow
  ( -- * Glow Types
    GlowKernel(GlowBloom, GlowOuter, GlowInner)
  , GlowTint
  , GlowFalloff(FalloffLinear, FalloffQuadratic, FalloffExponential, FalloffGaussian)
  
  -- * Specific Kernels
  , BloomKernel(BloomKernel)
  , OuterGlowKernel(OuterGlowKernel)
  , InnerGlowKernel(InnerGlowKernel)
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

import Hydrogen.GPU.ComputeKernel.Core
  ( KernelConfig
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // glow kernels
-- ═════════════════════════════════════════════════════════════════════════════

-- | Glow kernel variants
-- |
-- | Each variant maps to a specific WebGPU compute shader.
data GlowKernel
  = GlowBloom BloomKernel
  | GlowOuter OuterGlowKernel
  | GlowInner InnerGlowKernel

derive instance eqGlowKernel :: Eq GlowKernel

instance showGlowKernel :: Show GlowKernel where
  show (GlowBloom k) = "(GlowBloom " <> show k <> ")"
  show (GlowOuter k) = "(GlowOuter " <> show k <> ")"
  show (GlowInner k) = "(GlowInner " <> show k <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bloom
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bloom kernel
-- |
-- | Extracts bright pixels, blurs them, and composites back.
-- | 3-pass pipeline:
-- | 1. Threshold: Extract pixels above threshold
-- | 2. Blur: Gaussian blur the extracted pixels
-- | 3. Composite: Add blurred result back to original
newtype BloomKernel = BloomKernel
  { threshold :: Number        -- Brightness threshold (0.0-1.0)
  , intensity :: Number        -- Bloom intensity
  , radius :: Int              -- Blur radius
  , passes :: Int              -- Blur passes for quality
  , tint :: GlowTint           -- Optional color tint
  , config :: KernelConfig
  }

derive instance eqBloomKernel :: Eq BloomKernel

instance showBloomKernel :: Show BloomKernel where
  show (BloomKernel k) = "(BloomKernel threshold:" <> show k.threshold <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // outer glow
-- ═════════════════════════════════════════════════════════════════════════════

-- | Outer glow kernel
-- |
-- | Creates glow outside element edges.
newtype OuterGlowKernel = OuterGlowKernel
  { color :: GlowTint
  , radius :: Int              -- Glow spread radius
  , intensity :: Number        -- Glow intensity (0.0-1.0)
  , falloff :: GlowFalloff     -- Intensity falloff curve
  , config :: KernelConfig
  }

derive instance eqOuterGlowKernel :: Eq OuterGlowKernel

instance showOuterGlowKernel :: Show OuterGlowKernel where
  show (OuterGlowKernel k) = "(OuterGlowKernel radius:" <> show k.radius <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // inner glow
-- ═════════════════════════════════════════════════════════════════════════════

-- | Inner glow kernel
-- |
-- | Creates glow inside element edges.
newtype InnerGlowKernel = InnerGlowKernel
  { color :: GlowTint
  , radius :: Int
  , intensity :: Number
  , choke :: Number            -- Edge hardness (0.0-1.0)
  , config :: KernelConfig
  }

derive instance eqInnerGlowKernel :: Eq InnerGlowKernel

instance showInnerGlowKernel :: Show InnerGlowKernel where
  show (InnerGlowKernel k) = "(InnerGlowKernel radius:" <> show k.radius <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // glow tint
-- ═════════════════════════════════════════════════════════════════════════════

-- | Glow color tint
-- |
-- | Defines the color applied to glow effects.
type GlowTint =
  { r :: Number                -- Red (0.0-1.0)
  , g :: Number                -- Green (0.0-1.0)
  , b :: Number                -- Blue (0.0-1.0)
  , enabled :: Boolean         -- Whether tint is applied
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // glow falloff
-- ═════════════════════════════════════════════════════════════════════════════

-- | Glow falloff type
-- |
-- | Controls how glow intensity diminishes with distance from edge.
data GlowFalloff
  = FalloffLinear              -- Linear intensity decay
  | FalloffQuadratic           -- Squared distance decay
  | FalloffExponential         -- Exponential decay
  | FalloffGaussian            -- Gaussian distribution (most natural)

derive instance eqGlowFalloff :: Eq GlowFalloff
