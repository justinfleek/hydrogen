-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // gpu // compute-kernel/composite
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ComputeKernel/Composite — GPU Compositing Kernel Types
-- |
-- | Layer compositing operations:
-- | - Blend: Layer blending modes
-- | - Mask: Alpha masking
-- | - Alpha: Alpha channel manipulation

module Hydrogen.GPU.ComputeKernel.Composite
  ( -- * Composite Types
    CompositeKernel(..)
  , BlendKernelMode(..)
  , MaskChannel(..)
  , AlphaOperation(..)
  
  -- * Specific Kernels
  , BlendKernel(..)
  , MaskKernel(..)
  , AlphaKernel(..)
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
  , KernelInput
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // composite kernels
-- ═════════════════════════════════════════════════════════════════════════════

-- | Composite kernel variants
-- |
-- | Each variant maps to a WebGPU compute shader with workgroup 16x16x1.
data CompositeKernel
  = CompositeBlend BlendKernel
  | CompositeMask MaskKernel
  | CompositeAlpha AlphaKernel

derive instance eqCompositeKernel :: Eq CompositeKernel

instance showCompositeKernel :: Show CompositeKernel where
  show (CompositeBlend k) = "(CompositeBlend " <> show k <> ")"
  show (CompositeMask k) = "(CompositeMask " <> show k <> ")"
  show (CompositeAlpha k) = "(CompositeAlpha " <> show k <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // blend
-- ═════════════════════════════════════════════════════════════════════════════

-- | Blend kernel
-- |
-- | Combines two layers using various blending modes.
newtype BlendKernel = BlendKernel
  { layerA :: KernelInput      -- Bottom layer
  , layerB :: KernelInput      -- Top layer
  , mode :: BlendKernelMode
  , opacity :: Number          -- Top layer opacity (0.0-1.0)
  , config :: KernelConfig
  }

derive instance eqBlendKernel :: Eq BlendKernel

instance showBlendKernel :: Show BlendKernel where
  show (BlendKernel k) = "(BlendKernel " <> show k.mode <> ")"

-- | Blend modes for kernel compositing
-- |
-- | Standard photoshop-like blend modes.
data BlendKernelMode
  = KernelBlendNormal          -- Alpha compositing
  | KernelBlendAdd             -- Additive (glow)
  | KernelBlendMultiply        -- Darken
  | KernelBlendScreen          -- Lighten
  | KernelBlendOverlay         -- Contrast
  | KernelBlendSoftLight       -- Subtle contrast
  | KernelBlendHardLight       -- Strong contrast
  | KernelBlendDifference      -- Invert comparison

derive instance eqBlendKernelMode :: Eq BlendKernelMode

instance showBlendKernelMode :: Show BlendKernelMode where
  show KernelBlendNormal = "Normal"
  show KernelBlendAdd = "Add"
  show KernelBlendMultiply = "Multiply"
  show KernelBlendScreen = "Screen"
  show KernelBlendOverlay = "Overlay"
  show KernelBlendSoftLight = "SoftLight"
  show KernelBlendHardLight = "HardLight"
  show KernelBlendDifference = "Difference"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // mask
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mask kernel
-- |
-- | Applies a mask to control visibility.
newtype MaskKernel = MaskKernel
  { source :: KernelInput      -- Source to mask
  , mask :: KernelInput        -- Mask input
  , channel :: MaskChannel     -- Which mask channel to use
  , invert :: Boolean          -- Invert mask
  , config :: KernelConfig
  }

derive instance eqMaskKernel :: Eq MaskKernel

instance showMaskKernel :: Show MaskKernel where
  show (MaskKernel k) = "(MaskKernel " <> show k.channel <> ")"

-- | Mask channel selection
-- |
-- | Determines which channel of the mask texture controls visibility.
data MaskChannel
  = MaskRed
  | MaskGreen
  | MaskBlue
  | MaskAlpha
  | MaskLuminance              -- Grayscale from RGB

derive instance eqMaskChannel :: Eq MaskChannel

instance showMaskChannel :: Show MaskChannel where
  show MaskRed = "Red"
  show MaskGreen = "Green"
  show MaskBlue = "Blue"
  show MaskAlpha = "Alpha"
  show MaskLuminance = "Luminance"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // alpha
-- ═════════════════════════════════════════════════════════════════════════════

-- | Alpha adjustment kernel
-- |
-- | Manipulates the alpha channel.
newtype AlphaKernel = AlphaKernel
  { source :: KernelInput
  , operation :: AlphaOperation
  , threshold :: Number        -- For threshold operations
  , feather :: Number          -- Edge softness
  , config :: KernelConfig
  }

derive instance eqAlphaKernel :: Eq AlphaKernel

instance showAlphaKernel :: Show AlphaKernel where
  show (AlphaKernel k) = "(AlphaKernel " <> show k.operation <> ")"

-- | Alpha operations
-- |
-- | Different ways to transform the alpha channel.
data AlphaOperation
  = AlphaMultiply Number       -- Multiply alpha by factor
  | AlphaThreshold             -- Binary threshold
  | AlphaInvert                -- Invert alpha
  | AlphaRemapRange Number Number  -- Remap alpha range

derive instance eqAlphaOperation :: Eq AlphaOperation

instance showAlphaOperation :: Show AlphaOperation where
  show (AlphaMultiply f) = "(AlphaMultiply " <> show f <> ")"
  show AlphaThreshold = "AlphaThreshold"
  show AlphaInvert = "AlphaInvert"
  show (AlphaRemapRange min' max') = "(AlphaRemapRange " <> show min' <> " " <> show max' <> ")"
