-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // gpu // compute-kernel/blur
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ComputeKernel/Blur — GPU Blur Kernel Types
-- |
-- | Blur operations for real-time image processing:
-- | - Gaussian: High-quality separable convolution
-- | - Directional: Motion blur effects
-- | - Radial: Spin and zoom blur
-- | - Box: Fast approximation for performance

module Hydrogen.GPU.ComputeKernel.Blur
  ( -- * Blur Types
    BlurKernel(..)
  , BlurQuality(..)
  , RadialBlurType(..)
  
  -- * Specific Kernels
  , GaussianBlurKernel(..)
  , DirectionalBlurKernel(..)
  , RadialBlurKernel(..)
  , BoxBlurKernel(..)
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
--                                                               // blur kernels
-- ═════════════════════════════════════════════════════════════════════════════

-- | Blur kernel variants
-- |
-- | Each variant maps to a specific WebGPU compute shader with workgroup 16x16x1.
data BlurKernel
  = BlurGaussian GaussianBlurKernel
  | BlurDirectional DirectionalBlurKernel
  | BlurRadial RadialBlurKernel
  | BlurBox BoxBlurKernel

derive instance eqBlurKernel :: Eq BlurKernel

instance showBlurKernel :: Show BlurKernel where
  show (BlurGaussian k) = "(BlurGaussian " <> show k <> ")"
  show (BlurDirectional k) = "(BlurDirectional " <> show k <> ")"
  show (BlurRadial k) = "(BlurRadial " <> show k <> ")"
  show (BlurBox k) = "(BlurBox " <> show k <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // gaussian
-- ═════════════════════════════════════════════════════════════════════════════

-- | Gaussian blur kernel
-- |
-- | Implements separable 2-pass Gaussian blur:
-- | - Pass 1: Horizontal convolution
-- | - Pass 2: Vertical convolution
-- |
-- | Multiple passes create softer, more diffuse blur.
newtype GaussianBlurKernel = GaussianBlurKernel
  { radius :: Int              -- Kernel radius in pixels
  , sigma :: Number            -- Standard deviation
  , passes :: Int              -- Number of blur passes (more = softer)
  , config :: KernelConfig
  }

derive instance eqGaussianBlurKernel :: Eq GaussianBlurKernel

instance showGaussianBlurKernel :: Show GaussianBlurKernel where
  show (GaussianBlurKernel k) = "(GaussianBlurKernel radius:" <> show k.radius <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // directional
-- ═════════════════════════════════════════════════════════════════════════════

-- | Directional blur kernel (motion blur)
-- |
-- | Samples along a direction to create motion blur effect.
newtype DirectionalBlurKernel = DirectionalBlurKernel
  { angle :: Number            -- Direction in degrees
  , distance :: Int            -- Blur distance in pixels
  , samples :: Int             -- Number of samples along direction
  , config :: KernelConfig
  }

derive instance eqDirectionalBlurKernel :: Eq DirectionalBlurKernel

instance showDirectionalBlurKernel :: Show DirectionalBlurKernel where
  show (DirectionalBlurKernel k) = "(DirectionalBlurKernel angle:" <> show k.angle <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // radial
-- ═════════════════════════════════════════════════════════════════════════════

-- | Radial blur kernel (spin/zoom)
-- |
-- | Creates circular blur effects emanating from a center point.
newtype RadialBlurKernel = RadialBlurKernel
  { centerX :: Number          -- Center X (0.0-1.0 normalized)
  , centerY :: Number          -- Center Y (0.0-1.0 normalized)
  , amount :: Number           -- Blur strength
  , blurType :: RadialBlurType -- Spin or zoom
  , samples :: Int             -- Number of samples
  , config :: KernelConfig
  }

derive instance eqRadialBlurKernel :: Eq RadialBlurKernel

instance showRadialBlurKernel :: Show RadialBlurKernel where
  show (RadialBlurKernel k) = "(RadialBlurKernel amount:" <> show k.amount <> ")"

-- | Radial blur type
data RadialBlurType
  = RadialTypeSpin             -- Rotational blur around center
  | RadialTypeZoom             -- Zoom blur toward/from center

derive instance eqRadialBlurType :: Eq RadialBlurType

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // box
-- ═════════════════════════════════════════════════════════════════════════════

-- | Box blur kernel (fast, lower quality)
-- |
-- | Uses simple averaging within a box region.
-- | Multiple iterations approximate Gaussian blur with better performance.
newtype BoxBlurKernel = BoxBlurKernel
  { radius :: Int              -- Box radius
  , iterations :: Int          -- Multiple passes for approximated Gaussian
  , config :: KernelConfig
  }

derive instance eqBoxBlurKernel :: Eq BoxBlurKernel

instance showBoxBlurKernel :: Show BoxBlurKernel where
  show (BoxBlurKernel k) = "(BoxBlurKernel radius:" <> show k.radius <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // quality
-- ═════════════════════════════════════════════════════════════════════════════

-- | Blur quality levels
-- |
-- | Controls compute precision vs performance tradeoff.
-- | At billion-agent scale, quality selection determines GPU budget allocation:
-- | - Low: Fast, acceptable for backgrounds, UI blur
-- | - Medium: Balanced for general use
-- | - High: Best quality for hero elements, slower
data BlurQuality
  = BlurQualityLow            -- Fast: fewer samples, single pass
  | BlurQualityMedium         -- Balanced: moderate samples, dual pass
  | BlurQualityHigh           -- Quality: many samples, multi-pass

derive instance eqBlurQuality :: Eq BlurQuality

instance showBlurQuality :: Show BlurQuality where
  show BlurQualityLow = "BlurQualityLow"
  show BlurQualityMedium = "BlurQualityMedium"
  show BlurQualityHigh = "BlurQualityHigh"
